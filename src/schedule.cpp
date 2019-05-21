#include "schedule.h"

#include <algorithm>
#include <list>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <glog/logging.h>

using std::equal_to;
using std::get;
using std::holds_alternative;
using std::list;
using std::make_shared;
using std::ostringstream;
using std::pair;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::visit;

using nlohmann::json;

uint64_t Schedule::constructed = 0;
uint64_t Schedule::deconstructed = 0;

size_t Schedule::Cost() const {
  auto children = Children();
  return unordered_set<Schedule>{children.begin(), children.end()}.size();
}

template <typename Iterator>
Schedule LinearSchedule(Iterator first, Iterator last) {
  --last;
  RAttr distance = last->rattr - first->rattr;
  if (std::distance(first, last) == 1) {
    return Schedule{first->aattr, last->aattr, distance};
  }
  return Schedule{Schedule::Ptr(new Schedule{LinearSchedule(first, last)}),
                  last->aattr, distance};
}

Schedule BestGreedySchedule(const vector<RAttr>& rattrs,
                            const vector<AAttr>& aattrs) {
  return BestGreedySchedule(rattrs,
                            vector<AAttrUnion>{aattrs.begin(), aattrs.end()});
}

Schedule BestGreedySchedule(const vector<RAttr>& rattrs,
                            const vector<AAttrUnion>& aattrs) {
  VLOG(2) << "prepare data structures";
  vector<AttrUnion> attrs;
  attrs.reserve(rattrs.size());
  unordered_map<AttrUnion, size_t> attr_map;
  unordered_map<size_t, AttrUnion> new_attrs_map;
  for (size_t i = 0; i < rattrs.size(); ++i) {
    attrs.push_back(AttrUnion{rattrs[i], aattrs[i]});
    attr_map[attrs[i]] = i;
    new_attrs_map[i] = {attrs[i].rattr, attrs[i].aattr};
    VLOG(3) << "recv attr " << *attrs.rbegin();
  }
  unordered_map<Schedule, list<pair<size_t, size_t>>> reuses;

  VLOG(2) << "look for reuse";
  for (size_t i = 0; i < attrs.size(); ++i) {
    const auto& left_rattr = attrs[i].rattr;
    const auto& left_aattr = attrs[i].aattr;
    for (size_t j = i + 1; j < attrs.size(); ++j) {
      const auto& right_rattr = attrs[j].rattr;
      const auto& right_aattr = attrs[j].aattr;
      VLOG(3) << "checking reuse of " << attrs[i] << " + " << attrs[j];
      Schedule operation{left_aattr, right_aattr,
                         static_cast<RAttr>(right_rattr - left_rattr)};
      if (reuses.count(operation)) {
        VLOG(4) << "  already seen";
        continue;
      }

      // look for reuse of this operation over all operands
      unordered_set<size_t> used;
      for (size_t idx_l = 0; idx_l < attrs.size(); ++idx_l) {
        VLOG(4) << "  examining " << attrs[idx_l];
        const auto& attr_l = attrs[idx_l];
        const auto& rattr_l = attr_l.rattr;
        const auto& aattr_l = attr_l.aattr;
        if (!equal_to<AAttrUnion>{}(aattr_l, left_aattr) || used.count(idx_l)) {
          continue;
        }
        AttrUnion attr_r = {
            static_cast<RAttr>(rattr_l + right_rattr - left_rattr),
            right_aattr};
        auto idx_r_iter = attr_map.find(attr_r);
        if (idx_r_iter == attr_map.end() || used.count(idx_r_iter->second)) {
          continue;
        }
        size_t idx_r = idx_r_iter->second;
        reuses[operation].push_back({idx_l, idx_r});
        used.insert({idx_l, idx_r});
        VLOG(4) << "  found (re)use of " << attrs[idx_l] << " + "
                << attrs[idx_r];
      }
    }
  }

  // filter out operations that cannot be reused
  // what's left may not all be useful because they overlap
  VLOG(2) << "confirm reuse";
  auto reuses_iter = reuses.begin();
  while (reuses_iter != reuses.end()) {
    if (reuses_iter->second.size() <= 1) {
      reuses_iter = reuses.erase(reuses_iter);
    } else {
      ++reuses_iter;
    }
  }

  if (reuses.size() == 0) {
    return LinearSchedule(attrs.begin(), attrs.end());
  }

  unordered_set<size_t> used;
  // only activate reused operationswith the maximum reuse
  // this avoids some of the sub-optimalities
  size_t max_reuse = 0;
  for (const auto iter : reuses) {
    max_reuse = std::max(max_reuse, iter.second.size());
  }
  VLOG(1) << "max reuse: " << max_reuse;

  vector<pair<Schedule, list<pair<size_t, size_t>>>> sorted_reuses{
      reuses.begin(), reuses.end()};
  std::sort(sorted_reuses.begin(), sorted_reuses.end(),
            [](const decltype(sorted_reuses)::value_type& lhs,
               const decltype(sorted_reuses)::value_type& rhs) -> bool {
              if (lhs.second.size() == rhs.second.size()) {
                return lhs.first.distance < rhs.first.distance;
              }
              return lhs.second.size() > rhs.second.size();
            });

  for (auto& reuse : sorted_reuses) {
    const auto& operation{reuse.first};
    auto& reused_indices{reuse.second};
    auto iter = reused_indices.begin();
    while (iter != reused_indices.end()) {
      if (used.count(iter->first) == 0 && used.count(iter->second) == 0) {
        ++iter;
      } else {
        iter = reused_indices.erase(iter);
      }
    }
    if (reused_indices.size() < max_reuse) {
      continue;
    }
    for (const auto& idx_pair : reused_indices) {
      auto idx_l = idx_pair.first;
      auto idx_r = idx_pair.second;
      VLOG(2) << "reusing " << operation << " for " << attrs[idx_l] << " + "
              << attrs[idx_r];
      new_attrs_map[idx_l] = {new_attrs_map[idx_l].rattr,
                              Schedule::Ptr{new Schedule{operation}}};
      new_attrs_map.erase(idx_r);
      used.insert({idx_l, idx_r});
    }
  }

  vector<AttrUnion> sorted_new_attrs;
  sorted_new_attrs.reserve(new_attrs_map.size());
  for (const auto& item : new_attrs_map) {
    sorted_new_attrs.push_back(item.second);
  }
  std::sort(sorted_new_attrs.begin(), sorted_new_attrs.end(),
            [](const AttrUnion& lhs, const AttrUnion& rhs) {
              return lhs.rattr < rhs.rattr;
            });

  if (VLOG_IS_ON(2)) {
    ostringstream oss;
    bool first = true;
    for (const auto& item : sorted_new_attrs) {
      if (first) {
        first = false;
      } else {
        oss << ", ";
      }
      if (holds_alternative<AAttr>(item.aattr)) {
        oss << Attr{item.rattr, get<AAttr>(item.aattr)};
      } else {
        oss << *get<Schedule::Ptr>(item.aattr) << "@" << item.rattr;
      }
    }
    VLOG(2) << "new attrs: " << oss.str() << " (" << sorted_new_attrs.size()
            << ")";
  }

  vector<RAttr> new_rattrs;
  vector<AAttrUnion> new_aattrs;
  new_rattrs.reserve(new_attrs_map.size());
  new_aattrs.reserve(new_attrs_map.size());
  for (const auto& attr : sorted_new_attrs) {
    new_rattrs.push_back(attr.rattr);
    new_aattrs.push_back(attr.aattr);
  }
  return BestGreedySchedule(new_rattrs, new_aattrs);
};

// json serializers
void to_json(json& j, const Attr& v) {
  j["rattr"] = v.rattr;
  j["aattr"] = v.aattr;
}
void to_json(json& j, const Schedule& v) {
  j["left"] = v.left;
  j["right"] = v.right;
  j["distance"] = v.distance;
}
void to_json(json& j, const AAttrUnion& v) {
  if (holds_alternative<AAttr>(v)) {
    j = get<AAttr>(v);
  } else {
    j = *get<Schedule::Ptr>(v);
  }
}
void to_json(json& j, const AttrUnion& v) {
  j["rattr"] = v.rattr;
  j["aattr"] = v.aattr;
}