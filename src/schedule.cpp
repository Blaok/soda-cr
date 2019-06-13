#include "schedule.h"

#include <algorithm>
#include <atomic>
#include <list>
#include <memory>
#include <queue>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <glog/logging.h>
#include <glpk.h>

using std::atomic_uint64_t;
using std::equal_to;
using std::get;
using std::holds_alternative;
using std::list;
using std::make_shared;
using std::ostringstream;
using std::pair;
using std::queue;
using std::unordered_map;
using std::unordered_set;
using std::vector;
using std::visit;

using nlohmann::json;

atomic_uint64_t Schedule::constructed = 0;
atomic_uint64_t Schedule::deconstructed = 0;

size_t Schedule::NumOps() const {
  auto children = Children();
  return unordered_set<Schedule>{children.begin(), children.end()}.size();
}

Generator<pair<size_t, size_t>> GetAttrs(
    const Schedule::Ptr& schedule,
    const unordered_map<Schedule::Ptr, size_t>& reuses,
    const size_t* offset_ptr = nullptr) {
  auto reused_vid_iter = reuses.find(schedule);
  if (reused_vid_iter != reuses.end() && offset_ptr != nullptr) {
    co_yield{*offset_ptr, reused_vid_iter->second};
  } else {
    size_t offset = offset_ptr == nullptr ? 0 : *offset_ptr;
    if (auto ptr = std::get_if<AAttr>(&schedule->left)) {
      co_yield{offset, 0};
    } else {
      for (const auto& attr :
           GetAttrs(std::get<Schedule::Ptr>(schedule->left), reuses, &offset)) {
        co_yield attr;
      }
    }
    offset += schedule->distance;
    if (auto ptr = std::get_if<AAttr>(&schedule->right)) {
      co_yield{offset, 0};
    } else {
      for (const auto& attr : GetAttrs(std::get<Schedule::Ptr>(schedule->right),
                                       reuses, &offset)) {
        co_yield attr;
      }
    }
  }
}

bool Inline(
    const unordered_map<size_t, unordered_set<size_t>>& dependers,
    const unordered_map<size_t, unordered_map<size_t, pair<size_t, size_t>>>&
        dependees,
    size_t* src_vid_ptr, size_t* dst_vid_ptr) {
  for (const auto& [src_vid, dst_vids] : dependers) {
    if (dst_vids.size() == 1) {
      auto dst_vid = *dst_vids.begin();
      auto min_offset = dependees.at(dst_vid).at(src_vid).first;
      auto max_offset = dependees.at(dst_vid).at(src_vid).second;
      if (min_offset == max_offset) {
        VLOG(2) << "var_" << src_vid << " is only accessed by var_" << dst_vid
                << " @ " << min_offset << ", it should be inlined";
        *src_vid_ptr = src_vid;
        *dst_vid_ptr = dst_vid;
        return true;
      }
    }
  }
  return false;
}

size_t Schedule::TotalDistance() const {
  if (this->total_distance == 0) {
    unordered_map<Schedule::Ptr, size_t> tcse_vars;
    unordered_map<size_t, Schedule::Ptr> tcse_var_table;
    auto self = Schedule::Ptr(new Schedule{*this});
    tcse_vars[self] = 1;
    tcse_var_table[1] = self;
    // var_0 is input, var_1 is output

    unordered_map<Schedule::Ptr, size_t> counter;
    for (auto child_obj : Children()) {
      auto child = Schedule::Ptr(new Schedule{child_obj});
      if (counter.count(child) == 0) {
        counter[child] = 0;
      }
      ++counter[child];
    }
    for (const auto& item : counter) {
      if (item.second > 1) {
        tcse_vars[item.first] = tcse_vars.size() + 1;
        tcse_var_table[tcse_vars.size()] = item.first;
      }
    }
    for (const auto& item : tcse_vars) {
      VLOG(2) << "var_" << item.second << ": " << *item.first;
    }

    queue<Schedule::Ptr> vars_to_process{{self}};
    unordered_set<size_t> vars_to_process_set{1};
    unordered_set<size_t> vars_processed{0};
    unordered_map<size_t, unordered_set<size_t>> dependers;
    unordered_map<size_t, unordered_map<size_t, pair<size_t, size_t>>>
        dependees;
    while (!vars_to_process.empty()) {
      auto schedule = vars_to_process.front();
      vars_to_process.pop();
      auto dst_vid = tcse_vars[schedule];
      vars_to_process_set.erase(dst_vid);
      vars_processed.insert(dst_vid);
      for (const auto& attr : GetAttrs(schedule, tcse_vars)) {
        auto offset = attr.first;
        auto src_vid = attr.second;
        VLOG(2) << "var_" << dst_vid << " accesses var_" << src_vid << " @ "
                << offset;
        dependers[src_vid].insert(dst_vid);
        dependees[dst_vid].insert({src_vid, {offset, offset}});
        auto min_offset = dependees[dst_vid][src_vid].first;
        auto max_offset = dependees[dst_vid][src_vid].second;
        dependees[dst_vid][src_vid] = {std::min(offset, min_offset),
                                       std::max(offset, max_offset)};
        if (vars_processed.count(src_vid) == 0 &&
            vars_to_process_set.count(src_vid) == 0) {
          vars_to_process.push(tcse_var_table[src_vid]);
          vars_to_process_set.insert(src_vid);
        }
      }
    }
    for (size_t src_vid, dst_vid;
         Inline(dependers, dependees, &src_vid, &dst_vid);) {
      VLOG(2) << "trying to inline var_" << src_vid;
      auto offset = dependees[dst_vid][src_vid].first;
      for (const auto& item2 : dependees[src_vid]) {
        auto src_src_vid = item2.first;
        auto min_offset = item2.second.first;
        auto max_offset = item2.second.second;
        auto new_min_offset = min_offset + offset;
        auto new_max_offset = max_offset + offset;
        VLOG(2) << "var_" << dst_vid << " accesses var_" << src_vid << " @ "
                << offset;
        VLOG(2) << "var_" << src_vid << " accesses var_" << src_src_vid
                << " @ [" << min_offset << ", " << max_offset << "]";
        VLOG(2) << "therefore var_" << dst_vid << " accesses var_"
                << src_src_vid << " @ [" << new_min_offset << ", "
                << new_max_offset << "] via var_" << src_vid;
        auto old_min_offset = new_min_offset;
        auto old_max_offset = new_max_offset;
        if (dependees[dst_vid].count(src_src_vid)) {
          old_min_offset = dependees[dst_vid][src_src_vid].first;
          old_max_offset = dependees[dst_vid][src_src_vid].second;
          VLOG(2) << "var_" << dst_vid << " used to access var_" << src_src_vid
                  << " @ [" << old_min_offset << ", " << old_max_offset << "]";
        }
        dependees[dst_vid][src_src_vid] = {
            std::min(old_min_offset, new_min_offset),
            std::max(old_max_offset, new_max_offset)};
        VLOG(2) << "after inlining, var_" << dst_vid << " accesses var_"
                << src_src_vid << " @ ["
                << dependees[dst_vid][src_src_vid].first << ", "
                << dependees[dst_vid][src_src_vid].second << "]";
      }
      for (auto [src_src_vid, _] : dependees[src_vid]) {
        dependers[src_src_vid].insert(dst_vid);
        dependers[src_src_vid].erase(src_vid);
      }
      dependers.erase(src_vid);
      dependees[dst_vid].erase(src_vid);
      dependees.erase(src_vid);
    }

    // solve ILP for optimal offsets
    glp_prob* lp = glp_create_prob();
    vector<int> ia{0};
    vector<int> ja{0};
    vector<double> ar{0.};
    glp_set_obj_dir(lp, GLP_MIN);
    // dependers.size() doesn't include the output
    unordered_map<size_t, size_t> produce_offset_index_table{{1, 1}};
    unordered_map<size_t, size_t> consume_offset_index_table{{1, 1}};
    for (auto item : dependers) {
      auto src_vid = item.first;
      produce_offset_index_table[src_vid] =
          produce_offset_index_table.size() + 1;
      consume_offset_index_table[src_vid] =
          consume_offset_index_table.size() + dependers.size() + 2;
    }

    glp_add_cols(lp, dependers.size() * 2 + 2);
    VLOG(3) << "add " << dependers.size() * 2 + 2 << " to ILP";
    size_t num_rows = 0;
    for (auto item : dependers) {
      auto src_vid = item.first;
      auto produce_offset_src_vid = produce_offset_index_table[src_vid];
      auto consume_offset_src_vid = consume_offset_index_table[src_vid];
      VLOG(3) << "index of consume_offset_" << src_vid << ": "
              << consume_offset_src_vid;
      // produce_offset_vid
      VLOG(3) << "index of produce_offset_" << src_vid << ": "
              << produce_offset_src_vid;
      glp_set_col_bnds(lp, produce_offset_src_vid,
                       src_vid == 0 || src_vid == 1 ? GLP_FX : GLP_LO, 0., 0.);
      glp_set_obj_coef(lp, produce_offset_src_vid, -1.);
      // consume_offset_vid
      glp_set_col_bnds(lp, consume_offset_src_vid, GLP_LO, 0., 0.);
      glp_set_obj_coef(lp, consume_offset_src_vid, 1.);
      auto dst_vids = item.second;
      for (auto dst_vid : dst_vids) {
        auto produce_offset_dst_vid = produce_offset_index_table[dst_vid];
        VLOG(3) << "index of produce_offset_" << dst_vid << ": "
                << produce_offset_dst_vid;
        auto min_offset = dependees[dst_vid][src_vid].first;
        auto max_offset = dependees[dst_vid][src_vid].second;
        // produce_offset_src_vid <= min_offset + produce_offset_dst_vid
        glp_add_rows(lp, 2);
        glp_set_row_bnds(lp, ++num_rows, GLP_UP, 0., min_offset);
        ia.push_back(num_rows);
        ja.push_back(produce_offset_src_vid);
        ar.push_back(1.);
        VLOG(3) << "ILP coefficient: a[" << *ia.rbegin() << ", " << *ja.rbegin()
                << "] = " << *ar.rbegin();
        ia.push_back(num_rows);
        ja.push_back(produce_offset_dst_vid);
        ar.push_back(-1.);
        VLOG(3) << "ILP coefficient: a[" << *ia.rbegin() << ", " << *ja.rbegin()
                << "] = " << *ar.rbegin();
        // consume_offset_src_vid >= max_offset + produce_offset_dst_vid
        glp_set_row_bnds(lp, ++num_rows, GLP_LO, max_offset, 0.);
        ia.push_back(num_rows);
        ja.push_back(consume_offset_src_vid);
        ar.push_back(1.);
        VLOG(3) << "ILP coefficient: a[" << *ia.rbegin() << ", " << *ja.rbegin()
                << "] = " << *ar.rbegin();
        ia.push_back(num_rows);
        ja.push_back(produce_offset_dst_vid);
        ar.push_back(-1.);
        VLOG(3) << "ILP coefficient: a[" << *ia.rbegin() << ", " << *ja.rbegin()
                << "] = " << *ar.rbegin();
      }
    }
    VLOG(3) << "load ILP coefficient matrix";
    glp_load_matrix(lp, ia.size() - 1, ia.data(), ja.data(), ar.data());
    VLOG(3) << "solve ILP";
    glp_smcp params;
    glp_init_smcp(&params);
    params.msg_lev = GLP_MSG_OFF;
    glp_simplex(lp, &params);
    this->total_distance = glp_get_obj_val(lp);
    glp_delete_prob(lp);
    glp_free_env();
  }
  return this->total_distance;
}

template <typename Iterator>
Schedule::Ptr LinearSchedule(Iterator second, Iterator last) {
  auto first = second++;
  RAttr distance = second->rattr - first->rattr;
  if (std::distance(second, last) == 1) {
    return new Schedule{first->aattr, second->aattr, distance};
  }
  return new Schedule{first->aattr, LinearSchedule(second, last), distance};
}

Schedule BestGreedySchedule(const vector<RAttr>& rattrs,
                            const vector<AAttr>& aattrs,
                            const Linearizer* linearizer, size_t num_pruned) {
  vector<AttrUnion> attrs;
  attrs.reserve(rattrs.size());
  for (size_t i = 0; i < rattrs.size(); ++i) {
    attrs.push_back(AttrUnion{rattrs[i], aattrs[i]});
  }
  auto generator = GreedySchedules(attrs, linearizer, num_pruned);
  auto iter = generator.begin();
  Schedule::Ptr best{*iter};
  for (; iter != generator.end(); ++iter) {
    if (**iter < *best) {
      best = *iter;
    }
  }
  return *best;
}

Generator<Schedule::Ptr> GreedySchedules(const vector<AttrUnion>& attrs,
                                         const Linearizer* linearizer,
                                         size_t num_pruned) {
  VLOG(2) << "prepare data structures";
  unordered_map<AttrUnion, size_t> attr_map;
  unordered_map<size_t, AttrUnion> new_attrs_map;
  for (size_t i = 0; i < attrs.size(); ++i) {
    attr_map[attrs[i]] = i;
    new_attrs_map[i] = {attrs[i].rattr, attrs[i].aattr};
    VLOG(3) << "recv attr " << attrs[i];
  }

  // the value of reuses is a pair of <reuse list, insertion order>
  // each list element is a pair of <idx_l, idx_r>
  unordered_map<Schedule::Ptr, pair<list<pair<size_t, size_t>>, size_t>> reuses;

  VLOG(2) << "look for reuse";
  for (size_t i : Range(attrs.size())) {
    const auto& [left_rattr, left_aattr] = attrs[i];
    for (size_t j : Range(attrs.size(), i + 1)) {
      const auto& [right_rattr, right_aattr] = attrs[j];
      VLOG(3) << "checking reuse of " << attrs[i] << " + " << attrs[j];
      Schedule::Ptr operation{
          new Schedule{left_aattr, right_aattr,
                       static_cast<RAttr>(right_rattr - left_rattr)}};
      if (reuses.count(operation)) {
        VLOG(4) << "  already seen";
        continue;
      }

      // look for reuse of this operation over all operands
      unordered_set<size_t> used;
      // reuses.size() is used to keep track of the insertion order
      // it is ok because we won't delete from it until we've finished
      // inserting
      reuses[operation].second = reuses.size();
      for (size_t idx_l : Range(attrs.size())) {
        VLOG(4) << "  examining " << attrs[idx_l];
        const auto& attr_l = attrs[idx_l];
        const auto& [rattr_l, aattr_l] = attr_l;
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
        reuses[operation].first.push_back({idx_l, idx_r});
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
    if (reuses_iter->second.first.size() <= 1) {
      reuses_iter = reuses.erase(reuses_iter);
    } else {
      ++reuses_iter;
    }
  }

  auto aligns = [&linearizer](RAttr dis, size_t dim) -> bool {
    assert(linearizer != nullptr);
    auto idx = (*linearizer)(dis);
    if (idx[dim] != 0) {
      idx.erase(idx.begin() + dim);
      return std::all_of(idx.begin(), idx.end(),
                         [&](auto val) { return val == 0; });
    }
    return false;
  };

  if (linearizer != nullptr && reuses.size() > attrs.size()) {
    for (auto dim : linearizer->ReversedDims()) {
      if (std::any_of(reuses.begin(), reuses.end(),
                      [&](const auto& item) -> bool {
                        auto& [op, _] = item;
                        return aligns(op->distance, dim);
                      })) {
        auto reuses_iter = reuses.begin();
        while (reuses_iter != reuses.end()) {
          auto& [op, _] = *reuses_iter;
          auto& [reuse_list, insertion_order] = reuses_iter->second;
          if (aligns(op->distance, dim)) {
            auto reuse_list_iter = reuse_list.begin();
            while (reuse_list_iter != reuse_list.end()) {
              auto [idx_l, idx_r] = *reuse_list_iter;
              if (aligns(attrs[idx_r].rattr - attrs[idx_l].rattr, dim)) {
                ++reuse_list_iter;
              } else {
                reuse_list_iter = reuse_list.erase(reuse_list_iter);
              }
            }
            ++reuses_iter;
          } else {
            reuses_iter = reuses.erase(reuses_iter);
          }
        }
      }
    }
  }

  if (reuses.size() == 0) {
    co_yield LinearSchedule(attrs.begin(), attrs.end());
  } else {
    // candidates store the linear schedule for faster comparison
    vector<pair<Schedule::Ptr, vector<AttrUnion>>> candidates;
    for (const auto& [op, _] : reuses) {
      VLOG(5) << "find all compatible reuses that include " << *op;
      auto new_attrs = new_attrs_map;
      unordered_set<size_t> used;
      auto do_reuse_for = [&](const Schedule::Ptr& schedule) {
        auto reused_indices{reuses[schedule].first};
        auto iter = reused_indices.begin();
        while (iter != reused_indices.end()) {
          if (used.count(iter->first) == 0 && used.count(iter->second) == 0) {
            ++iter;
          } else {
            iter = reused_indices.erase(iter);
          }
        }
        if (reused_indices.size() > 1) {
          for (auto [idx_l, idx_r] : reused_indices) {
            VLOG(6) << "reusing " << *schedule << " for " << attrs[idx_l]
                    << " + " << attrs[idx_r];
            new_attrs[idx_l] = {new_attrs[idx_l].rattr, schedule};
            new_attrs.erase(idx_r);
            used.insert({idx_l, idx_r});
          }
        }
      };
      do_reuse_for(op);
      vector<pair<decltype(reuses)::key_type, decltype(reuses)::mapped_type>>
          sorted_reuses{reuses.begin(), reuses.end()};
      std::sort(sorted_reuses.begin(), sorted_reuses.end(),
                [](const auto& lhs, const auto& rhs) -> bool {
                  if (lhs.second.first.size() == rhs.second.first.size()) {
                    if (lhs.first->distance == rhs.first->distance) {
                      return lhs.second.second < rhs.second.second;
                    }
                    return lhs.first->distance < rhs.first->distance;
                  }
                  return lhs.second.first.size() > rhs.second.first.size();
                });
      for (const auto& [op, _] : sorted_reuses) {
        do_reuse_for(op);
      }
      vector<AttrUnion> new_attr_vec;
      new_attr_vec.reserve(new_attrs.size());
      for (size_t i = 0; i < attrs.size(); ++i) {
        if (new_attrs.count(i)) {
          new_attr_vec.push_back(new_attrs[i]);
        }
      }
      candidates.emplace_back(
          LinearSchedule(new_attr_vec.begin(), new_attr_vec.end()),
          new_attr_vec);
    }
    VLOG(3) << "processing candidates";
    std::nth_element(
        candidates.begin(),
        std::min(candidates.begin() + num_pruned - 1, candidates.end()),
        candidates.end(), [](const auto& lhs, const auto& rhs) -> bool {
          return *lhs.first < *rhs.first;
        });
    VLOG(3) << "partially sorted candidates";
    candidates.erase(
        std::min(candidates.begin() + num_pruned, candidates.end()),
        candidates.end());
    VLOG(3) << "erased unused candidates";
    for (const auto& [_, new_attrs] : candidates) {
      for (const auto& schedule :
           GreedySchedules(new_attrs, linearizer, num_pruned)) {
        co_yield schedule;
      }
    }
  }
}

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
void from_json(const json& j, Schedule& v) {
  v.left = j["left"].get<Schedule::ChildType>();
  v.right = j["right"].get<Schedule::ChildType>();
  v.distance = j["distance"].get<RAttr>();
}
void from_json(const json& j, Schedule::ChildType& v) {
  if (j.contains("left") && j.contains("right") && j.contains("distance")) {
    auto ptr = new Schedule;
    j.get_to(*ptr);
    v = Schedule::Ptr{ptr};
  } else {
    v = j.get<AAttr>();
  }
}