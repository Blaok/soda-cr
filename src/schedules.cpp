#include "schedules.h"

#include <algorithm>
#include <atomic>
#include <functional>
#include <memory>
#include <tuple>
#include <unordered_set>
#include <variant>

#include <glog/logging.h>

#include "generator.h"

using std::atomic_uint64_t;
using std::count;
using std::distance;
using std::find;
using std::function;
using std::get_if;
using std::make_shared;
using std::tuple;
using std::unordered_set;
using std::vector;

atomic_uint64_t Schedules::constructed = 0;
atomic_uint64_t Schedules::deconstructed = 0;
bool Schedules::cache_schedules = true;
bool Schedules::bottom_up = true;

Schedules::Key Schedules::KeyOf(const Bits& operands) const {
  RAttr offset = rattrs[distance(operands.begin(),
                                 find(operands.begin(), operands.end(), true))];
  Key key;
  for (size_t i = 0; i < operands.size(); ++i) {
    if (operands[i]) {
      key.push_back({static_cast<RAttr>(rattrs[i] - offset), aattrs[i]});
    }
  }
  VLOG(8) << "key of " << operands << " is " << key;
  return key;
}

Generator<AAttrUnion> Schedules::Generate() const {
  if (bottom_up) {
    if (rattrs.size() == 2) {
      co_yield Schedule::Ptr{
          new Schedule{aattrs[0], aattrs[1], rattrs[1] - rattrs[0]}};
    } else {
      vector<RAttr> new_rattrs{rattrs.begin(), rattrs.end() - 1};
      vector<AAttr> new_aattrs{aattrs.begin(), aattrs.end() - 1};
      const auto& new_rattr = *rattrs.rbegin();
      const auto& new_aattr = *aattrs.rbegin();
      Schedules schedules{new_rattrs, new_aattrs};
      for (auto schedule_ptr : schedules.Generate()) {
        VLOG(5) << "old schedule: " << schedule_ptr << " new op: " << new_aattr
                << "@" << (new_rattr - *rattrs.begin());
        if (auto schedule = PtrOrNull(schedule_ptr)) {
          vector<tuple<const AAttrUnion*, RAttr, int>> stack{
              {&schedule_ptr, *rattrs.begin(), 0}};
          VLOG(8) << "==> push " << *std::get<0>(stack.back()) << " ==>";
          while (!stack.empty()) {
            auto& [top_node_ptr, top_rattr, top_state] = stack.back();
            auto top_node = PtrOrNull(*top_node_ptr);
            switch (top_state) {
              case 0: {
                // First time visit this node.
                VLOG(6) << "child: " << top_node_ptr;
                Schedule::Ptr new_node{new Schedule{*top_node_ptr, new_aattr,
                                                    new_rattr - top_rattr}};
                const AAttrUnion* last_parent = top_node_ptr;
                for (auto it = stack.crbegin(); it != stack.crend(); ++it) {
                  if (it == stack.crbegin()) {  // Skip self.
                    continue;
                  }
                  auto& [parent_ptr, rattr, state] = *it;
                  auto parent = std::get<Schedule::Ptr>(*parent_ptr);
                  VLOG(7) << "ancestor: " << parent;
                  if (last_parent == &parent->left) {
                    // Replace left child & keep right child.
                    new_node =
                        new Schedule{new_node, parent->right, parent->distance};
                    last_parent = parent_ptr;
                  } else if (last_parent == &parent->right) {
                    // Replace right child & keep left
                    new_node =
                        new Schedule{parent->left, new_node, parent->distance};
                    last_parent = parent_ptr;
                  } else {
                    LOG(FATAL)
                        << "should not have gone here; last_parent: "
                        << *last_parent << "; parent->left: " << parent->left
                        << "; parent->right: " << parent->right;
                  }
                }
                VLOG(6) << "yield: " << new_node;
                co_yield new_node;
                if (top_node) {
                  top_state = 1;
                } else {
                  VLOG(8) << "<== pop " << *std::get<0>(stack.back()) << " <==";
                  stack.pop_back();
                }
                break;
              }
              case 1: {
                // Second time visit this node, recurse into left child.
                top_state = 2;
                stack.push_back({&top_node->left, top_rattr, 0});
                VLOG(8) << "==> push " << *std::get<0>(stack.back()) << " ==>";
                break;
              }
              case 2: {
                // Third time visit this node, recurse into right child.
                top_state = 3;
                stack.push_back(
                    {&top_node->right, top_rattr + top_node->distance, 0});
                VLOG(8) << "==> push " << *std::get<0>(stack.back()) << " ==>";
                break;
              }
              case 3: {
                VLOG(8) << "<== pop " << *std::get<0>(stack.back()) << " <==";
                stack.pop_back();
                break;
              }
              default: { LOG(FATAL) << "invalid traversal state"; }
            }
          }
        } else {
          co_yield Schedule::Ptr{new Schedule{schedule_ptr, new_aattr,
                                              new_rattr - *rattrs.begin()}};
        }
      }
    }
  } else {
    if (schedules.empty()) {
      VLOG(3) << "generate schedules for " << operands;
      const auto n = count(operands.begin(), operands.end(), true);
      size_t cap = 1;
      for (size_t i = 0; i < n; ++i) {
        cap *= i * 2 + 1;
      }
      schedules.reserve(cap);
      const auto num_operands = rattrs.size();
      vector<size_t> indices;
      indices.reserve(n);
      for (size_t i = 0; i < num_operands; ++i) {
        if (operands[i]) indices.push_back(i);
      }
      if (n == 1) {
        VLOG(3) << "singleton schedule: " << aattrs[*indices.begin()];
        if (Schedules::cache_schedules) {
          schedules.push_back(aattrs[*indices.begin()]);
        }
        co_yield aattrs[*indices.begin()];
      } else {
        for (auto m : Range(n - 1)) {
          VLOG(4) << "m = " << m;
          for (const auto& selection :
               Combinations<size_t>(indices.begin() + 1, indices.end(), m)) {
            ++stat->trip_count[0];
            VLOG(5) << "operands: " << operands;

            // calculate indices of the left part
            auto left_indices = selection;
            left_indices.push_front(*indices.begin());
            VLOG(5) << "left indices: " << left_indices;

            // calculate indices of the right part
            decltype(left_indices) right_indices;
            unordered_set<size_t> left_index_set{left_indices.begin(),
                                                 left_indices.end()};
            for (const auto& idx : indices) {
              if (left_index_set.count(idx) == 0) {
                right_indices.push_back(idx);
              }
            }
            VLOG(5) << "right indices: " << right_indices;

            // generate the bitmasks
            Bits left_operands(num_operands);
            Bits right_operands(num_operands);
            for (auto idx : left_indices) {
              left_operands[idx] = true;
            }
            for (auto idx : right_indices) {
              right_operands[idx] = true;
            }

            // iterate over all possible schedules
            VLOG(5) << "operands: " << left_operands << " | " << right_operands;
            for (auto left : GetSchedules(left_operands)) {
              ++stat->trip_count[1];
              for (auto right : GetSchedules(right_operands)) {
                ++stat->trip_count[2];
                RAttr distance = rattrs[*right_indices.begin()] -
                                 rattrs[*left_indices.begin()];
                VLOG(7) << "Schedule{" << left << ", " << right << ", "
                        << distance << "} generated for " << operands;
                Schedule::Ptr schedule{new Schedule{left, right, distance}};
                if (Schedules::cache_schedules) {
                  schedules.push_back(schedule);
                }
                co_yield schedule;
              }
            }
          }
        }
      }
    } else {
      VLOG(3) << "loading schedules for " << operands;
      for (auto schedule : schedules) {
        co_yield schedule;
      }
    }
  }
}
