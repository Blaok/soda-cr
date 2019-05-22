#include "schedules.h"

#include <algorithm>
#include <atomic>
#include <functional>
#include <memory>
#include <unordered_set>

#include <glog/logging.h>

#include "generator.h"

using std::atomic_uint64_t;
using std::count;
using std::distance;
using std::find;
using std::function;
using std::make_shared;
using std::unordered_set;
using std::vector;

atomic_uint64_t Schedules::constructed = 0;
atomic_uint64_t Schedules::deconstructed = 0;
bool Schedules::cache_schedules = true;

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
