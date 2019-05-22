#include <chrono>
#include <functional>
#include <iostream>
#include <limits>
#include <memory>
#include <thread>
#include <unordered_set>
#include <vector>

#include <sys/resource.h>
#include <sys/time.h>

#include <glog/logging.h>
#include <nlohmann/json.hpp>

#include "generator.h"
#include "schedule.h"
#include "schedules.h"

using std::make_shared;
using std::numeric_limits;
using std::shared_ptr;
using std::string;
using std::unordered_set;
using std::vector;
using std::chrono::duration;
using std::chrono::system_clock;

using nlohmann::json;

enum class Strategy { kGreedy, kBruteForce, kDefault = kGreedy };

int main(int argc, char* argv[]) {
  google::InitGoogleLogging(argv[0]);
  FLAGS_alsologtostderr = true;
  FLAGS_colorlogtostderr = true;

  VLOG(1) << "sizeof(Schedule) = " << sizeof(Schedule);
  VLOG(1) << "sizeof(Schedules) = " << sizeof(Schedules);
  VLOG(1) << "sizeof(AAttrUninon) = " << sizeof(AAttrUnion);
  VLOG(1) << "sizeof(Schedule::Ptr) = " << sizeof(Schedule::Ptr);

  string kGreedyStr = "--greedy";
  string kBruteForceStr = "--brute-force";
  string usage = string("usage: ") + argv[0] + " [" + kGreedyStr + "|" +
                 kBruteForceStr + "]";
  Strategy strategy = Strategy::kDefault;

  if (argc == 2) {
    if (argv[1] == kBruteForceStr) {
      strategy = Strategy::kBruteForce;
    } else if (argv[1] == kGreedyStr) {
      strategy = Strategy::kGreedy;
    }
  } else if (argc > 2) {
    LOG(ERROR) << "too many arguments";
    LOG(INFO) << usage;
    return 1;
  }

  json json_root;
  std::cin >> json_root;
  LOG(INFO) << "rattrs: " << json_root["rattrs"];
  LOG(INFO) << "aattrs: " << json_root["aattrs"];
  vector<RAttr> rattrs{json_root["rattrs"].begin(), json_root["rattrs"].end()};
  vector<AAttr> aattrs{json_root["aattrs"].begin(), json_root["aattrs"].end()};

  Schedule best;
  auto t1 = system_clock::now();
  switch (strategy) {
    case Strategy::kGreedy:
      best = BestGreedySchedule(rattrs, aattrs);
      break;
    case Strategy::kBruteForce: {
      Schedules::Cache cache;
      best = (new Schedules(rattrs, aattrs, nullptr, &cache))->Best();
      VLOG(1) << "Schedule::constructed: " << Schedule::constructed.load();
      VLOG(1) << "Schedule::deconstructed: " << Schedule::deconstructed.load();
      VLOG(1) << "Schedules::constructed: " << Schedules::constructed.load();
      VLOG(1) << "Schedules::deconstructed: " << Schedules::deconstructed.load();
      break;
    }
    default:
      LOG(FATAL) << "unexpected strategy";
  }
  auto t2 = system_clock::now();

  LOG(INFO) << "best: " << best;
  LOG(INFO) << "cost: " << best.Cost();
  struct rusage resource_usage;
  PCHECK(getrusage(RUSAGE_SELF, &resource_usage) == 0)
      << "failed to get resource usage";
  LOG(INFO) << "maxrss: " << resource_usage.ru_maxrss << " kB";
  LOG(INFO) << "walltime: " << duration<float>(t2 - t1).count() << " s";
  std::cout << json(best).dump(2);
  return 0;
}
