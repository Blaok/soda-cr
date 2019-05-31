#include <iostream>

#include <glog/logging.h>
#include <nlohmann/json.hpp>

#include "schedule.h"

using nlohmann::json;

int main(int argc, char* argv[]) {
  google::InitGoogleLogging(argv[0]);
  FLAGS_alsologtostderr = true;
  FLAGS_colorlogtostderr = true;

  VLOG(1) << "sizeof(Schedule) = " << sizeof(Schedule);
  VLOG(1) << "sizeof(AAttrUninon) = " << sizeof(AAttrUnion);
  VLOG(1) << "sizeof(Schedule::Ptr) = " << sizeof(Schedule::Ptr);

  json json_root;
  std::cin >> json_root;
  auto schedule = json_root.get<Schedule>();
  VLOG(1) << schedule;
  json_root["num_ops"] = schedule.NumOps();
  json_root["total_distance"] = schedule.TotalDistance();
  std::cout << json_root.dump(2);
  return 0;
}
