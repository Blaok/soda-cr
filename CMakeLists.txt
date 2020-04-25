cmake_minimum_required(VERSION 3.1)

set(WITH_GFLAGS OFF CACHE BOOL "disable gflags" FORCE)
add_subdirectory(glog EXCLUDE_FROM_ALL)
add_subdirectory(smart_ptr EXCLUDE_FROM_ALL)
add_subdirectory(json EXCLUDE_FROM_ALL)

project(soda-cr)

add_library(schedule STATIC src/schedule.cpp)
add_library(schedules STATIC src/schedules.cpp)
add_executable(soda-cr src/soda-cr.cpp)
add_executable(calc-cost src/calc-cost.cpp)
target_compile_features(schedule PUBLIC cxx_std_17)
target_compile_options(schedule PUBLIC -stdlib=libc++ -fcoroutines-ts -Wall)
target_compile_options(glog PUBLIC -stdlib=libc++)
target_link_libraries(
  schedule
  PRIVATE libglpk.a libltdl.so libz.so
  PUBLIC glog::glog nlohmann_json::nlohmann_json libc++.a libc++abi.a)
target_link_libraries(schedules PUBLIC schedule)
target_link_libraries(soda-cr PRIVATE schedules schedule)
target_link_libraries(calc-cost PRIVATE schedule)

# optional feature
target_compile_definitions(schedule PUBLIC SCHEDULE_CACHE_ATTR_SET)
