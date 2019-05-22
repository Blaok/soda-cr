cmake_minimum_required(VERSION 3.0)

set(WITH_GFLAGS OFF CACHE BOOL "disable gflags" FORCE)
add_subdirectory(glog EXCLUDE_FROM_ALL)
add_subdirectory(smart_ptr EXCLUDE_FROM_ALL)
add_subdirectory(json EXCLUDE_FROM_ALL)

project(tcse)

add_executable(tcse src/schedule.cpp src/schedules.cpp src/tcse.cpp)
target_compile_features(tcse PRIVATE cxx_std_17)
target_compile_options(tcse PRIVATE -stdlib=libc++ -fcoroutines-ts -Wall)
target_compile_options(glog PUBLIC -stdlib=libc++)
target_link_libraries(tcse
                      libc++.a
                      libc++abi.a
                      glog::glog
                      nlohmann_json::nlohmann_json)
