#ifndef SCHEDULE_H_
#define SCHEDULE_H_

#include <atomic>
#include <iterator>
#include <limits>
#include <memory>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

#include <glog/logging.h>
#include <boost/intrusive_ptr.hpp>
#include <nlohmann/json.hpp>

#include "generator.h"

using RAttr = uint16_t;
using AAttr = uint16_t;

struct Attr {
  RAttr rattr;
  AAttr aattr;

  bool operator==(const Attr& rhs) const {
    return rattr == rhs.rattr && aattr == rhs.aattr;
  }
  bool operator!=(const Attr& rhs) const { return !(*this == rhs); }
};

namespace std {

template <>
struct hash<Attr> {
  using argument_type = Attr;
  using result_type = size_t;
  result_type operator()(const argument_type& key) const noexcept {
    return std::hash<RAttr>{}(key.rattr) ^ std::hash<AAttr>{}(key.aattr);
  }
};

template <>
struct hash<std::vector<Attr>> {
  using argument_type = vector<Attr>;
  using result_type = size_t;
  result_type operator()(const argument_type& key) const noexcept {
    result_type result = 0;
    auto hasher = std::hash<Attr>{};
    for (const auto& attr : key) {
      result ^= hasher(attr);
    }
    return result;
  }
};

}  // namespace std

struct Schedule {
  using Ptr = boost::intrusive_ptr<const Schedule>;
  using AttrSet = std::unordered_set<Attr>;
  using ChildType = std::variant<Ptr, AAttr>;
  ChildType left;
  ChildType right;
  RAttr distance;

  mutable uint32_t references = 0;
#ifdef SCHEDULE_CACHE_ATTR_SET
  mutable std::shared_ptr<const AttrSet> norm_attr_set;
#endif

  bool LeftIsLeaf() const { return std::holds_alternative<AAttr>(left); }
  bool RightIsLeaf() const { return std::holds_alternative<AAttr>(right); }

  static std::atomic_uint64_t constructed;
  static std::atomic_uint64_t deconstructed;
  void* operator new(size_t size) {
    ++constructed;
    return ::operator new(size);
  }
  void operator delete(void* ptr) {
    ++deconstructed;
    ::operator delete(ptr);
    if (constructed == deconstructed) {
      LOG(INFO) << "Schedule construct-and-deconstructed: " << constructed;
    }
  }

  std::string ToStrWithOffset(RAttr offset = 0) const {
    return "(" +
           (LeftIsLeaf() ? std::to_string(std::get<AAttr>(left))
                         : std::get<Ptr>(left)->ToStrWithOffset(offset)) +
           "==" + std::to_string(distance) + "=>" +
           (RightIsLeaf()
                ? std::to_string(std::get<AAttr>(right))
                : std::get<Ptr>(right)->ToStrWithOffset(offset + distance)) +
           ")";
  }

  Generator<Schedule> Children() const {
    co_yield* this;
    for (const auto& child : {left, right}) {
      if (auto ptr = std::get_if<Ptr>(&child)) {
        for (const auto& schedule : (*ptr)->Children()) {
          co_yield schedule;
        }
      }
    }
  }

  size_t NumOps() const;
  size_t TotalDistance() const;

  Generator<Attr> GetAttrsWithOffset(RAttr offset = 0) const {
    if (auto ptr = std::get_if<AAttr>(&left)) {
      co_yield Attr{offset, *ptr};
    } else {
      for (const auto& attr : std::get<Ptr>(left)->GetAttrsWithOffset(offset)) {
        co_yield attr;
      }
    }

    offset += distance;

    if (auto ptr = std::get_if<AAttr>(&right)) {
      co_yield Attr{offset, *ptr};
    } else {
      for (const auto& attr :
           std::get<Ptr>(right)->GetAttrsWithOffset(offset)) {
        co_yield attr;
      }
    }
  }

  Generator<Attr> NormAttrs() const { return GetAttrsWithOffset(); }

#ifdef SCHEDULE_CACHE_ATTR_SET
  const AttrSet& NormAttrSet() const {
    if (norm_attr_set == nullptr) {
      auto attrs = NormAttrs();
      norm_attr_set =
          std::make_shared<const AttrSet>(attrs.begin(), attrs.end());
    }
    return *norm_attr_set;
  }
#else
  AttrSet NormAttrSet() const {
    auto attrs = NormAttrs();
    return {attrs.begin(), attrs.end()};
  }
#endif

  bool operator==(const Schedule& rhs) const {
    return NormAttrSet() == rhs.NormAttrSet();
  }

  bool operator!=(const Schedule& rhs) const { return !(*this == rhs); }
};

inline void intrusive_ptr_add_ref(const Schedule* ptr) { ++ptr->references; }
inline void intrusive_ptr_release(const Schedule* ptr) {
  if (--ptr->references == 0) {
    delete ptr;
  }
}

using AAttrUnion = Schedule::ChildType;

namespace std {

template <>
struct hash<Schedule> {
  using argument_type = Schedule;
  using result_type = size_t;
  result_type operator()(const argument_type& key) const noexcept {
    result_type result = 0;
    for (const auto& attr : key.NormAttrSet()) {
      result ^= std::hash<Attr>{}(attr);
    }
    return result;
  }
};

template <>
struct hash<Schedule::Ptr> {
  using argument_type = Schedule::Ptr;
  using result_type = size_t;
  result_type operator()(const argument_type& key) const noexcept {
    return std::hash<Schedule>{}(*key);
  }
};

template <>
struct equal_to<Schedule::Ptr> {
  constexpr bool operator()(const Schedule::Ptr& lhs,
                            const Schedule::Ptr& rhs) const {
    return *lhs == *rhs;
  }
};

template <>
struct equal_to<AAttrUnion> {
  constexpr bool operator()(const AAttrUnion& lhs,
                            const AAttrUnion& rhs) const {
    if (lhs.index() != rhs.index()) {
      return false;
    }
    for (size_t i = 0; i < std::variant_size_v<AAttrUnion>; ++i) {
      if (lhs.index() == i and rhs.index() == i) {
        if (auto ptr = std::get_if<Schedule::Ptr>(&lhs)) {
          return **ptr == *std::get<Schedule::Ptr>(rhs);
        }
        return std::get<AAttr>(lhs) == std::get<AAttr>(rhs);
      }
    }
    return false;
  }
};

}  // namespace std

struct AttrUnion {
  RAttr rattr;
  AAttrUnion aattr;

  bool operator==(const AttrUnion& rhs) const {
    return rattr == rhs.rattr && std::equal_to<AAttrUnion>{}(aattr, rhs.aattr);
  }
  bool operator!=(const AttrUnion& rhs) const { return !(*this == rhs); }
};

namespace std {
template <>
struct hash<AttrUnion> {
  using argument_type = AttrUnion;
  using result_type = size_t;
  result_type operator()(const argument_type& key) const noexcept {
    return std::hash<RAttr>{}(key.rattr) ^ std::hash<AAttrUnion>{}(key.aattr);
  }
};
}  // namespace std

// debug helpers
inline std::ostream& operator<<(std::ostream& os, const Attr& attr) {
  return os << attr.aattr << "@" << attr.rattr;
}
inline std::ostream& operator<<(std::ostream& os, const Schedule& schedule) {
  return os << schedule.ToStrWithOffset();
}
inline std::ostream& operator<<(std::ostream& os, const AttrUnion& attr) {
  if (auto ptr = std::get_if<AAttr>(&attr.aattr)) {
    os << *ptr;
  } else {
    os << *std::get<Schedule::Ptr>(attr.aattr);
  }
  return os << "@" << attr.rattr;
}

// json serializers
void to_json(nlohmann::json& j, const Attr& v);
void to_json(nlohmann::json& j, const Schedule& v);
void to_json(nlohmann::json& j, const AAttrUnion& v);
void to_json(nlohmann::json& j, const AttrUnion& v);
void from_json(const nlohmann::json& j, Schedule& v);
void from_json(const nlohmann::json& j, Schedule::ChildType& v);

// schedule creators
template <typename Iterator>
Schedule LinearSchedule(Iterator first, Iterator last);
Schedule BestGreedySchedule(const std::vector<RAttr>& rattrs,
                            const std::vector<AAttrUnion>& aattrs);
Schedule BestGreedySchedule(const std::vector<RAttr>& rattrs,
                            const std::vector<AAttr>& aattrs);

#endif  // SCHEDULE_H_
