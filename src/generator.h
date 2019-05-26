#ifndef GENERATOR_H_
#define GENERATOR_H_

#include <experimental/coroutine>
#include <list>

template <typename T>
struct Generator {
  struct promise_type {
    T value;

    auto yield_value(const T& value) {
      this->value = value;
      return std::experimental::suspend_always{};
    }
    Generator get_return_object() { return Generator{this}; };
    auto initial_suspend() { return std::experimental::suspend_always{}; }
    auto final_suspend() { return std::experimental::suspend_always{}; }
    auto return_void() { return std::experimental::suspend_always{}; }
    void unhandled_exception() { std::terminate(); }
  };

  struct iterator {
    using difference_type = int64_t;
    using value_type = T;
    using pointer = T*;
    using reference = T&;
    using iterator_category = std::input_iterator_tag;

    std::experimental::coroutine_handle<promise_type> coroutine;
    bool done;

    iterator& operator++() {
      coroutine.resume();
      done = coroutine.done();
      return *this;
    }

    bool operator==(iterator const& rhs) const { return done == rhs.done; }
    bool operator!=(iterator const& rhs) const { return !(*this == rhs); }

    const T& operator*() const { return coroutine.promise().value; }
    const T* operator->() const { return &**this; }
  };

  std::experimental::coroutine_handle<promise_type> coroutine;

  explicit Generator(promise_type* promise)
      : coroutine(decltype(coroutine)::from_promise(*promise)) {}
  Generator(const Generator&) = delete;
  Generator(Generator&& rhs) : coroutine(rhs.coroutine) {
    rhs.coroutine = nullptr;
  }

  ~Generator() {
    if (coroutine) {
      coroutine.destroy();
    }
  }

  Generator& operator=(const Generator&) = delete;
  Generator& operator=(Generator&& rhs) {
    coroutine = rhs.coroutine;
    rhs.coroutine = nullptr;
  }

  iterator begin() {
    coroutine.resume();
    return {coroutine, coroutine.done()};
  }
  iterator end() { return {coroutine, true}; }
};

template <typename T, typename Iterator>
inline Generator<std::list<T>> Combinations(Iterator begin, Iterator end,
                                            size_t m) {
  VLOG(5) << "Combinations of " << m << " out of " << std::distance(begin, end);
  if (m == 0) {
    co_yield std::list<T>();
  } else if (std::distance(begin, end) == m) {
    co_yield std::list<T>{begin, end};
  } else {
    const auto& front = *begin;
    for (auto v : Combinations<T>(++begin, end, m - 1)) {
      v.push_front(front);
      co_yield v;
    }
    for (const auto& v : Combinations<T>(begin, end, m)) {
      co_yield v;
    }
  }
}

inline Generator<size_t> Range(size_t end, size_t begin = 0) {
  for (; begin < end; ++begin) {
    co_yield begin;
  }
}

inline Generator<size_t> ReversedRange(size_t end, size_t begin = 0) {
  while (begin < end) {
    --end;
    co_yield end;
  }
}

#endif  // GENERATOR_H_
