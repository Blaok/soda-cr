#ifndef LINEARIZER_H_
#define LINEARIZER_H_

#include <algorithm>
#include <vector>

#include <nlohmann/json.hpp>

class Linearizer {
 public:
  using Int = int;
  Linearizer(const nlohmann::json& j)
      : maxs_{j["maxs"].begin(), j["maxs"].end()},
        mins_{j["mins"].begin(), j["mins"].end()},
        sizes_{j["sizes"].begin(), j["sizes"].end()} {
    assert(maxs_.size() == mins_.size());
    assert(maxs_.size() == sizes_.size());
  }
  size_t NumDim() const { return maxs_.size(); }
  std::vector<size_t> Dims() const {
    std::vector<size_t> dims(NumDim());
    for (size_t d = 0; d < NumDim(); ++d) {
      dims[d] = d;
    }
    return dims;
  }
  std::vector<size_t> ReversedDims() const {
    auto dims = Dims();
    std::reverse(dims.begin(), dims.end());
    return dims;
  }
  std::vector<Int> Weights() const {
    std::vector<Int> weights(NumDim(), 1);
    for (auto d : Dims()) {
      if (d == 0) {
        continue;
      }
      weights[d] = weights[d - 1] * sizes_[d - 1];
    }
    return weights;
  }
  Int Apply(const std::vector<Int>& rattr) const {
    Int result = 0;
    for (auto d : Dims()) {
      result += (rattr[d] - mins_[d]) * Weights()[d];
    }
    return result;
  }
  std::vector<Int> Restore(Int rattr) const {
    std::vector<Int> restored;
    auto weights = Weights();
    for (auto d : ReversedDims()) {
      auto rval = rattr / weights[d];
      rattr -= rval * weights[d];
      restored.push_back(mins_[d] + rval);
    }
    std::reverse(restored.begin(), restored.end());
    return restored;
  }
  Int operator()(const std::vector<Int>& rattr) const { return Apply(rattr); }
  std::vector<Int> operator()(Int rattr) const { return Restore(rattr); }
  const auto& Mins() const { return mins_; }
  const auto& Maxs() const { return maxs_; }
  const auto& Sizes() const { return sizes_; }

 private:
  std::vector<Int> maxs_;
  std::vector<Int> mins_;
  std::vector<Int> sizes_;
};

#endif  // LINEARIZER_H_