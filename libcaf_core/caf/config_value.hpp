/******************************************************************************
 *                       ____    _    _____                                   *
 *                      / ___|  / \  |  ___|    C++                           *
 *                     | |     / _ \ | |_       Actor                         *
 *                     | |___ / ___ \|  _|      Framework                     *
 *                      \____/_/   \_|_|                                      *
 *                                                                            *
 * Copyright 2011-2018 Dominik Charousset                                     *
 *                                                                            *
 * Distributed under the terms and conditions of the BSD 3-Clause License or  *
 * (at your option) under the terms and conditions of the Boost Software      *
 * License 1.0. See accompanying files LICENSE and LICENSE_ALTERNATIVE.       *
 *                                                                            *
 * If you did not receive a copy of the license files, see                    *
 * http://opensource.org/licenses/BSD-3-Clause and                            *
 * http://www.boost.org/LICENSE_1_0.txt.                                      *
 ******************************************************************************/

#ifndef CAF_CONFIG_VALUE_HPP
#define CAF_CONFIG_VALUE_HPP

#include <string>
#include <vector>
#include <cstdint>

#include "caf/atom.hpp"
#include "caf/variant.hpp"
#include "caf/duration.hpp"

namespace caf {

/// A type for config parameters with similar interface to a `variant`. This
/// type is not implemented as a simple variant alias because variants cannot
/// contain lists of themselves.
class config_value {
public:
  using T0 = std::string;
  using T1 = double;
  using T2 = int64_t;
  using T3 = bool;
  using T4 = atom_value;
  using T5 = duration;
  using T6 = std::vector<config_value>;

  using types = detail::type_list<T0, T1, T2, T3, T4, T5, T6>;

  using variant_type = variant<T0, T1, T2, T3, T4, T5, T6>;

  config_value() = default;

  config_value(config_value& other);

  config_value(config_value&& other) = default;

  config_value(const config_value& other) = default;

  template <class T>
  config_value(T&& x) : data_(std::forward<T>(x)) {
    // nop
  }

  config_value& operator=(config_value& other);

  config_value& operator=(config_value&& other) = default;

  config_value& operator=(const config_value& other) = default;

  template <class T>
  config_value& operator=(T&& x) {
    data_ = std::forward<T>(x);
    return *this;
  }

  ~config_value();

  inline size_t index() const {
    return data_.index();
  }

  inline bool valueless_by_exception() const {
    return data_.valueless_by_exception();
  }

  /// @cond PRIVATE
  template <int Pos>
  bool is(std::integral_constant<int, Pos>) const {
    return data_.index() == Pos;
  }

  template <class T>
  bool is() const {
    using namespace detail;
    int_token<tl_index_where<types,
                             tbind<is_same_ish, T>::template type>::value>
      token;
    return is(token);
  }

  template <class Visitor>
  auto apply(Visitor&& visitor) -> decltype(visitor(std::declval<T0&>())) {
    return data_.apply(visitor);
  }

  template <class Visitor>
  auto apply(Visitor&& visitor) const
  -> decltype(visitor(std::declval<const T0&>())) {
    return data_.apply(visitor);
  }

  template <int Pos>
  const typename detail::tl_at<types, Pos>::type&
  get(std::integral_constant<int, Pos> token) const {
    return data_.get(token);
  }

  template <int Pos>
  typename detail::tl_at<types, Pos>::type&
  get(std::integral_constant<int, Pos> token) {
    return data_.get(token);
  }

  inline variant_type& data() {
    return data_;
  }

  inline const variant_type& data() const {
    return data_;
  }

  /// @endcond

private:
  variant_type data_;
};

/// @relates config_value
template <class Visitor>
auto visit(Visitor&& f, config_value& x)
  -> decltype(f(std::declval<int64_t&>())) {
  return visit(std::forward<Visitor>(f), x.data());
}

/// @relates config_value
template <class Visitor>
auto visit(Visitor&& f, const config_value& x)
  -> decltype(f(std::declval<const int64_t&>())) {
  return visit(std::forward<Visitor>(f), x.data());
}

/// @relates config_value
template <class T>
bool holds_alternative(const config_value& x) {
  return holds_alternative<T>(x.data());
}

/// @relates config_value
template <class T>
T& get(config_value& x) {
  return get<T>(x.data());
}

/// @relates config_value
template <class T>
const T& get(const config_value& x) {
  return get<T>(x.data());
}

/// @relates config_value
template <class T>
T* get_if(config_value* x) {
  return x != nullptr ? get_if<T>(&(x->data())) : nullptr;
}

/// @relates config_value
template <class T>
const T* get_if(const config_value* x) {
  return x != nullptr ? get_if<T>(&(x->data())) : nullptr;
}

/// @relates config_value
template <class Inspector>
typename Inspector::result_type inspect(Inspector& f, config_value& x) {
  return f(meta::type_name("config_value"), x.data());
}

} // namespace caf

#endif // CAF_CONFIG_VALUE_HPP
