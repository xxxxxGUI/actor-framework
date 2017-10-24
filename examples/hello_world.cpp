#include <cctype>
#include <cstring>
#include <iostream>
#include <string>

#include "caf/all.hpp"

#define CAF_SUITE parser
#include "caf/test/unit_test.hpp"
#include "caf/test/unit_test_impl.hpp"

using std::cout;
using std::endl;
using std::string;

using namespace caf;

#define start()                                                                \
  parser_result<Iterator> result;                                              \
  goto s_init;                                                                 \
  s_unexpected_eof:                                                            \
  result.code = ec::unexpected_eof;                                            \
  s_return:                                                                    \
  result.last = i;                                                             \
  return result;                                                               \
  {                                                                            \
    static constexpr ec mismatch_ec = ec::unexpected_character

#define state(name)                                                            \
  result.code = mismatch_ec;                                                   \
  goto s_return;                                                               \
  }                                                                            \
  {                                                                            \
    static constexpr ec mismatch_ec = ec::unexpected_character;                \
    s_##name : __attribute__((unused));                                        \
    if (i == last)                                                             \
      goto s_unexpected_eof;                                                   \
    e_##name : __attribute__((unused));

#define term_state(name)                                                       \
  result.code = mismatch_ec;                                                   \
  goto s_return;                                                               \
  }                                                                            \
  {                                                                            \
    static constexpr ec mismatch_ec = ec::trailing_character;                  \
    s_##name : __attribute__((unused));                                        \
    if (i == last)                                                             \
      goto s_fin;                                                              \
    e_##name : __attribute__((unused));

#define fin()                                                                  \
  result.code = mismatch_ec;                                                   \
  goto s_return;                                                               \
  }                                                                            \
  s_fin:                                                                       \
  result.code = ec::success;                                                   \
  goto s_return;

#define input(condition, target)                                               \
  if (condition) {                                                             \
    ++i;                                                                       \
    goto s_##target;                                                           \
  }

#define action(condition, target, statement)                                   \
  if (condition) {                                                             \
    statement;                                                                 \
    ++i;                                                                       \
    goto s_##target;                                                           \
  }

/// Invokes a nested parser `parser`. Calls the `callback` with the produced
/// result if the nested parser produces a result. Jumps to `target` if the
/// nested parser returns `ec::trailing_character`.
#define invoke_parser(condition, target, parser, callback)                     \
  if (condition) {                                                             \
    {                                                                          \
      parser_attribute_t<decltype(callback)> attr;                             \
      auto pres = parser(i, last, attr);                                       \
      if (pres.code <= ec::trailing_character)                                 \
        callback(attr);                                                        \
      if (pres.code != ec::trailing_character)                                 \
        return pres;                                                           \
      i = pres.last;                                                           \
    }                                                                          \
    goto s_##target;                                                           \
  }

#define failure(condition, error_code)                                         \
  if (condition) {                                                             \
    result.code = error_code;                                                  \
    goto s_return;                                                             \
  }

#define epsilon(target) goto e_##target;

enum class ec : uint8_t {
  /// Not-an-error.
  success,
  /// Parser succeeded but found trailing character(s).
  trailing_character,
  /// Parser stopped after reaching the end while still expecting input.
  unexpected_eof,
  /// Parser stopped after reading an unexpected character.
  unexpected_character,
  /// Cannot construct a negative caf::duration.
  negative_duration,
  /// Cannot construct a caf::duration with a value exceeding uint32_t.
  duration_overflow,
  /// Too many characters for an atom.
  too_many_characters,
  /// Unrecognized character after escaping `\`.
  illegal_escape_sequence,
};

std::string to_string(ec x) {
  static constexpr const char* ec_names[] = {
    "success",
    "trailing_character",
    "unexpected_eof",
    "unexpected_character",
    "negative_duration",
    "duration_overflow",
    "too_many_characters",
    "illegal_escape_sequence",
  };
  return ec_names[static_cast<int>(x)];
}
template <class... Ts>
error make_error(ec code, Ts&&... xs) {
  return {static_cast<uint8_t>(code), atom("parser"),
          make_message(std::forward<Ts>(xs)...)};
}

/// A `string_view`-ish abstraction for a range of characters.
// TODO: replace with `std::string_view` when switching to C++17
class char_range : detail::comparable<char_range>,
                   detail::comparable<char_range, std::string> {
public:
  using iterator = const char*;

  explicit char_range(const std::string& x)
      : begin_(x.c_str()),
        end_(begin_ + x.size()) {
    // nop
  }

  template <size_t N>
  char_range(const char (&xs)[N]) : begin_(xs), end_(begin_ + N) {
    if (xs[N - 1] == '\0')
      --end_;
  }

  char_range(iterator first, iterator last) : begin_(first), end_(last) {
    // nop
  }

  char_range(const char_range&) = default;

  char_range& operator=(const char_range&) = default;

  char_range& operator=(const std::string& x) {
    begin_ = x.c_str();
    end_ = begin_ + x.size();
    return *this;
  }

  template <size_t N>
  char_range& operator=(char (&xs)[N]) {
    begin_ = xs;
    end_ = begin_ + N;
    return *this;
  }

  iterator begin() const {
    return begin_;
  }

  iterator end() const {
    return end_;
  }

  size_t size() const {
    return static_cast<size_t>(std::distance(begin_, end_));
  }

  bool empty() const {
    return begin_ == end_;
  }

  int compare(char_range x) const {
    if (size() == x.size())
      return strncmp(begin(), x.begin(), size());
    // `this < x` if `this` is a prefix of `x`.
    if (size() < x.size()) {
      auto res = strncmp(begin(), x.begin(), size());
      return res == 0 ? -1 : res;
    }
    // `this > x` if `x` is a prefix of `this`.
    auto res = strncmp(begin(), x.begin(), size());
    return res == 0 ? 1 : res;
  }

  int compare(const std::string& x) const {
    char_range tmp{x};
    return compare(tmp);
  }

  std::string to_string() const {
    return {begin_, end_};
  }

private:
  iterator begin_;
  iterator end_;
};

template <class Iterator>
struct parser_result {
  /// Returned status code.
  ec code;
  /// Halt position.
  Iterator last;
};

template <class F>
struct parser_attribute;

template <class T>
struct parser_attribute<void (T&)> {
  using type = T;
};

template <class T>
struct parser_attribute<void (T)> {
  using type = T;
};

template <class F>
using parser_attribute_t = typename parser_attribute<
  typename detail::get_callable_trait<F>::fun_sig>::type;

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_integer(Iterator i, Sentinel last, int64_t& x) {
  // Utility functions.
  auto hexval = [](char c) -> int64_t {
    return c >= '0' && c <= '9' ?
             c - '0' :
             (c >= 'A' && c <= 'F' ? c - 'A' : c - 'a') + 10;
  };
  auto bin_digit = [](char c) {
    return c == '0' || c == '1';
  };
  auto oct_digit = [](char c) {
    return c >= '0' && c <= '7';
  };
  auto dec_digit = [](char c) {
    return c >= '0' && c <= '9';
  };
  auto hex_digit = [](char c) {
    return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')
           || (c >= 'A' && c <= 'F');
  };
  // Parser FSM.
  start();
  state(init) {
    input(*i == '-', start_neg)
    action(*i == '0', pos_zero, x = 0)
    action(dec_digit(*i), pos_dec, x = *i - '0')
  }
  term_state(pos_zero) {
    input(*i == 'b' || *i == 'B', start_pos_bin)
    input(*i == 'x' || *i == 'X', start_pos_hex)
    action(oct_digit(*i), pos_oct, x = *i - '0')
  }
  state(start_neg) {
    action(*i == '0', neg_zero, x = 0)
    action(dec_digit(*i), neg_dec, x = -(*i - '0'))
  }
  term_state(neg_zero) {
    input(*i == 'b' || *i == 'B', start_neg_bin)
    input(*i == 'x' || *i == 'X', start_neg_hex)
    action(oct_digit(*i), neg_oct, x = -(*i - '0'))
  }
  state(start_pos_bin) {
    epsilon(pos_bin)
  }
  term_state(pos_bin) {
    action(bin_digit(*i), pos_bin, x = (x * 2) + (*i - '0'))
  }
  term_state(pos_oct) {
    action(oct_digit(*i), pos_oct, x = (x * 8) + (*i - '0'))
  }
  term_state(pos_dec) {
    action(dec_digit(*i), pos_dec, x = (x * 10) + (*i - '0'))
  }
  state(start_pos_hex) {
    action(hex_digit(*i), pos_hex, x = (x * 16) + hexval(*i))
  }
  term_state(pos_hex) {
    action(hex_digit(*i), pos_hex, x = (x * 16) + hexval(*i))
  }
  state(start_neg_bin) {
    action(bin_digit(*i), neg_bin, x = (x * 2) - (*i - '0'))
  }
  term_state(neg_bin) {
    action(bin_digit(*i), neg_bin, x = (x * 2) - (*i - '0'))
  }
  term_state(neg_oct) {
    action(oct_digit(*i), neg_oct, x = (x * 8) - (*i - '0'))
  }
  term_state(neg_dec) {
    action(dec_digit(*i), neg_dec, x = (x * 10) - (*i - '0'))
  }
  state(start_neg_hex) {
    action(hex_digit(*i), neg_hex, x = (x * 16) - (hexval(*i)))
  }
  term_state(neg_hex) {
    action(hex_digit(*i), neg_hex, x = (x * 16) - (hexval(*i)))
  }
  fin();
}

template <class T>
struct opt_visit {
  optional<T> operator()(T x) const {
    return x;
  }
  template <class U>
  optional<T> operator()(U) const {
    return none;
  }
};

timespan make_timespan(int64_t x, time_unit y) {
  switch (y) {
    default:
      return timespan{0};
    case time_unit::nanoseconds:
      return timespan{x};
    case time_unit::microseconds:
      return timespan{x * 1000};
    case time_unit::milliseconds:
      return timespan{x * 1000000};
    case time_unit::seconds:
      return timespan{x * 1000000000};
    case time_unit::minutes:
      return timespan{x * 60000000000};
  }
}

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_time_unit(Iterator i, Sentinel last,
                                        time_unit& x) {
  // Parser FSM.
  start();
  state(init) {
    input(*i == 'u', have_u)
    input(*i == 'n', have_n)
    input(*i == 'm', have_m)
    action(*i == 's', done, x = time_unit::seconds)
  }
  state(have_u) {
    action(*i == 's', done, x = time_unit::microseconds)
  }
  state(have_n) {
    action(*i == 's', done, x = time_unit::nanoseconds)
  }
  state(have_m) {
    input(*i == 'i', have_mi)
    action(*i == 's', done, x = time_unit::milliseconds)
  }
  state(have_mi) {
    action(*i == 'n', done, x = time_unit::minutes)
  }
  term_state(done) {
    // nop
  }
  fin();
}

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_double(Iterator i, Sentinel last, double& x) {
  // We cannot assume [first, last) is null-terminated and from_chars is a
  // C++17 feature.
  std::string tmp{i, last};
  auto j = tmp.c_str();
  char* e;
  parser_result<Iterator> result;
  // TODO: this sucks; use from_chars after switching to C++17
  x = strtod(j, &e);
  result.last = i + std::distance(j, const_cast<const char*>(e));
  if (j == e)
    result.code = ec::unexpected_character;
  else
    result.code = (*e == '\0') ? ec::success : ec::trailing_character;
  return result;
}

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_atom(Iterator i, Sentinel last, atom_value& x) {
  size_t pos = 0;
  char buf[11];
  memset(buf, 0, sizeof(buf));
  auto legal = [](char c) {
    return isalnum(c) || c == '_' || c == ' ';
  };
  start();
  state(init) {
    input(*i == '\'', read_chars)
  }
  state(read_chars) {
    action(*i == '\'', done, x = atom(buf))
    failure(pos >= sizeof(buf) - 1, ec::too_many_characters)
    action(legal(*i), read_chars, buf[pos++] = *i)
  }
  term_state(done) {
    // nop
  }
  fin();
}

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_bool(Iterator i, Sentinel last, bool& x) {
  start();
  state(init) {
    input(*i == 'f', has_f)
    input(*i == 't', has_t)
  }
  state(has_f) {
    input(*i == 'a', has_fa)
  }
  state(has_fa) {
    input(*i == 'l', has_fal)
  }
  state(has_fal) {
    input(*i == 's', has_fals)
  }
  state(has_fals) {
    action(*i == 'e', done, x = false)
  }
  state(has_t) {
    input(*i == 'r', has_tr)
  }
  state(has_tr) {
    input(*i == 'u', has_tru)
  }
  state(has_tru) {
    action(*i == 'e', done, x = true)
  }
  term_state(done) {
    // nop
  }
  fin();
}

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_string(Iterator i, Sentinel last, std::string& x) {
  start();
  state(init) {
    input(*i == '"', read_chars)
  }
  state(read_chars) {
    input(*i == '\\', escape)
    input(*i == '"', done)
    action(true, read_chars, x += *i)
  }
  state(escape) {
    action(*i == 'n', read_chars, x += '\n')
    action(*i == 'r', read_chars, x += '\r')
    action(*i == '\\', read_chars, x += '\\')
    action(*i == '"', read_chars, x += '"')
    input(*i == '\n', read_chars);
    failure(true, ec::illegal_escape_sequence)
  }
  term_state(done) {
    // nop
  }
  fin();
}

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_number_or_timespan(Iterator i, Sentinel last, config_value& x) {
  if (i == last)
    return {ec::unexpected_eof, i};
  // Try integer parser first.
  int64_t tmp;
  auto res = parse_integer(i, last, tmp);
  // Disambiguate integer with trailing characters.
  if (res.code == ec::trailing_character) {
    // Try whether we can continue parsing a timespan.
    time_unit tu;
    auto tu_res = parse_time_unit(res.last, last, tu);
    if (tu_res.last > res.last) {
      if (tu_res.code <= ec::trailing_character)
        x = make_timespan(tmp, tu);
      return tu_res;
    }
    // Try whether we read the first part of a double.
    switch (*res.last) {
      case '.':
      case 'e':
      case 'E': {
        double d;
        auto d_res = parse_double(i, last, d);
        if (d_res.code <= ec::trailing_character)
          x = d;
        return d_res;
      }
      default:
        break;
    }
    // No disambiguation succeeds, return original integer.
    x = i;
    return res;
  }
  // Set integer on success and return result.
  if (res.code == ec::success)
    x = i;
  // Floating point literals starting with '.' (as in '.132') are the only
  // literal type that produces a straight error in the integer parser.
  else if (res.code == ec::unexpected_character) {
    if (res.last == i && *i == '.') {
      double d;
      auto d_res = parse_double(i, last, d);
      if (d_res.code <= ec::trailing_character)
        x = d;
      return d_res;
    }
  }
  return res;
}

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_config_value(Iterator i, Sentinel last,
                                           config_value& x) {
  // Try reading integer/double/timespan.
  auto res = parse_number_or_timespan(i, last, x);
  if (res.code <= ec::trailing_character)
    return res;
  // Try reading an atom.
  atom_value x1;
  auto x1_res = parse_atom(i, last, x1);
  if (x1_res.code <= ec::trailing_character) {
    x = x1;
    return x1_res;
  }
  // Try reading a bool.
  bool x2;
  auto x2_res = parse_bool(i, last, x2);
  if (x2_res.code <= ec::trailing_character) {
    x = x2;
    return x2_res;
  }
  // Try reading a string.
  std::string x3;
  auto x3_res = parse_string(i, last, x3);
  if (x3_res.code <= ec::trailing_character) {
    x = x3;
    return x3_res;
  }
  // In case non parser produced a value: return the error of whichever parser
  // consumed the most input.
  auto cmp = [&](const parser_result<Iterator>& x,
                 const parser_result<Iterator>& y) {
    return std::distance(i, x.last) < std::distance(i, y.last);
  };
  parser_result<Iterator> results[] = {res, x1_res, x2_res, x3_res};
  auto j = std::max_element(std::begin(results), std::end(results), cmp);
  return *j;
}

using res_t = std::tuple<config_value, ec, ptrdiff_t>;

template <class Iterator, class Sentinel, class T>
std::function<res_t(const std::string& x)>
make_parser(parser_result<Iterator> (*f)(Iterator i, Sentinel last, T&)) {
  return [f](const std::string& x) {
    T val;
    char_range cr{x};
    auto y = f(cr.begin(), cr.end(), val);
    //auto val = holds_alternative<T>(y.value) ? get<T>(y.value) : T{};
    return res_t{std::move(val), y.code, std::distance(x.c_str(), y.last)};
  };
}

res_t res(int x, ec y, ptrdiff_t z) {
  return {config_value{static_cast<int64_t>(x)}, y, z};
}

template <class T>
res_t res(T x, ec y, ptrdiff_t z) {
  return {config_value{x}, y, z};
}

CAF_TEST(integers) {
  auto parse = make_parser(parse_integer<char_range::iterator>);
  CAF_CHECK_EQUAL(parse("0"), res(0, ec::success, 1));
  CAF_CHECK_EQUAL(parse("1"), res(1, ec::success, 1));
  CAF_CHECK_EQUAL(parse("00"), res(0, ec::success, 2));
  CAF_CHECK_EQUAL(parse("10"), res(10, ec::success, 2));
  CAF_CHECK_EQUAL(parse("101"), res(101, ec::success, 3));
  CAF_CHECK_EQUAL(parse("0101"), res(65, ec::success, 4));
  CAF_CHECK_EQUAL(parse("0b101"), res(5, ec::success, 5));
  CAF_CHECK_EQUAL(parse("0B101"), res(5, ec::success, 5));
  CAF_CHECK_EQUAL(parse("0x101"), res(257, ec::success, 5));
  CAF_CHECK_EQUAL(parse("0X101"), res(257, ec::success, 5));
  CAF_CHECK_EQUAL(parse("-0"), res(0, ec::success, 2));
  CAF_CHECK_EQUAL(parse("-1"), res(-1, ec::success, 2));
  CAF_CHECK_EQUAL(parse("-00"), res(0, ec::success, 3));
  CAF_CHECK_EQUAL(parse("-10"), res(-10, ec::success, 3));
  CAF_CHECK_EQUAL(parse("-101"), res(-101, ec::success, 4));
  CAF_CHECK_EQUAL(parse("-0101"), res(-65, ec::success, 5));
  CAF_CHECK_EQUAL(parse("-0b101"), res(-5, ec::success, 6));
  CAF_CHECK_EQUAL(parse("-0B101"), res(-5, ec::success, 6));
  CAF_CHECK_EQUAL(parse("-0x101"), res(-257, ec::success, 6));
  CAF_CHECK_EQUAL(parse("-0X101"), res(-257, ec::success, 6));
  CAF_CHECK_EQUAL(parse("0s"), res(0, ec::trailing_character, 1));
  CAF_CHECK_EQUAL(parse("0b"), res(0, ec::unexpected_eof, 2));
  CAF_CHECK_EQUAL(parse("0B"), res(0, ec::unexpected_eof, 2));
  CAF_CHECK_EQUAL(parse("0x"), res(0, ec::unexpected_eof, 2));
  CAF_CHECK_EQUAL(parse("0X"), res(0, ec::unexpected_eof, 2));
  CAF_CHECK_EQUAL(parse("0Xz"), res(0, ec::unexpected_character, 2));
}

constexpr timespan operator"" _min(unsigned long long x) {
  return timespan{x * 60000000000};
}

constexpr timespan operator"" _s(unsigned long long x) {
  return timespan{x * 1000000000};
}
constexpr timespan operator"" _ms(unsigned long long x) {
  return timespan{x * 1000000};
}

constexpr timespan operator"" _us(unsigned long long x) {
  return timespan{x * 1000};
}

constexpr timespan operator"" _ns(unsigned long long x) {
  return timespan{x};
}

CAF_TEST(timespans) {
  auto parse = make_parser(parse_number_or_timespan<char_range::iterator>);
  CAF_CHECK_EQUAL(parse("0"), res(0, ec::success, 1));
  CAF_CHECK_EQUAL(parse("10"), res(10, ec::success, 2));
  CAF_CHECK_EQUAL(parse("-10"), res(-10, ec::success, 3));
  CAF_CHECK_EQUAL(parse("0min"), res(0_min, ec::success, 4));
  CAF_CHECK_EQUAL(parse("0ss"), res(0_s, ec::trailing_character, 2));
  CAF_CHECK_EQUAL(parse("0s"), res(0_s, ec::success, 2));
  CAF_CHECK_EQUAL(parse("0ms"), res(0_ms, ec::success, 3));
  CAF_CHECK_EQUAL(parse("0us"), res(0_us, ec::success, 3));
  CAF_CHECK_EQUAL(parse("0ns"), res(0_ns, ec::success, 3));
  CAF_CHECK_EQUAL(parse("1337min"), res(1337_min, ec::success, 7));
  CAF_CHECK_EQUAL(parse("1337s"), res(1337_s, ec::success, 5));
  CAF_CHECK_EQUAL(parse("1337ms"), res(1337_ms, ec::success, 6));
  CAF_CHECK_EQUAL(parse("1337us"), res(1337_us, ec::success, 6));
  CAF_CHECK_EQUAL(parse("1337ns"), res(1337_ns, ec::success, 6));
  CAF_CHECK_EQUAL(parse("-1min"), res(-1_min, ec::success, 5));
  CAF_CHECK_EQUAL(parse("-1s"), res(-1_s, ec::success, 3));
  CAF_CHECK_EQUAL(parse("-1ms"), res(-1_ms, ec::success, 4));
  CAF_CHECK_EQUAL(parse("-1us"), res(-1_us, ec::success, 4));
  CAF_CHECK_EQUAL(parse("-1ns"), res(-1_ns, ec::success, 4));
  CAF_CHECK_EQUAL(parse("0."), res(0.0, ec::success, 2));
  CAF_CHECK_EQUAL(parse(".0"), res(0.0, ec::success, 2));
  CAF_CHECK_EQUAL(parse("10e3"), res(10e3, ec::success, 4));
}

CAF_TEST(doubles) {
  auto parse = make_parser(parse_double<char_range::iterator>);
  CAF_CHECK_EQUAL(parse("0"), res(0.0, ec::success, 1));
  CAF_CHECK_EQUAL(parse("1.2"), res(1.2, ec::success, 3));
}

CAF_TEST(atoms) {
  auto parse = make_parser(parse_atom<char_range::iterator>);
  auto nil = atom("");
  CAF_CHECK_EQUAL(parse("''"), res(nil, ec::success, 2));
  CAF_CHECK_EQUAL(parse("'abc'"), res(atom("abc"), ec::success, 5));
  CAF_CHECK_EQUAL(parse("'0123456789'"),
                  res(atom("0123456789"), ec::success, 12));
  CAF_CHECK_EQUAL(parse("'01234567891'"),
                  res(nil, ec::too_many_characters, 11));
  CAF_CHECK_EQUAL(parse("'012345678912'"),
                  res(nil, ec::too_many_characters, 11));
  CAF_CHECK_EQUAL(parse("'a#'"), res(nil, ec::unexpected_character, 2));
  CAF_CHECK_EQUAL(parse("'A B'"), res(atom("A B"), ec::success, 5));
}

CAF_TEST(bools) {
  auto parse = make_parser(parse_bool<char_range::iterator>);
  CAF_CHECK_EQUAL(parse("true"), res(true, ec::success, 4));
  CAF_CHECK_EQUAL(parse("false"), res(false, ec::success, 5));
  CAF_CHECK_EQUAL(parse("trues"), res(true, ec::trailing_character, 4));
  CAF_CHECK_EQUAL(parse("falses"), res(false, ec::trailing_character, 5));
}

CAF_TEST(mixed) {
  auto parse = make_parser(parse_config_value<char_range::iterator>);
  CAF_CHECK_EQUAL(parse("true"), res(true, ec::success, 4));
  CAF_CHECK_EQUAL(parse("false"), res(false, ec::success, 5));
  CAF_CHECK_EQUAL(parse("10"), res(10, ec::success, 2));
  CAF_CHECK_EQUAL(parse("1.0"), res(1.0, ec::success, 3));
  CAF_CHECK_EQUAL(parse("20ns"), res(20_ns, ec::success, 4));
  CAF_CHECK_EQUAL(parse("'hello'"), res(atom("hello"), ec::success, 7));
  CAF_CHECK_EQUAL(parse("\"foo\""), res("foo", ec::success, 5));
  // The bool parser stops after 'f', all other parsers immediately.
  CAF_CHECK_EQUAL(parse("foo"), res(0, ec::unexpected_character, 1));
  CAF_CHECK_EQUAL(parse("\"foo"), res(0, ec::unexpected_eof, 4));
}

struct config_consumer {
  virtual ~config_consumer() {
    // nop
  }
  /// Starts parsing a map, i.e., expects the producer to call `add_key` next.
  virtual void map_begin(char_range name) = 0;
  virtual void map_end() = 0;
  virtual void list_begin(char_range name) = 0;
  virtual void list_end() = 0;
  /// Inserts into the map `name` of the current scope.
  virtual void map_insert(char_range name) = 0;
  /// Inserts into a list in the current scope. Alters the meaning of the next
  /// call to `add_key` by interpreting the given name as the name of the list.
  virtual void list_append() = 0;
  virtual void add_key(char_range name) = 0;
  virtual void add_value(config_value&& x) = 0;
};

template <class Iterator, class Sentinel = Iterator>
parser_result<Iterator> parse_ini_line(Iterator i, Sentinel last,
                                       config_consumer& x) {
  auto legal_first_char = [](char c) -> bool {
    return isalpha(c);
  };
  auto legal_char = [](char c) -> bool {
    return isalpha(c) || isdigit(c) || c == '_' || c == '-';
  };
  auto space_or_tab = [](char c) -> bool {
    return c == ' ' || c == '\t';
  };
  auto config_value_cb = [&](config_value& y) {
    x.add_value(std::move(y));
  };
  // TODO: fuse into a single generic lambda when switching to C++14
  auto atom_cb = [&](atom_value y) {
    config_value tmp{y};
    config_value_cb(tmp);
  };
  auto string_cb = [&](std::string& y) {
    config_value tmp{std::move(y)};
    config_value_cb(tmp);
  };
  auto double_cb = [&](double y) {
    config_value tmp{y};
    config_value_cb(tmp);
  };
  /// Iterators for storing identifier names.
  char_range::iterator id_begin = i;
  char_range::iterator id_end = i;
  // FSM implementation.
  start();
  term_state(init) { // init is terminal because empty lines are allowed
    input(space_or_tab(*i), init)
    input(*i == '[', start_read_section_name)
    action(legal_first_char(*i), read_key, id_begin = i)
  }
  state(start_read_section_name) {
    input(space_or_tab(*i), start_read_section_name)
    action(legal_first_char(*i), read_section_name, id_begin = i)
  }
  state(read_section_name) {
    input(isalnum(*i), read_section_name)
    action(*i == ']', done, x.map_begin({id_begin, i}))
    action(space_or_tab(*i), after_section_name, id_end = i)
  }
  state(after_section_name) {
    input(space_or_tab(*i), after_section_name)
    action(*i == ']', done, x.map_begin({id_begin, id_end}))
  }
  state(read_key) {
    input(legal_char(*i), read_section_name)
    action(*i == '[', start_read_map_key, id_end = i)
    action(space_or_tab(*i), await_assign, id_end = i)
    action(*i == '=', start_read_value, x.add_key({id_begin, i}))
  }
  state(start_read_map_key) {
    action(*i == ']', await_assign, x.list_append())
    action(legal_first_char(*i), read_map_key,
           x.map_insert({id_begin, id_end}); id_begin = i)
  }
  state(read_map_key) {
    input(legal_char(*i), read_map_key)
    action(*i == ']', await_assign, id_end = i)
  }
  state(await_assign) {
    action(*i == '=', start_read_value, x.add_key({id_begin, id_end}))
    input(space_or_tab(*i), await_assign)
  }
  state(start_read_value) {
    input(space_or_tab(*i), start_read_value)
    invoke_parser(*i == '\'', done, parse_atom, atom_cb)
    invoke_parser(*i == '"', done, parse_string, string_cb)
    invoke_parser(isdigit(*i), done, parse_number_or_timespan, config_value_cb)
    invoke_parser(*i == '.', done, parse_double, double_cb)
  }
  term_state(drop_comment) {
    input(true, drop_comment)
  }
  term_state(done) {
    input(space_or_tab(*i), done)
    input(*i == ';', drop_comment)
  }
  fin();
}

struct actual_config_consumer : config_consumer {
  enum mode_t {
    build_map,
    build_list,
    extend_list
  };
  mode_t mode;
  using inner_map = std::map<std::string, config_value>;
  std::map<std::string, inner_map> data;
  inner_map* scope;
  std::string current_key;
  actual_config_consumer() : scope(nullptr) {
    // Create implicit [global] scope.
    map_begin("global");
  }

  void map_begin(char_range name) override {
    auto i = data.emplace(name.to_string(), inner_map{}).first;
    scope = &(i->second);
  }

  void map_end() override {
    scope = nullptr;
  }

  void map_insert(char_range) override {
    throw std::runtime_error("implement me");
  }

  void list_begin(char_range) override {
    throw std::runtime_error("implement me");
  }

  void list_end() override {
    throw std::runtime_error("implement me");
  }

  void list_append() override {
    mode = extend_list;
  }

  void add_key(char_range name) override {
    current_key.assign(name.begin(), name.end());
  }

  void add_value(config_value&& x) override {
    auto i = scope->find(current_key);
    if (mode == extend_list) {
      if (i == scope->end()) {
        x.convert_to_list();
        scope->emplace(current_key, std::move(x));
      } else {
        i->second.append(std::move(x));
      }
      mode = build_map;
    }
    else if (mode == build_map) {
      if (i == scope->end()) {
        scope->emplace(current_key, std::move(x));
      } else {
        i->second = std::move(x);
      }
    }
  }
};

struct test_config_consumer : actual_config_consumer {
  using super = actual_config_consumer;
  std::vector<std::string> log;
  void map_begin(char_range name) override {
    log.emplace_back("map_begin: ");
    log.back().append(name.begin(), name.end());
    super::map_begin(name);
  }
  void map_end() override {
    log.emplace_back("map_end");
    super::map_end();
  }
  void map_insert(char_range name) override {
    log.emplace_back("map_insert_begin: ");
    log.back().append(name.begin(), name.end());
    super::map_insert(name);
  }
  void list_begin(char_range name) override {
    log.emplace_back("list_begin: ");
    log.back().append(name.begin(), name.end());
    super::list_begin(name);
  }
  void list_end() override {
    log.emplace_back("list_end");
    super::list_end();
  }
  void list_append() override {
    log.emplace_back("list_append");
    super::list_append();
  }
  void add_key(char_range name) override {
    log.emplace_back("add_key: ");
    log.back().append(name.begin(), name.end());
    super::add_key(name);
  }
  void add_value(config_value&& x) override {
    log.emplace_back("add_value: ");
    log.back().append(to_string(x));
    super::add_value(std::move(x));
  }
};

CAF_TEST(ini_lines) {
  auto ini_res = [](std::vector<std::string> xs, ec code, ptrdiff_t pos) {
    return std::make_tuple(xs, code, pos);
  };
  auto parse = [&](char_range str) {
    test_config_consumer f;
    auto res = parse_ini_line(str.begin(), str.end(), f);
    printf("f content: %s\n", deep_to_string(f.data).c_str());
    return std::make_tuple(std::move(f.log), res.code,
                           std::distance(str.begin(), res.last));
  };
  CAF_CHECK_EQUAL(parse("[abc]"), ini_res({"map_begin: abc"}, ec::success, 5));
  CAF_CHECK_EQUAL(parse("[ abc]"), ini_res({"map_begin: abc"}, ec::success, 6));
  CAF_CHECK_EQUAL(parse("[abc ]"), ini_res({"map_begin: abc"}, ec::success, 6));
  CAF_CHECK_EQUAL(parse("[ abc ]"),
                  ini_res({"map_begin: abc"}, ec::success, 7));
  CAF_CHECK_EQUAL(parse(" [ abc ]"),
                  ini_res({"map_begin: abc"}, ec::success, 8));
  CAF_CHECK_EQUAL(parse(" [ abc ] "),
                  ini_res({"map_begin: abc"}, ec::success, 9));
  CAF_CHECK_EQUAL(parse(" [ a bc ] "),
                  ini_res({}, ec::unexpected_character, 5));
  CAF_CHECK_EQUAL(parse("[abc"), ini_res({}, ec::unexpected_eof, 4));
  CAF_CHECK_EQUAL(parse("a=1"),
                  ini_res({"add_key: a", "add_value: 1"}, ec::success, 3));
  CAF_CHECK_EQUAL(parse("a =1"),
                  ini_res({"add_key: a", "add_value: 1"}, ec::success, 4));
  CAF_CHECK_EQUAL(parse("a = 1"),
                  ini_res({"add_key: a", "add_value: 1"}, ec::success, 5));
  CAF_CHECK_EQUAL(parse(" a = 1"),
                  ini_res({"add_key: a", "add_value: 1"}, ec::success, 6));
  CAF_CHECK_EQUAL(parse(" a = 1 "),
                  ini_res({"add_key: a", "add_value: 1"}, ec::success, 7));
  CAF_CHECK_EQUAL(parse("a=1;foo"),
                  ini_res({"add_key: a", "add_value: 1"}, ec::success, 7));
  CAF_CHECK_EQUAL(parse("a=1 ;foo"),
                  ini_res({"add_key: a", "add_value: 1"}, ec::success, 8));
  CAF_CHECK_EQUAL(parse("a[]=1"),
                  ini_res({"list_append", "add_key: a", "add_value: 1"},
                          ec::success, 5));
  CAF_CHECK_EQUAL(parse("a=1.0"),
                  ini_res({"add_key: a", "add_value: " + std::to_string(1.0)},
                          ec::success, 5));
  CAF_CHECK_EQUAL(parse("a=1s"),
                  ini_res({"add_key: a", "add_value: 1000000000ns"},
                          ec::success, 4));
  CAF_CHECK_EQUAL(parse("a=.1"),
                  ini_res({"add_key: a", "add_value: " + std::to_string(.1)},
                          ec::success, 4));
  CAF_CHECK_EQUAL(parse("a='abc'"),
                  ini_res({"add_key: a", "add_value: 'abc'"}, ec::success, 7));
  CAF_CHECK_EQUAL(parse("a=\"dc\""),
                  ini_res({"add_key: a", "add_value: \"dc\""}, ec::success, 6));
}

