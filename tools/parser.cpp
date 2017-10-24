#include <cstdlib>
#include <cstring>

#include <stack>
#include <string>
#include <vector>
#include <iostream>

#include "caf/message.hpp"
#include "caf/optional.hpp"
#include "caf/expected.hpp"
#include "caf/config_value.hpp"
#include "caf/make_message.hpp"

#include "caf/test/unit_test.hpp"
#include "caf/test/unit_test_impl.hpp"

using namespace std;
using namespace caf;

namespace parser {

class store {
public:
  virtual ~store() {
    // nop
  }

  /// Returns the content of the variable `var`.
  virtual std::string get(const std::string& var) const = 0;

  /// Returns the content of the variable `var` at index `idx`.
  virtual std::string get(const std::string& var,
                          const std::string& idx) const = 0;
};

/// Lists all valid characters for binary digits.
const char* bin_digit = "01";

/// Lists all valid characters for octal digits.
const char* oct_digit = "01234567";

/// Lists all valid characters for decimal digits.
const char* dec_digit = "0123456789";

/// Lists all valid characters for hexadecimal digits.
const char* hex_digit = "0123456789ABCDEFabcdef";

/// Lists all valid characters for letters and numerals.
const char* alphanumeric = "0123456789"
                           "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                           "abcdefghijklmnopqrstuvwxyz";

using iterator = std::string::const_iterator;

// Error codes for parser failures.
enum class ec : uint8_t {
  /// Parsing succeeded.
  none,
  /// Parsing stopped at an invalid input.
  unexpected_character,
  /// Parsing stopped because no input was provided.
  empty_string,
  /// Parsing a duration failed because no number was provided.
  missing_number,
  /// Parsing a duration failed because the number has no suffix.
  missing_suffix,
  /// Parsing a duration failed because the suffix is incomplete.
  incomplete_suffix,
  /// Parsing a duration failed because the number is negative.
  negative_duration,
  /// Parsing a duration failed because the number exceeds an uint32.
  duration_overflow,
  /// Parsing a variable failed because no name was provided.
  empty_variable_name,
  /// Parsing an index failed because no name was provided.
  empty_variable_index,
  /// Parsing an escaped sequence failed because of invalid input.
  invalid_escape_sequence,
};

const char* ec_names[] = {
  "none",
  "unexpected_character",
  "empty_string",
  "missing_number",
  "missing_suffix",
  "incomplete_suffix",
  "negative_duration",
  "duration_overflow",
  "empty_variable_name",
  "empty_variable_index",
  "invalid_escape_sequence",
};

std::string to_string(ec x) {
  return ec_names[static_cast<int>(x)];
}

error make_error(ec x) {
  return {static_cast<uint8_t>(x), atom("parser")};
}

/// Points to the implementation of an action.
template <class State>
using action_ptr = void (*)(State&, char, const char*);

/// Stores an action along with a guarding condition.
template <class State>
struct transition {
  /// Guards the action. The condition is interpreted as follows:
  /// - `nullptr` accepts any input (wildcard) *except* end-of-input (`\0`)
  /// - the empty string accepts the end-of-input signal `\0`
  /// - non-empty strings accept any of the listed characters, e.g., "abc"
  ///   accepts 'a', 'b', and 'c'.
  const char* condition;

  /// Identifies the action `f`.
  const char* action_name;

  /// Points to the implementation of the target action.
  action_ptr<State> action;
};

#define CAF_DECL_FSM_ACTION(name)                                              \
  template <class T>                                                           \
  static void name(T& st, char c __attribute__((unused)),                      \
                   const char* last __attribute__((unused)))

#define CAF_FSM_ACTION(condition, name)                                        \
  transition<T> {                                                              \
    condition, #name, name<T>                                                  \
  }

#define CAF_FSM_TERM_ACTION()                                                  \
  transition<T> {                                                              \
    "", "terminal", terminal<T>                                                \
  }

template <class Storage>
void inputs(Storage &st, std::initializer_list<transition<Storage>> xs) {
  st.transitions.assign(xs);
}

template <class Storage>
void is_terminated(Storage& st) {
  return st.transitions.empty();
}

template <class T>
void terminal(T& st, char, const char*) {
  st.transitions.clear();
}

/// Hosts storage types for different parsers.
namespace storage {

template <class Derived>
struct base {
  /// A transition for this type.
  using transition_type = transition<Derived>;

  /// List of transitions.
  using transition_vec = std::vector<transition_type>;

  /// Signals errors to the user.
  ec error_code = ec::none;

  /// Stores the current state transitions.
  transition_vec transitions;

  /// Allows to combine parsers by defining fallbacks. For example, a suffix
  /// parser can provide a fallback for an integer parser. Once the integer
  /// parser stops at the unexpected character the suffix parser takes over.
  /// Only a single fallback is triggered whenever a parser terminates, i.e.,
  /// putting multiple fallbacks into the stack nests multiple layers of
  /// parsers. Note that the fallback has to check for the `'\0'` character,
  /// because all fallbacks are informed when reaching the end of the input.
  std::stack<action_ptr<Derived>, std::vector<action_ptr<Derived>>> fallback;
};

template <class Derived>
void reset_base(base<Derived>& st) {
  st.error_code = ec::none;
  st.transitions.clear();
}

/// State for parsing an integer number.
struct integer : base<integer> {
  bool has_value = false;
  int64_t value = 0;
  bool negative = false;
};

/// @relates integer
void reset(integer& st) {
  reset_base(st);
  st.has_value = false;
  st.value = 0;
  st.negative = false;
}

/// State for parsing a duration.
struct duration : base<duration> {
  bool has_value = false;
  int64_t value = 0;
  bool negative = false;
  time_unit suffix = time_unit::invalid;
};

/// @relates duration
void reset(duration& st) {
  reset_base(st);
  st.has_value = false;
  st.value = 0;
  st.negative = false;
  st.suffix = time_unit::invalid;
}

/// State for parsing a string.
struct string : base<string> {
  bool has_value = false;
  std::string value;
};

/// @relates string
void reset(string& st) {
  reset_base(st);
  st.has_value = false;
  st.value.clear();
}

struct line : base<line> {
  bool has_value = false;
  std::string value;
  std::string current_var;
  std::string current_idx;
  bool inside_string = false;
  store* kvs = nullptr;
};

/// @relates line
void reset(line& st) {
  reset_base(st);
  st.has_value = false;
  st.value.clear();
  st.current_var.clear();
  st.current_idx.clear();
  st.inside_string = false;
}

} // namespace state

class abstract_fsm {
public:
  virtual ~abstract_fsm() {
    // nop
  }

  virtual ec error_code() const = 0;

  virtual bool has_value() const = 0;

  virtual config_value value() const = 0;

  virtual const char* handle(char c, const char* last_action) = 0;
};

/// Tries to trigger a transition on `st` and returns the name or the taken
/// action or `nullptr` if no condition matches.
template <class State>
typename std::enable_if<!std::is_base_of<abstract_fsm, State>::value,
                        const char*>::type
event(State& st, char c, const char* last_action) {
  // Find an action in the current transition table.
  auto pred = [c](const transition<State>& x) {
    return c != '\0'
           ? x.condition == nullptr || strchr(x.condition, c) != nullptr
           : x.condition != nullptr && x.condition[0] == '\0';
  };
  auto e = st.transitions.end();
  auto i = std::find_if(st.transitions.begin(), e, pred);
  if (i != e) {
    auto x = *i;
    x.action(st, c, last_action);
    // Trigger all epsilon transitions to fallback parsers.
    if (c == '\0') {
      while (!st.fallback.empty()) {
        auto fallback = st.fallback.top();
        st.fallback.pop();
        fallback(st, '\0', x.action_name);
      }
    }
    return x.action_name;
  }
  st.error_code = ec::unexpected_character;
  // Try to recover via epsilon transition.
  if (!st.fallback.empty()) {
    auto fallback = st.fallback.top();
    st.fallback.pop();
    fallback(st, c, last_action);
    // The fallback action has no name.
    return last_action;
  }
  return nullptr;
}

const char* event(abstract_fsm& x, char c, const char* last_action) {
  return x.handle(c, last_action);
}

template <class T>
class fsm_base : public abstract_fsm {
public:
  ec error_code() const override {
    return st_.error_code;
  }

  bool has_value() const override {
    return st_.has_value;
  }

  config_value value() const override {
    return st_.value;
  }

  const char* handle(char c, const char* last_action) override {
    return event(st_, c, last_action);
  }

protected:
  T st_;
};

using parse_result = std::pair<iterator, const char*>;

/*
template <class Storage>
parse_result parse(Storage& st, iterator first, iterator last) {
  // Iterate the sequence `[first, last)`, aborting if the FSM stops.
  const char* last_action = "init";
  for (auto i = first; i != last; ++i) {
    auto x = event(st, *i, last_action);
    if (x != nullptr)
      last_action = x;
    if (st.error_code != ec::none) {
      // Propagate error up the chain to see if this is recoverable.
      while (!st.fallback.empty() && st.error_code != ec::none) {
        auto fallback = st.fallback.top();
        st.fallback.pop();
        fallback(st, *i, last_action);
      }
      if (st.error_code != ec::none)
        return {i, last_action};
    }
  }
  // Trigger the end-of-input event and return end iterator.
  last_action = event(st, '\0', last_action);
  while (!st.fallback.empty()) {
    auto fallback = st.fallback.top();
    st.fallback.pop();
    fallback(st, '\0', last_action);
  }
  return {last, last_action};
}
*/

template <class Storage>
parse_result parse(Storage& st, iterator first, iterator last) {
  // Iterate the sequence `[first, last)`, aborting if the FSM stops.
  const char* last_action = "init";
  for (auto i = first; i != last; ++i) {
    auto x = event(st, *i, last_action);
    if (x == nullptr)
      return {i, nullptr};
    last_action = x;
  }
  // Trigger the end-of-input event and return end iterator.
  return {last, event(st, '\0', last_action)};
}

/// Combines two FSMs by implementing a failover from the primary to the
/// secondary on error. Picks the output of the primary parser if both accept
/// the input.
class fsm_failover : public abstract_fsm {
public:
  enum liveness {
    both_alive,
    left_alive,
    right_alive,
    none_alive
  };

  fsm_failover(abstract_fsm& left, abstract_fsm& right)
      : lv_(both_alive),
        left_(left),
        right_(right) {
    // nop
  }

  ec error_code() const override {
    if (lv_ != none_alive)
      return ec::none;
    return left_.error_code();
  }

  bool has_value() const override {
    return lv_ == right_alive ? right_.has_value() : left_.has_value();
  }

  inline config_value native_value() const {
    return value();
  }

  config_value value() const override {
    return lv_ == right_alive ? right_.value() : left_.value();
  }

  const char* handle(char c, const char* last_action) override {
    switch (lv_) {
      case both_alive: {
        auto res = left_.handle(c, last_action);
        auto alt = right_.handle(c, last_action);
        if (res == nullptr) {
          if (alt == nullptr) {
            lv_ = none_alive;
            return nullptr;
          }
          lv_ = right_alive;
          return alt;
        }
        if (alt == nullptr)
          lv_ = left_alive;
        return res;
        break;
      }
      case left_alive: {
        auto res = left_.handle(c, last_action);
        if (res == nullptr)
          lv_ = none_alive;
        return res;
      }
      case right_alive: {
        auto res = right_.handle(c, last_action);
        if (res == nullptr)
          lv_ = none_alive;
        return res;
      }
      default:
        return nullptr;
    }
  }

  parse_result parse(iterator first, iterator last) {
    return parser::parse(*this, first, last);
  }

private:
  liveness lv_;
  abstract_fsm& left_;
  abstract_fsm& right_;
};
/// Common state that transitions into itself.
template <class T>
void no_op(T&, char, const char*) {
  // nop
}

/// Common state that aborts parsing with specified reason.
template <class T, ec Reason>
void fail(T& st, char, const char*) {
  st.error_code = Reason;
  st.transitions.clear();
}

// Hosts states for forming an integer-parsing FSM.
class integer : public fsm_base<storage::integer> {
public:
  // -- initialization ---------------------------------------------------------

  template <class T>
  static void init(T& st) {
    reset(st);
    inputs(st, {CAF_FSM_ACTION("-", read_minus),
                CAF_FSM_ACTION("0", read_zero),
                {dec_digit, "read_digit", start_dec<T>}});
  }

  template <class T>
  static void init_value(T& st, int64_t x) {
    st.has_value = true;
    st.value = x;
  }

  // -- branching --------------------------------------------------------------

  CAF_DECL_FSM_ACTION(read_minus) {
    st.negative = true;
    inputs(st, {CAF_FSM_ACTION("-", read_minus),
                CAF_FSM_ACTION("0", read_zero),
                {dec_digit, "read_digit", start_dec<T>}});
  }

  CAF_DECL_FSM_ACTION(read_zero) {
    inputs(st, {CAF_FSM_ACTION("bB", start_bin),
                CAF_FSM_ACTION("xX", start_hex),
                CAF_FSM_ACTION(oct_digit, start_oct),
                CAF_FSM_TERM_ACTION()});
  }

  // -- parsing with different bases ------------------------------------------

  CAF_DECL_FSM_ACTION(start_bin) {
    init_value(st, 0);
    inputs(st, {{bin_digit, "read_digit", read_bin}, CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(read_bin) {
    st.value = (st.value * 2) + (c - '0');
  }

  CAF_DECL_FSM_ACTION(start_oct) {
    init_value(st, c - '0');
    inputs(st, {{oct_digit, "read_digit", read_oct}, CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(read_oct) {
    st.value = (st.value * 8) + (c - '0');
  }

  CAF_DECL_FSM_ACTION(start_dec) {
    init_value(st, c - '0');
    inputs(st, {{dec_digit, "read_digit", read_dec}, CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(read_dec) {
    st.value = (st.value * 10) + (c - '0');
  }

  CAF_DECL_FSM_ACTION(start_hex) {
    init_value(st, 0);
    inputs(st, {{hex_digit, "read_digit", read_hex}, CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(read_hex) {
    auto hexval = c >= '0' && c <= '9'
                  ? c - '0'
                  : (c >= 'A' && c <= 'F' ? c - 'A' : c - 'a') + 10;
    st.value = (st.value * 16) + hexval;
  }

  // -- member functions -------------------------------------------------------

  inline int64_t native_value() const {
    return st_.negative ? -st_.value : st_.value;
  }

  config_value value() const override {
    return native_value();
  }

  inline parse_result parse(iterator first, iterator last) {
    init(st_);
    return parser::parse(st_, first, last);
  }
};

/// Checks for a valid input and then forwards to `strtod`.
class real : public fsm_base<storage::string> {
public:
  // -- initialization ---------------------------------------------------------

  template <class T>
  static void init(T& st) {
    reset(st);
    st.has_value = false;
    inputs(st, {CAF_FSM_ACTION("+-", read_sign),
                CAF_FSM_ACTION(dec_digit, start_pre_decimal),
                CAF_FSM_ACTION(".", read_decimal_point),
                CAF_FSM_ACTION("iI", read_inf),
                CAF_FSM_ACTION("nN", read_nan)});
  }

  // -- internal transitions ---------------------------------------------------

  CAF_DECL_FSM_ACTION(read) {
    st.value += c;
  }

  // -- sequences --------------------------------------------------------------

  CAF_DECL_FSM_ACTION(read_inf) {
    st.value += c;
    auto f = [](T& st0, char c0, const char*) {
      st0.value += c0;
      auto f0 = [](T& st1, char c1, const char*) {
        st1.value += c1;
        auto f1 = [](T& st2, char c2, const char*) {
          st2.value += c2;
          auto f2 = [](T& st3, char c3, const char*) {
            st3.value += c3;
            auto f3 = [](T& st4, char c4, const char*) {
              st4.value += c4;
              auto f4 = [](T& st5, char c5, const char*) {
                st5.value += c5;
                auto f5 = [](T& st6, char c6, const char*) {
                  st6.value += c6;
                  inputs(st6, {CAF_FSM_TERM_ACTION()});
                };
                inputs(st5, {{"yY", "read_inf", f5}});
              };
              inputs(st4, {{"tT", "read_inf", f4}});
            };
            inputs(st3, {{"iI", "read_inf", f3}});
          };
          inputs(st2, {{"nN", "read_inf", f2}});
        };
        inputs(st1, {{"iI", "read_inf", f1}, CAF_FSM_TERM_ACTION()});
      };
      inputs(st0, {{"fF", "read_inf", f0}});
    };
    inputs(st, {{"nN", "read_inf", f}});
  }

  CAF_DECL_FSM_ACTION(read_nan) {
    st.value += c;
    auto f = [](T& st0, char c0, const char*) {
      st0.value += c0;
      auto f0 = [](T& st1, char c1, const char*) {
        st1.value += c1;
        inputs(st1, {CAF_FSM_TERM_ACTION()});
      };
      inputs(st0, {{"nN", "read_nan", f0}});
    };
    inputs(st, {{"aA", "read_nan", f}});
  }

  // -- branching states -------------------------------------------------------

  CAF_DECL_FSM_ACTION(read_sign) {
    st.value += c;
    inputs(st, {CAF_FSM_ACTION(dec_digit, start_pre_decimal),
                CAF_FSM_ACTION(".", read_decimal_point),
                CAF_FSM_ACTION("eE", read_e),
                CAF_FSM_ACTION("iI", read_inf),
                CAF_FSM_ACTION("nN", read_nan)});
  }

  CAF_DECL_FSM_ACTION(start_pre_decimal) {
    st.value += c;
    st.has_value = true;
    inputs(st, {CAF_FSM_ACTION(dec_digit, read),
                CAF_FSM_ACTION(".", read_decimal_point),
                CAF_FSM_ACTION("eE", read_e),
                CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(read_decimal_point) {
    st.value += c;
    st.has_value = true;
    inputs(st, {CAF_FSM_ACTION(dec_digit, start_decimal),
                CAF_FSM_ACTION("eE", read_e),
                CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(start_decimal) {
    st.value += c;
    inputs(st, {CAF_FSM_ACTION(dec_digit, read),
                CAF_FSM_ACTION("eE", read_e),
                CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(read_e) {
    st.value += c;
    inputs(st, {CAF_FSM_ACTION("+-", read_exponent_sign),
                CAF_FSM_ACTION(dec_digit, read_exponent)});
  }

  CAF_DECL_FSM_ACTION(read_exponent_sign) {
    st.value += c;
    inputs(st, {CAF_FSM_ACTION(dec_digit, read_exponent)});
  }

  CAF_DECL_FSM_ACTION(read_exponent) {
    st.value += c;
    inputs(st, {CAF_FSM_ACTION(dec_digit, read),
                CAF_FSM_TERM_ACTION()});
  }

  // -- member functions -------------------------------------------------------

  inline double native_value() const {
    char* e;
    return strtod(st_.value.c_str(), &e);
  }

  config_value value() const override {
    return native_value();
  }

  parse_result parse(iterator first, iterator last) {
    init(st_);
    return parser::parse(st_, first, last);
  }
};

class duration : public fsm_base<storage::duration>{
public:
  // -- terminal states --------------------------------------------------------

  template <class T>
  static void init(T& st, bool reset_state = true) {
    if (reset_state)
      reset(st);
    inputs(st, {{"s", "set_suffix", set_suffix<T, time_unit::seconds>},
                CAF_FSM_ACTION("m", read_m),
                CAF_FSM_ACTION("u", read_u),
                CAF_FSM_ACTION("n", read_n)});
  }

  // -- terminal states --------------------------------------------------------

  template <class T, time_unit X>
  static void set_suffix(T& st, char, const char*) {
    st.suffix = X;
    inputs(st, {CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(set_incomplete) {
    st.error_code = ec::incomplete_suffix;
  }

  // -- branching states -------------------------------------------------------

  CAF_DECL_FSM_ACTION(read_m) {
    inputs(st, {CAF_FSM_ACTION("i", read_i),
                {"s", "set_suffix", set_suffix<T, time_unit::milliseconds>},
                CAF_FSM_ACTION("", set_incomplete)});
  }

  // -- states for parsing "min" suffix ----------------------------------------

  CAF_DECL_FSM_ACTION(read_i) {
    inputs(st, {{"n", "set_suffix", set_suffix<T, time_unit::minutes>},
                CAF_FSM_ACTION("", set_incomplete)});
  }

  // -- states for parsing "us" suffix -----------------------------------------

  CAF_DECL_FSM_ACTION(read_u) {
    inputs(st, {{"s", "set_suffix", set_suffix<T, time_unit::microseconds>}});
  }

  // -- states for parsing "ns" suffix -----------------------------------------

  CAF_DECL_FSM_ACTION(read_n) {
    inputs(st, {{"s", "set_suffix", set_suffix<T, time_unit::nanoseconds>}});
  }

  // -- transition from the integer parser -------------------------------------

  CAF_DECL_FSM_ACTION(handover) {
    if (c == '\0') {
      if (st.error_code == ec::none)
        st.error_code = ec::missing_suffix;
      return;
    }
    if (st.error_code != ec::unexpected_character) {
      // Do not recover from actual errors in the integer parser.
      return;
    }
    if (last != nullptr
        && (strcmp(last, "read_digit") == 0
            || strcmp(last, "read_zero") == 0)) {
      st.error_code = ec::none;
      init(st, false);
      event(st, c, last);
    } else {
      st.error_code = ec::missing_number;
    }
  }

  // -- member functions -------------------------------------------------------

  bool has_value() const override {
    return st_.has_value && st_.suffix != time_unit::invalid;
  }

  inline caf::duration native_value() const {
    return {st_.suffix, static_cast<uint32_t>(st_.value)};
  }

  config_value value() const override {
    return native_value();
  }

  inline parse_result parse(iterator first, iterator last) {
    // Use the integer parser to read the count.
    integer::init(st_);
    st_.fallback.push(handover<storage::duration>);
    return parser::parse(st_, first, last);
  }

  inline parse_result parse(const std::string& str) {
    return parse(str.begin(), str.end());
  }
};

/// Reads a string enclosed in double quotes.
class string : public fsm_base<storage::string> {
public:
  // -- initialization ---------------------------------------------------------

  template <class T>
  static void init(T& st) {
    reset(st);
    inputs(st, {CAF_FSM_ACTION(" ", no_op),
                CAF_FSM_ACTION("\"", start_reading)});
  }

  // -- actions ----------------------------------------------------------------

  CAF_DECL_FSM_ACTION(start_reading) {
    st.has_value = true;
    inputs(st, {CAF_FSM_ACTION("\\", start_escaping),
                CAF_FSM_ACTION("\"", stop_reading),
                CAF_FSM_ACTION(nullptr, read)});
  }

  CAF_DECL_FSM_ACTION(stop_reading) {
    inputs(st, {CAF_FSM_ACTION(" ", no_op), CAF_FSM_TERM_ACTION()});
  }

  CAF_DECL_FSM_ACTION(start_escaping) {
    inputs(st, {CAF_FSM_ACTION("\"\\", stop_escaping)});
  }

  CAF_DECL_FSM_ACTION(stop_escaping) {
    st.value += c;
    inputs(st, {CAF_FSM_ACTION("\\", start_escaping),
                CAF_FSM_ACTION("\"", stop_reading),
                CAF_FSM_ACTION(nullptr, read)});
  }

  CAF_DECL_FSM_ACTION(read) {
    st.value += c;
  }

  // -- member functions -------------------------------------------------------

  inline const std::string& native_value() const {
    return st_.value;
  }

  config_value value() const override {
    return native_value();
  }

  parse_result parse(iterator first, iterator last) {
    init(st_);
    return parser::parse(st_, first, last);
  }
};

/// Reads either an integer or a real.
/// Interface for consuming INI-formatted input.
class ini_visitor {
public:
  virtual ~ini_visitor() {
    // nop
  }

  /// Visits `[x]` statements.
  void visit_group(const std::string& x);

  /// Visits `x = y` statements.
  void visit_assign(const std::string& x, config_value y);

  /// Visits `x += y` statements.
  void visit_append(const std::string& x, config_value y);

  /// Visits `!read x` statements.
  void visit_read(const std::string& x);

  /// Visits `!print x` statements.
  void visit_print(config_value x);
};

/// Reads a line from an INI config file by expanding variables and dropping
/// comments. Variables use "$name", "${name}", "$name[index]", or
/// "${name[index]}" notation and are expanded by the parser.
class ini_line : public fsm_base<storage::line> {
public:
  // -- initialization ---------------------------------------------------------

  template <class T>
  static void init(T& st) {
    reset(st);
    st.has_value = true;
    set_base_inputs(st);
  }


  template <class T>
  static void set_base_inputs(T& st) {
    inputs(st, {CAF_FSM_ACTION("$", start_variable),
                CAF_FSM_ACTION("\"", start_string),
                CAF_FSM_ACTION(";", start_dropping),
                CAF_FSM_ACTION(nullptr, string::read),
                CAF_FSM_TERM_ACTION()});
  }

  template <class T>
  static void set_string_inputs(T& st) {
    inputs(st, {CAF_FSM_ACTION("$", start_variable),
                CAF_FSM_ACTION("\"", stop_string),
                CAF_FSM_ACTION("\\", start_escaping),
                CAF_FSM_ACTION(nullptr, string::read)});
  }

  template <class T>
  static void set_inputs(T& st) {
    if (st.inside_string)
      set_string_inputs(st);
    else
      set_base_inputs(st);
  }

  // -- internal transitions ---------------------------------------------------

  CAF_DECL_FSM_ACTION(read_variable) {
    st.current_var += c;
  }

  CAF_DECL_FSM_ACTION(read_index) {
    st.current_idx += c;
  }

  // -- branching --------------------------------------------------------------

  CAF_DECL_FSM_ACTION(start_variable) {
    st.current_var.clear();
    st.current_idx.clear();
    inputs(st, {{" ", "fail", fail<T, ec::empty_variable_name>},
                CAF_FSM_ACTION("{", start_bracketed_variable),
                CAF_FSM_ACTION(alphanumeric, start_plain_variable),
                CAF_FSM_ACTION("_", start_plain_variable)});
  }

  // -- variable access using plain "$foo" or "$foo[bar]" notation -------------

  CAF_DECL_FSM_ACTION(start_plain_variable) {
    st.current_var += c;
    inputs(st, {CAF_FSM_ACTION(alphanumeric, read_variable),
                CAF_FSM_ACTION("_", read_variable),
                CAF_FSM_ACTION("[", start_plain_index),
                CAF_FSM_ACTION(nullptr, stop_plain_variable),
                CAF_FSM_ACTION("", stop_plain_variable)});
  }

  CAF_DECL_FSM_ACTION(stop_plain_variable) {
    st.value += st.kvs->get(st.current_var);
    // Immediately trigger next event from c if not at end of input.
    if (c != '\0') {
      set_inputs(st);
      event(st, c, "stop_plain_variable");
    } else {
      terminal(st, c, "stop_plain_variable");
    }
  }

  CAF_DECL_FSM_ACTION(start_plain_index) {
    inputs(st, {CAF_FSM_ACTION(alphanumeric, read_index),
                CAF_FSM_ACTION("]", stop_plain_index)});
  }

  CAF_DECL_FSM_ACTION(stop_plain_index) {
    st.value += st.kvs->get(st.current_var, st.current_idx);
    set_inputs(st);
  }

  // -- variable access using "${foo}" or "${foo[bar]}" notation ---------------

  CAF_DECL_FSM_ACTION(start_bracketed_variable) {
    inputs(st, {CAF_FSM_ACTION(alphanumeric, read_variable),
                CAF_FSM_ACTION("_", read_variable),
                CAF_FSM_ACTION("[", start_bracketed_index),
                CAF_FSM_ACTION("}", stop_bracketed_variable)});
  }

  CAF_DECL_FSM_ACTION(stop_bracketed_variable) {
    st.value += st.kvs->get(st.current_var);
    set_inputs(st);
  }

  CAF_DECL_FSM_ACTION(start_bracketed_index) {
    inputs(st, {CAF_FSM_ACTION(alphanumeric, read_index),
                CAF_FSM_ACTION("]", stop_bracketed_index)});
  }

  CAF_DECL_FSM_ACTION(stop_bracketed_index) {
    inputs(st, {CAF_FSM_ACTION("}", await_bracket_end)});
  }

  CAF_DECL_FSM_ACTION(await_bracket_end) {
    st.value += st.kvs->get(st.current_var, st.current_idx);
    set_inputs(st);
  }

  // -- strings ----------------------------------------------------------------

  CAF_DECL_FSM_ACTION(start_string) {
    st.value += '"';
    st.inside_string = true;
    set_string_inputs(st);
  }

  CAF_DECL_FSM_ACTION(stop_string) {
    st.value += '"';
    st.inside_string = false;
    set_base_inputs(st);
  }

  CAF_DECL_FSM_ACTION(start_escaping) {
    inputs(st, {CAF_FSM_ACTION("\"\\\t$", stop_escaping),
                {nullptr, "fail", fail<T, ec::invalid_escape_sequence>}});
  }

  CAF_DECL_FSM_ACTION(stop_escaping) {
    if (c == '$') {
      // The next parser (usually the string parser) does not escape $ signs.
      st.value += '$';
    } else {
      // Forward fully escaped sequence to the next parser.
      st.value += '\\';
      st.value += c;
    }
    set_string_inputs(st);
  }

  // -- drop comments ----------------------------------------------------------

  CAF_DECL_FSM_ACTION(start_dropping) {
    inputs(st, {CAF_FSM_ACTION(nullptr, no_op), CAF_FSM_TERM_ACTION()});
  }

  // -- constructors, destructors, and assignment operators --------------------

  ini_line(store& kvs) {
    st_.kvs = &kvs;
  }

  // -- member functions -------------------------------------------------------

  inline const std::string& native_value() const {
    return st_.value;
  }

  config_value value() const override {
    return native_value();
  }

  parse_result parse(iterator first, iterator last) {
    init(st_);
    return parser::parse(st_, first, last);
  }
};

} // namespace parser

template <class T>
using kvp_vector = std::vector<std::pair<std::string, T>>;

template <class Parser, class T>
void test_valids(Parser& f, const kvp_vector<T>& xs) {
  for (auto& x : xs) {
    auto e = x.first.end();
    auto i = f.parse(x.first.begin(), e);
    if (i.first != e) {
      CAF_ERROR("parser stopped at '" << *i.first << "', last action: "
                << i.second << ", input: " << x.first);
    } else {
      CAF_CHECK_EQUAL(f.error_code(), parser::ec::none);
      CAF_CHECK_EQUAL(f.native_value(), x.second);
    }
  }
}

CAF_TEST(valid_integers) {
  kvp_vector<int64_t> xs{
    {"01", 1},
    {"123", 123},
    {"0b0101", 5},
    {"0B101", 5},
    {"0xFF", 255},
    {"0XFF", 255},
    {"-0xFF", -255},
    {"-0Xff", -255},
    {"-0b11", -3},
    {"-99", -99},
    {"-0771", -505},
  };
  parser::integer f;
  test_valids(f, xs);
}

CAF_TEST(valid_reals) {
  kvp_vector<double> xs{
    {"1", 1.},
    {"+1", 1.},
    {"-1", -1.},
    {"1.", 1.},
    {".1", .1},
    {"+.1", .1},
    {"-.1", -.1},
    {"1e5", 1e5},
    {"1e+5", 1e+5},
    {"1e-5", 1e-5},
    {"1E55", 1E55},
    {"1E+55", 1E+55},
    {"1E-55", 1E-55},
  };
  parser::real f;
  test_valids(f, xs);
}

CAF_TEST(valid_numbers) {
  auto i = [](int x) { return static_cast<int64_t>(x); };
  kvp_vector<config_value> xs{
    {"01", i(1)},
    {"123", i(123)},
    {"0b0101", i(5)},
    {"0B101", i(5)},
    {"0xFF", i(255)},
    {"0XFF", i(255)},
    {"-0xFF", i(-255)},
    {"-0Xff", i(-255)},
    {"1", 1.},
    {"+1", 1.},
    {"-1", -1.},
    {"1.", 1.},
    {".1", .1},
    {"+.1", .1},
    {"-.1", -.1},
    {"1e5", 1e5},
    {"1e+5", 1e+5},
    {"1e-5", 1e-5},
    {"1E55", 1E55},
    {"1E+55", 1E+55},
    {"1E-55", 1E-55},
  };
  parser::integer f;
  parser::real g;
  parser::fsm_failover h{f, g};
  test_valids(h, xs);
}

CAF_TEST(infinite_reals) {
  auto inf = std::numeric_limits<double>::infinity();
  kvp_vector<double> xs{
    {"inf", inf},
    {"iNf", inf},
    {"inF", inf},
    {"INF", inf},
    {"+inf", -inf},
    {"-inf", -inf},
    {"infinity", inf},
    {"+infinity", inf},
    {"-infinity", -inf},
  };
  parser::real f;
  for (auto& x : xs) {
    auto e = x.first.end();
    auto i = f.parse(x.first.begin(), e);
    CAF_CHECK_EQUAL(i.first, e);
    CAF_CHECK_EQUAL(f.error_code(), parser::ec::none);
    CAF_CHECK(isinf(f.native_value()));
  }
}

CAF_TEST(nan_reals) {
  auto nan = std::numeric_limits<double>::quiet_NaN();
  kvp_vector<double> xs{
    {"nan", nan},
    {"nAn", nan},
    {"NaN", nan},
    {"NAN", nan},
    {"+nan", nan},
    {"-nan", nan},
  };
  parser::real f;
  for (auto& x : xs) {
    auto e = x.first.end();
    auto i = f.parse(x.first.begin(), e);
    CAF_CHECK_EQUAL(i.first, e);
    CAF_CHECK_EQUAL(f.error_code(), parser::ec::none);
    CAF_CHECK(isnan(f.native_value()));
  }

}

CAF_TEST(valid_durations) {
  kvp_vector<duration> xs{
    {"123min", {time_unit::minutes, 123}},
    {"0771s", {time_unit::seconds, 505}},
    {"0b0101ms", {time_unit::milliseconds, 5}},
    {"0xFFus", {time_unit::microseconds, 255}},
    {"0ns", {time_unit::nanoseconds, 0}},
  };
  parser::duration f;
  test_valids(f, xs);
}

CAF_TEST(invalid_durations) {
  parser::duration f;
  auto parse = [&](const std::string& str) -> parser::ec {
    f.parse(str.begin(), str.end());
    return f.error_code();
  };
  CAF_CHECK_EQUAL(parse(""), parser::ec::empty_string);
  CAF_CHECK_EQUAL(parse("min"), parser::ec::missing_number);
  CAF_CHECK_EQUAL(parse("s"), parser::ec::missing_number);
  CAF_CHECK_EQUAL(parse("ms"), parser::ec::missing_number);
  CAF_CHECK_EQUAL(parse("us"), parser::ec::missing_number);
  CAF_CHECK_EQUAL(parse("ns"), parser::ec::missing_number);
  CAF_CHECK_EQUAL(parse("0"), parser::ec::missing_suffix);
  CAF_CHECK_EQUAL(parse("0z"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("0m"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("0mi"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("0minn"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("0b101"), parser::ec::missing_suffix);
  CAF_CHECK_EQUAL(parse("0b101z"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("0b101m"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("0b101mi"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("0b101minn"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("066"), parser::ec::missing_suffix);
  CAF_CHECK_EQUAL(parse("066z"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("066m"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("066mi"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("066minn"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("22"), parser::ec::missing_suffix);
  CAF_CHECK_EQUAL(parse("22z"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("22m"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("22mi"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("22minn"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("0xf2"), parser::ec::missing_suffix);
  CAF_CHECK_EQUAL(parse("0x1z"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("0x1m"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("0x1mi"), parser::ec::incomplete_suffix);
  CAF_CHECK_EQUAL(parse("0x1minn"), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(parse("1.2s"), parser::ec::unexpected_character);
}

CAF_TEST(valid_strings) {
  kvp_vector<std::string> xs{
    {"    \"abc\"", "abc"},
    {"\"abc\"    ", "abc"},
    {"    \"abc\"     ", "abc"},
    {"\"foo\"", "foo"},
    {"\"me: \\\"n\\\\ce!\\\"\"", "me: \"n\\ce!\""},
  };
  parser::string f;
  test_valids(f, xs);
}

CAF_TEST(invalid_strings) {
  parser::string f;
  std::string x0 = "\"foo\"bar";
  auto e0 = x0.end();
  auto i0 = f.parse(x0.begin(), e0);
  CAF_REQUIRE_NOT_EQUAL(i0.first, e0);
  CAF_CHECK_EQUAL(f.error_code(), parser::ec::unexpected_character);
  CAF_CHECK_EQUAL(*i0.first, 'b');
}

CAF_TEST(lines) {
  kvp_vector<std::string> xs{
    {" \"abc\" ; def", " \"abc\" "},
    {"\"foo: $bar\"", "\"foo: \""},
    {"$bar.txt", ".txt"},
    {"$foo.txt", "ABC.txt"},
    {"${foo}.txt", "ABC.txt"},
    {"$ENV[foo].txt", "xyz.txt"},
    {"${ENV[foo]}.txt", "xyz.txt"},
    {"$foo$bar.txt;file", "ABC.txt"},
    {"${foo}$bar.txt;file", "ABC.txt"},
    {"$foo${bar}.txt;file", "ABC.txt"},
  };
  struct mock_kvs : parser::store {
    std::string get(const std::string& var, const std::string& idx) const override {
      return var == "ENV" && idx  == "foo" ? "xyz" : "";
    }
    std::string get(const std::string& var) const override {
      return var == "foo" ? "ABC" : "";
    }
  };
  mock_kvs m;
  parser::ini_line f{m};
  test_valids(f, xs);
}
