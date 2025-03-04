#pragma once 

#include <fmt/format.h>
#include <fmt/color.h>
#include <fmt/chrono.h>
// #include <fmt/xchar.h>
#include <fmt/core.h>
#include <string>
#include <pstring.h>

#define LOG_COLOR(_color, __fmt__, ...) \
fmt::print(fmt::fg(fmt::color::_color), __fmt__ + std::string("\n"), ##__VA_ARGS__)

#define LOG_RED(__fmt__, ... ) \
LOG_COLOR(red, __fmt__, ##__VA_ARGS__)

#define LOG_GREEN(__fmt__, ... ) \
LOG_COLOR(green, __fmt__, ##__VA_ARGS__)

#define LOG_BLUE(__fmt__, ... ) \
LOG_COLOR(blue, __fmt__, ##__VA_ARGS__)

#define LOG_NONE(__fmt__, ... ) \
fmt::print( __fmt__ + std::string("\n"), ##__VA_ARGS__)


#define LOG_DEBUG(__fmt, ...) \
fmt::print(fmt::fg(fmt::color::blue_violet), "[DEBUG]: ");\
fmt::print(fmt::fg(fmt::color::green), "[{}:{},{}] ", __FILE__, __LINE__, __func__);\
fmt::print(__fmt + std::string("\n"), ##__VA_ARGS__); \
fflush(stdout);


// template<typename... Args>
// std::string dyna_print(std::string_view rt_fmt_str, Args&&... args) {
//     return fmt::vformat(
//         rt_fmt_str,
//         fmt::make_format_args(std::forward<Args>(args)...)
//     );
// }
template<typename... Args>
inline std::string __dyna_print(const std::string& rt_fmt_str, Args... args) {
    return fmt::format(rt_fmt_str, args...);
}

inline std::string __format_str( const std::string& var, const std::string& name = "") {
    if(name.size() != 0) {
        return __dyna_print(std::string("{} = {}")  , name, var);
    }
    return __dyna_print("{}", var);
}
        
#define f(var, fmt) (std::string(fmt).size() == '\0' ? \
    __format_str(__dyna_print("{}",var)) : \
    fmt[0] == '=' ? \
    __format_str(__dyna_print(std::string("{") + std::string(fmt).substr(1) + "}", var), #var) : \
    __format_str(__dyna_print( std::string("{")  + fmt + "}", var)))

#define fe(var) f(var, "=")


template <>
struct fmt::formatter<PString> {
    constexpr auto parse(fmt::format_parse_context& ctx) {
        return ctx.begin();
    }
    auto format(const PString& pstr, fmt::format_context& ctx) const {
        return fmt::format_to(ctx.out(), "{}", static_cast<std::string>(pstr));
    }
};
