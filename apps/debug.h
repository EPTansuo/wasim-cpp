#pragma once 

#include <fmt/format.h>
#include <fmt/color.h>
#include <string>

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
fmt::print(fmt::fg(fmt::color::blue_violet), "[DEBUG]: "); \
fmt::print(fmt::fg(fmt::color::green), "[{}:{},{}] ", __FILE__, __LINE__, __func__);\
fmt::print(__fmt + std::string("\n"), ##__VA_ARGS__)
