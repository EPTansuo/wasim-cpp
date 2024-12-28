#pragma once

#include <string>

namespace wasim {
    void run_cmd(const std::string & cmd_string, int timeout);
    std::string GetTimeStamp();
}