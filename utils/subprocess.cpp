#include "subprocess.h"

#include <boost/asio.hpp>
#include <boost/bind.hpp>
#include <boost/process.hpp>
#include <boost/process/async.hpp>

#include <time.h>
#include <chrono>

namespace wasim {

    namespace bp = boost::process;
    class Process
    {
    public:
        Process(const std::string & cmd, int timeout);
        void run();

    private:
        void timeout_handler(boost::system::error_code ec);

        const std::string command;
        const int timeout;

        bool killed = false;
        bool stopped = false;

        std::string stdOut;
        std::string stdErr;
        int returnStatus = 0;

        boost::asio::io_context ios;
        boost::process::group group;
        boost::asio::deadline_timer deadline_timer;
    };

    Process::Process(const std::string & cmd, const int timeout)
        : command(cmd), timeout(timeout), deadline_timer(ios)
    {
    }

    void Process::timeout_handler(boost::system::error_code ec)
    {
        if (stopped) return;

        if (ec == boost::asio::error::operation_aborted) return;

        if (deadline_timer.expires_at()
            <= boost::asio::deadline_timer::traits_type::now()) {
            // std::cout << "Time Up!" << std::endl;
            group.terminate();  // NOTE: anticipate errors
            // std::cout << "Killed the process and all its decendants" << std::endl;
            killed = true;
            stopped = true;
            deadline_timer.expires_at(boost::posix_time::pos_infin);
        }
        // NOTE: don't make it a loop
        // deadline_timer.async_wait(boost::bind(&Process::timeout_handler, this,
        // boost::asio::placeholders::error));
    }

    void Process::run()
    {
        std::future<std::string> dataOut;
        std::future<std::string> dataErr;

        deadline_timer.expires_from_now(boost::posix_time::milliseconds(timeout));
        deadline_timer.async_wait(boost::bind(
            &Process::timeout_handler, this, boost::asio::placeholders::error));

        bp::child c(command,
                    bp::std_in.close(),
                    bp::std_out > dataOut,
                    bp::std_err > dataErr,
                    ios,
                    group,
                    bp::on_exit([=](int e, std::error_code ec) {
                        // TODO handle errors
                        // std::cout << "on_exit: " << ec.message() << " -> " << e <<
                        // std::endl;
                        deadline_timer.cancel();
                        returnStatus = e;
                    }));

        ios.run();

        stdOut = dataOut.get();
        stdErr = dataErr.get();

        c.wait();

        returnStatus = c.exit_code();
    }

    std::string GetTimeStamp()
    {
        auto timeNow = std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::system_clock::now().time_since_epoch());
        long long timestamp = timeNow.count();
        return std::to_string(timestamp);
    }

    void run_cmd(const std::string & cmd_string, int timeout)
    {
        Process p(cmd_string, timeout);
        p.run();
    }

} // end of namespace wasim
