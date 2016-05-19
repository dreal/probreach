//
// Created by fedor on 26/02/16.
//

#include "dreal_wrapper.h"
#include <system_error>
#include <unistd.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <logging/easylogging++.h>
#include <pdrh_config.h>

std::vector<std::string> dreal::sat_answers = {"sat", "delta-sat"};
std::vector<std::string> dreal::unsat_answers = {"unsat"};

int dreal::execute(std::string bin, std::string input, std::string args)
{
    /*
    int res;
    pid_t solver_pid = fork();
    if(solver_pid == 0)
    {
        std::stringstream s;
        s << bin << " " << args << " " << input << " > " << input << ".output";
        //res = system(s.str().c_str());
        //res = execl(s.str().c_str(), 0, 0);
        //res = execv(s.str().c_str(), NULL);
        int stdout_copy = dup(1);
        int fd;
        if((fd = open("hello.output", O_RDWR, S_IRUSR | S_IWUSR)) == -1)
        {
            std::cout << "Error opening the output file" << std::endl;
            return -1;
        }
        dup2(fd,STDOUT_FILENO);
        close(fd);
        execl("/bin/echo", "/bin/echo", "HELLO");
        dup2(stdout_copy, STDOUT_FILENO);

        if(res != 0)
        {
            std::cout << "Problem making system call: " << s.str() << std::endl;
            res = -1;
        }
        // parsing the output
        try
        {
            res = dreal::parse_output(input + ".output");
        }
        // unrecognized solver output
        catch(std::invalid_argument e)
        {
            std::cout << e.what() << std::endl;
            res = -1;
        }
    }
    else
    {
        wait(NULL);
        //int status;
        //waitpid(solver_pid, &status, 0);
        std::cout << "Parent process" << std::endl;
        //if(WIFEXITED(status))
        //{
        //    std::cout << "The child process has exited" << std::endl;
        //}
    }
    */
    std::stringstream s;
    s << bin << " " << args << " " << input << " > " << input << ".output";
    //LOG(DEBUG) << s.str();
    int res = system(s.str().c_str());
    if(res != 0)
    {
        std::cout << "Problem making system call: " << s.str() << std::endl;
        res = -1;
    }
    // parsing the output
    try
    {
        res = dreal::parse_output(input + ".output");
    }
    // unrecognized solver output
    catch(std::invalid_argument e)
    {
        std::cout << e.what() << std::endl;
        res = -1;
    }
    return res;
}

int dreal::parse_output(std::string output)
{
    std::fstream output_file;
    output_file.open(output.c_str());
    if(!output_file.is_open())
    {
        std::stringstream s;
        s << "Problem opening the file " << output;
        throw std::invalid_argument(s.str());
    }
    // getting the last line of the file
    std::string last_line, line;
    while(getline(output_file, line))
    {
        last_line = line;
    }
    // analyzing the last line of the output
    std::string res;
    unsigned long pos = last_line.find_first_of(" ");
    if(pos != std::string::npos)
    {
        res = last_line.substr(0, pos);
    }
    else
    {
        res = last_line;
    }
    // checking if the output line is a sat answer
    if(std::find(dreal::sat_answers.cbegin(), dreal::sat_answers.cend(), res) != dreal::sat_answers.cend())
    {
        return 0;
    }
    else if(std::find(dreal::unsat_answers.cbegin(), dreal::unsat_answers.cend(), res) != dreal::unsat_answers.cend())
    // checking if the output line is an unsat answer
    {
        return 1;
    }
    else
    // unrecognized answer
    {
        std::stringstream s;
        s << "Unrecognized solver output: " << res;
        throw std::invalid_argument(s.str());
    }
}