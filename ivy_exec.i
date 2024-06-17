%module ivy_exec
%include "std_string.i"
%{
/* Put header files here or function declarations like below */
extern void ivy_exec_init();
extern void ivy_exec_reset_buffer();
extern std::string ivy_exec_run_protocol(std::string input);
%}
extern void ivy_exec_init();
extern void ivy_exec_reset_buffer();
extern std::string ivy_exec_run_protocol(std::string input);

