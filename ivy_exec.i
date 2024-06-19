%module ivy_exec
%include "std_string.i"
%include "std_vector.i"
%{
/* Put header files here or function declarations like below */
// Instantiate templates used by example
extern void ivy_exec_init();
extern void ivy_exec_reset_buffer();
extern std::string ivy_exec_get_buffer();
extern void ivy_exec_set_state(std::vector<std::string> state_values);
extern void ivy_exec_run_protocol(std::vector<std::string> inputs);
%}
%template(StrVector) std::vector<std::string>;
extern void ivy_exec_init();
extern void ivy_exec_reset_buffer();
extern std::string ivy_exec_get_buffer();
extern void ivy_exec_set_state(std::vector<std::string> state_values);
extern void ivy_exec_run_protocol(std::vector<std::string> inputs);
