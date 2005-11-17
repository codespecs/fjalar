// A really basic tool built upon Fjalar
// (used for internal testing of the framework)
// by Philip Guo

#include "../fjalar_tool.h"

// Runs before processing command-line options:
void fjalar_tool_pre_clo_init() {
  VG_(printf)("\nfjalar_tool_pre_clo_init()\n");
}

// Runs after processing command-line options:
void fjalar_tool_post_clo_init() {
  VG_(printf)("\nfjalar_tool_post_clo_init()\n");
}

// Prints instructions when the --help option is invoked:
void fjalar_tool_print_usage() {
  VG_(printf)("\nfjalar_tool_print_usage()\n");
}

// Processes command-line options:
Bool fjalar_tool_process_cmd_line_option(Char* arg) {
  return True;
}

// Runs after the tool exits:
void fjalar_tool_finish() {
  VG_(printf)("\nfjalar_tool_finish()\n");
}


// When this function is called, Valgrind proper is already
// initialized so that tools can now have access to more useful
// Valgrind functions such as C++ name demangling:
void fjalar_tool_handle_first_function_entrance() {
  VG_(printf)("\nfjalar_tool_handle_first_function_entrance\n");
}

// These functions are called during every instance of a function
// entrance and exit, respectively:
void fjalar_tool_handle_function_entrance(FunctionExecutionState* f_state) {
  VG_(printf)("fjalar_tool_handle_function_entrance(%s)\n",
	      f_state->func->fjalar_name);
}

void fjalar_tool_handle_function_exit(FunctionExecutionState* f_state) {
  VG_(printf)("fjalar_tool_handle_function_exit(%s)\n",
	      f_state->func->fjalar_name);
}


// Constructors and destructors for classes that can be sub-classed:

// Default constructor that should return a particular sub-class of an
// object.  This should call VG_(calloc) the proper amount of space
// for the object and initialize it with whatever initial state is
// necessary.
VariableEntry* constructVariableEntry() {
  return (VariableEntry*)(VG_(calloc)(1, sizeof(VariableEntry)));
}

TypeEntry* constructTypeEntry() {
  return (TypeEntry*)(VG_(calloc)(1, sizeof(TypeEntry)));
}

FunctionEntry* constructFunctionEntry() {
  return (FunctionEntry*)(VG_(calloc)(1, sizeof(FunctionEntry)));
}

// Destructors that should clean-up and then call VG_(free) on the
// respective entries.
void destroyVariableEntry(VariableEntry* v) {
  VG_(free)(v);
}

void destroyTypeEntry(TypeEntry* t) {
  VG_(free)(t);
}

void destroyFunctionEntry(FunctionEntry* f) {
  VG_(free)(f);
}
