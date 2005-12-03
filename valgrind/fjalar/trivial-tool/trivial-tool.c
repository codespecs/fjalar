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
  // Return false because we have no options to process
  return False;
}

// Runs after the tool exits:
void fjalar_tool_finish() {
  VG_(printf)("\nfjalar_tool_finish()\n");
}


TraversalResult trivialAction(VariableEntry* var,
                              char* varName,
                              VariableOrigin varOrigin,
                              UInt numDereferences,
                              UInt layersBeforeBase,
                              char overrideIsInit,
                              DisambigOverride disambigOverride,
                              char isSequence,
                              // pValue only valid if isSequence is false
                              void* pValue,
                              // pValueArray and numElts only valid if
                              // isSequence is true
                              void** pValueArray,
                              UInt numElts,
                              FunctionEntry* varFuncInfo,
                              char isEnter) {
  VG_(printf)("   varName: %s\n", varName);
  return DO_NOT_DEREF_MORE_POINTERS;
}

// These functions are called during every instance of a function
// entrance and exit, respectively:
void fjalar_tool_handle_function_entrance(FunctionExecutionState* f_state) {
  struct geniterator* it;

  VG_(printf)("%s (enter)\n",
	      f_state->func->fjalar_name);

  visitVariableGroup(GLOBAL_VAR,
                     0,
                     1,
                     0,
                     &trivialAction);

  visitVariableGroup(FUNCTION_FORMAL_PARAM,
                     f_state->func,
                     1,
                     0,
                     &trivialAction);
}

void fjalar_tool_handle_function_exit(FunctionExecutionState* f_state) {
  VG_(printf)("%s (exit)\n",
	      f_state->func->fjalar_name);

  visitVariableGroup(GLOBAL_VAR,
                     0,
                     0,
                     0,
                     &trivialAction);

  visitVariableGroup(FUNCTION_FORMAL_PARAM,
                     f_state->func,
                     0,
                     0,
                     &trivialAction);

  visitVariableGroup(FUNCTION_RETURN_VAR,
                     f_state->func,
                     0,
                     0,
                     &trivialAction);
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
