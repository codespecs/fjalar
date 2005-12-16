// A really basic tool built upon Fjalar that prints out variable
// names and array sizes at function entrances and exits
// by Philip Guo, Dec. 2005

// Only implements the functions required by fjalar_tool.h
#include "../fjalar_tool.h"

// Runs before processing command-line options:
void fjalar_tool_pre_clo_init() {
  VG_(printf)("\nfjalar_tool_pre_clo_init()\n\n");
}

// Runs after processing command-line options:
void fjalar_tool_post_clo_init() {
  VG_(printf)("\nfjalar_tool_post_clo_init()\n\n");
}

// Prints instructions when the --help option is invoked:
void fjalar_tool_print_usage() {
  VG_(printf)("\nfjalar_tool_print_usage()\n\n");
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

// This simple callback function prints out variable names, and if
// it's a sequence, the number of elements
TraversalResult basicAction(VariableEntry* var,
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
  if (isSequence) {
    VG_(printf)("     %s - %d elements\n", varName, numElts);
  }
  else {
    VG_(printf)("     %s\n", varName);
  }

  // We want to deref. more pointers so that we can find out array
  // sizes for derived variables:
  return DEREF_MORE_POINTERS;
}

// These functions are called during every instance of a function
// entrance and exit, respectively:
void fjalar_tool_handle_function_entrance(FunctionExecutionState* f_state) {

  VG_(printf)("[%s - ENTER]\n",
	      f_state->func->fjalar_name);

  VG_(printf)("  Global variables:\n");
  visitVariableGroup(GLOBAL_VAR,
                     0,
                     1,
                     0,
                     &basicAction);

  VG_(printf)("  Function formal parameters:\n");
  // We need to use the virtual stack for function parameters:
  visitVariableGroup(FUNCTION_FORMAL_PARAM,
                     f_state->func,
                     1,
                     f_state->virtualStack,
                     &basicAction);
}

void fjalar_tool_handle_function_exit(FunctionExecutionState* f_state) {
  VG_(printf)("[%s - EXIT]\n",
	      f_state->func->fjalar_name);

  VG_(printf)("  Global variables:\n");
  visitVariableGroup(GLOBAL_VAR,
                     0,
                     0,
                     0,
                     &basicAction);

  VG_(printf)("  Function formal parameters:\n");
  // We need to use the virtual stack for function parameters:
  visitVariableGroup(FUNCTION_FORMAL_PARAM,
                     f_state->func,
                     0,
                     f_state->virtualStack,
                     &basicAction);

  VG_(printf)("  Return value:\n");
  visitReturnValue(f_state, &basicAction);

}


// Constructors and destructors for classes that can be sub-classed:

// We do not implement any sub-classing so just implement the
// 'default' constructor/destructor by calling VG_(calloc) and
// VG_(free), respectively
VariableEntry* constructVariableEntry() {
  return (VariableEntry*)(VG_(calloc)(1, sizeof(VariableEntry)));
}

TypeEntry* constructTypeEntry() {
  return (TypeEntry*)(VG_(calloc)(1, sizeof(TypeEntry)));
}

FunctionEntry* constructFunctionEntry() {
  return (FunctionEntry*)(VG_(calloc)(1, sizeof(FunctionEntry)));
}

void destroyVariableEntry(VariableEntry* v) {
  VG_(free)(v);
}

void destroyTypeEntry(TypeEntry* t) {
  VG_(free)(t);
}

void destroyFunctionEntry(FunctionEntry* f) {
  VG_(free)(f);
}
