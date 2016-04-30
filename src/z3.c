#include <SWI-Prolog.h>
#include <z3.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>

enum ASTType {
  AST_TYPE,
  EXCEPTION_TYPE
};

struct AST {
  union {
    Z3_ast ast;
    term_t exception;
  } value;
  enum ASTType which;
};

struct MultiResult {
  union {
    Z3_ast* results;
    term_t exception;
  } value;
  enum ASTType which;
  unsigned int num_results_requested;
};

enum SolverTypeId {
  BOOLEAN_TYPE,
  INT_TYPE,
  UNINSTANTIATED_TYPE
};

struct SolverType {
  enum SolverTypeId id;
};

struct VarMapEntry {
  char* name;
  term_t prolog_variable;
  Z3_ast z3_variable;
  struct SolverType solver_type;
};

struct Cons {
  struct VarMapEntry head;
  struct Cons* tail;
};

struct List {
  struct Cons* contents;
  unsigned int length;
};

struct TranslationState {
  Z3_context context;
  struct List list;
  term_t map_true_to;
  char* true_name;
  term_t map_false_to;
  char* false_name;
};

static void mk_empty_list(struct List* list);
static void prepend(struct VarMapEntry what,
		    struct List* list);
static void free_list(struct List* list);

static void set_ast(Z3_ast ast, struct AST* retval);
static void set_error(term_t term_with_error,
		      char* message,
		      struct AST* ast);
static Z3_ast forward_unary(Z3_context context,
			    Z3_ast to_forward);
static Z3_ast and_wrapper(Z3_context context,
			  Z3_ast left,
			  Z3_ast right);
static Z3_ast or_wrapper(Z3_context context,
			 Z3_ast left,
			 Z3_ast right);
static Z3_ast distinct_wrapper(Z3_context context,
			       Z3_ast left,
			       Z3_ast right);
static Z3_ast add_wrapper(Z3_context context,
			  Z3_ast left,
			  Z3_ast right);
static Z3_ast sub_wrapper(Z3_context context,
			  Z3_ast left,
			  Z3_ast right);
static Z3_ast mul_wrapper(Z3_context context,
			  Z3_ast left,
			  Z3_ast right);
static Z3_ast abs_wrapper(Z3_context context,
			  Z3_ast around);
static struct MultiResult multi_result(struct TranslationState* state,
				       term_t term,
				       struct SolverType** expected_types,
				       unsigned int num_results);
static void free_multi_result(struct MultiResult* result);
static struct AST mk_unary(struct TranslationState* state,
			   term_t holds_param,
			   Z3_ast (*f)(Z3_context, Z3_ast),
			   struct SolverType* expected_nested_type);
static struct AST mk_binary(struct TranslationState* state,
			    term_t holds_params,
			    Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast),
			    struct SolverType* expected_left_type,
			    struct SolverType* expected_right_type);
static struct AST mk_ternary(struct TranslationState* state,
			     term_t holds_params,
			     Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast, Z3_ast),
			     struct SolverType* first_type,
			     struct SolverType* second_type,
			     struct SolverType* third_type);
static struct AST term_to_ast(struct TranslationState* state,
			      term_t term,
			      struct SolverType* expected_type);
static foreign_t z3_sat(term_t query,
			term_t map_true_to,
			term_t map_false_to);

// For the moment, we only care about the theory of integers

static void mk_empty_list(struct List* list) {
  list->contents = NULL;
  list->length = 0;
}

void prepend(struct VarMapEntry what, struct List* list) {
  struct Cons* cell = malloc(sizeof(struct Cons));
  cell->head = what;
  cell->tail = list->contents;
  list->contents = cell;
  list->length++;
}

static void set_ast(Z3_ast ast, struct AST* retval) {
  retval->value.ast = ast;
  retval->which = AST_TYPE;
}

static term_t make_type_error(char* message,
			      term_t term_with_error) {
  term_t except = PL_new_term_ref();
  int ensure = PL_unify_term(except,
			     PL_FUNCTOR_CHARS,
			     "type_error",
			     2,
			     PL_CHARS, message,
			     PL_TERM, term_with_error);
  assert(ensure);
  return except;
}

static void set_error(term_t term_with_error, char* message, struct AST* retval) {
  retval->value.exception = make_type_error(message,
					    term_with_error);
  retval->which = EXCEPTION_TYPE;
}

static Z3_ast forward_unary(Z3_context context,
			    Z3_ast to_forward) {
  return to_forward;
}

static Z3_ast and_wrapper(Z3_context context,
			  Z3_ast left,
			  Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_and(context, 2, args);
}

static Z3_ast or_wrapper(Z3_context context,
			 Z3_ast left,
			 Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_or(context, 2, args);
}

static Z3_ast distinct_wrapper(Z3_context context,
			       Z3_ast left,
			       Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_distinct(context, 2, args);
}

static Z3_ast add_wrapper(Z3_context context,
			  Z3_ast left,
			  Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_add(context, 2, args);
}

static Z3_ast sub_wrapper(Z3_context context,
			  Z3_ast left,
			  Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_sub(context, 2, args);
}

static Z3_ast mul_wrapper(Z3_context context,
			  Z3_ast left,
			  Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_mul(context, 2, args);
}

static Z3_ast abs_wrapper(Z3_context context,
			  Z3_ast around) {
  // abs(x) = if (x < 0) -x else x
  return Z3_mk_ite(context,
		   Z3_mk_lt(context,
			    around,
			    Z3_mk_int(context, 0, Z3_mk_int_sort(context))),
		   Z3_mk_unary_minus(context, around),
		   around);
}

static struct AST mk_unary(struct TranslationState* state,
			   term_t holds_param,
			   Z3_ast (*f)(Z3_context, Z3_ast),
			   struct SolverType* expected_nested_type) {
  struct SolverType* expected[1];
  expected[0] = expected_nested_type;
  struct MultiResult result = multi_result(state,
					   holds_param,
					   expected,
					   1);
  struct AST retval;

  if (result.which == AST_TYPE) {
    set_ast((*f)(state->context,
		 result.value.results[0]),
	    &retval);
  } else {
    retval.which = EXCEPTION_TYPE;
    retval.value.exception = result.value.exception;
  }

  free_multi_result(&result);

  return retval;
} // mk_unary

static struct AST mk_binary(struct TranslationState* state,
			    term_t holds_params,
			    Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast),
			    struct SolverType* expected_left_type,
			    struct SolverType* expected_right_type) {
  struct SolverType* expected[2];
  expected[0] = expected_left_type;
  expected[1] = expected_right_type;
  struct MultiResult result = multi_result(state,
					   holds_params,
					   expected,
					   2);
  struct AST retval;

  if (result.which == AST_TYPE) {
    set_ast((*f)(state->context,
		 result.value.results[0],
		 result.value.results[1]),
	    &retval);
  } else {
    retval.which = EXCEPTION_TYPE;
    retval.value.exception = result.value.exception;
  }

  free_multi_result(&result);

  return retval;
} // mk_binary

static struct AST mk_ternary(struct TranslationState* state,
			     term_t holds_params,
			     Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast, Z3_ast),
			     struct SolverType* first_type,
			     struct SolverType* second_type,
			     struct SolverType* third_type) {
  struct SolverType* expected[3];
  expected[0] = first_type;
  expected[1] = second_type;
  expected[2] = third_type;
  struct MultiResult result = multi_result(state,
					   holds_params,
					   expected,
					   3);
  struct AST retval;

  if (result.which == AST_TYPE) {
    set_ast((*f)(state->context,
		 result.value.results[0],
		 result.value.results[1],
		 result.value.results[2]),
	    &retval);
  } else {
    retval.which = EXCEPTION_TYPE;
    retval.value.exception = result.value.exception;
  }

  free_multi_result(&result);

  return retval;
} // mk_ternary

static void free_multi_result(struct MultiResult* result) {
  if (result->which == AST_TYPE) {
    free(result->value.results);
  }
}

static struct MultiResult multi_result(struct TranslationState* state,
				       term_t term,
				       struct SolverType** expected_types,
				       unsigned int num_results) {
  assert(num_results > 0);

  struct MultiResult retval;
  retval.which = AST_TYPE;
  retval.num_results_requested = num_results;
  retval.value.results = malloc(sizeof(Z3_ast) * num_results);
  
  int x;
  for (x = 0; x < num_results; x++) {
    term_t cur_term = PL_new_term_ref();
    int ensure = PL_get_arg(x + 1, term, cur_term);
    assert(ensure);
    struct AST cur_ast = term_to_ast(state, cur_term, expected_types[x]);

    // bail out on error
    if (cur_ast.which == EXCEPTION_TYPE) {
      free(retval.value.results);
      retval.which = EXCEPTION_TYPE;
      retval.value.exception = cur_ast.value.exception;
      return retval;
    }

    assert(cur_ast.which == AST_TYPE);
    retval.value.results[x] = cur_ast.value.ast;
  }

  return retval;
} // multi_result

static struct VarMapEntry* get_variable(struct List* list,
					char* name) {
  struct VarMapEntry* retval = NULL;
  struct Cons* cur = list->contents;
  while (cur != NULL) {
    // TODO: could we just compare pointers?
    if (strcmp(name, cur->head.name) == 0) {
      retval = &(cur->head);
      break;
    }
    cur = cur->tail;
  }

  return retval;
}

// returns non-zero on success
static int unify_types(struct SolverType* type1,
		       struct SolverType* type2) {
  if (type1->id == UNINSTANTIATED_TYPE) {
    type1->id = type2->id;
    return 1;
  } else if (type2->id == UNINSTANTIATED_TYPE) {
    type2->id = type1->id;
    return 1;
  } else if (type1->id == type2->id) {
    return 1;
  } else {
    return 0;
  }
}

static void set_smt_type_error(term_t prolog_term,
			       struct AST* result) {
  set_error(prolog_term, "SMT type error", result);
}

// returns non-zero on success
static int unify_types_set_ast(struct SolverType* type1,
			       struct SolverType* type2,
			       term_t prolog_term,
			       Z3_ast z3_ast,
			       struct AST* result_ast) {
  int retval = unify_types(type1, type2);
  if (retval) {
    set_ast(z3_ast, result_ast);
  } else {
    set_smt_type_error(prolog_term, result_ast);
  }
  return retval;
}

// returns zero if there was no applicable sort
static int get_sort_for_type(Z3_context context,
			     struct SolverType* expected_type,
			     Z3_sort* sort) {
  switch (expected_type->id) {
  case BOOLEAN_TYPE:
    *sort = Z3_mk_bool_sort(context);
    return 1;
  case INT_TYPE:
    *sort = Z3_mk_int_sort(context);
    return 1;
  default:
    return 0;
  }
}

static struct AST handle_ternary_op(struct TranslationState* state,
				    term_t prolog_term,
				    const char* name,
				    struct SolverType* expected_type) {
  struct AST retval;
  struct SolverType my_type;
  my_type.id = UNINSTANTIATED_TYPE;

  // at the moment, we only handle ite, so this is specialized
  // for that
  if (strcmp(name, "ite") == 0) {
    struct SolverType guard_type;
    guard_type.id = BOOLEAN_TYPE;
    // my type = left child type = right child type
    retval = mk_ternary(state, prolog_term,
			&Z3_mk_ite,
			&guard_type,
			expected_type,
			expected_type);
  } else {
    set_error(prolog_term, "unknown ternary operation", &retval);
  }

  return retval;
}

static struct AST handle_binary_op(struct TranslationState* state,
				   term_t prolog_term,
				   const char* name,
				   struct SolverType* expected_type) {
  struct AST retval;
  Z3_ast (*mk_op)(Z3_context, Z3_ast, Z3_ast);
  struct SolverType my_type;
  int error_occurred = 0;

  // we intentionally split this up because `distinct`
  // requires both parameters to be of the same type,
  // but it's polymorphic.  A trick is to leave the type
  // uninstantiated here, but use the same SolverType
  // for both sides.
  struct SolverType left_type_struct;
  struct SolverType right_type_struct;
  struct SolverType* left_type = &left_type_struct;
  struct SolverType* right_type = &right_type_struct;

  if (strcmp(name, "-") == 0) {
    my_type.id = INT_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &sub_wrapper;
  } else if (strcmp(name, "+") == 0) {
    my_type.id = INT_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &add_wrapper;
  } else if (strcmp(name, "*") == 0) {
    my_type.id = INT_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &mul_wrapper;
  } else if (strcmp(name, "div") == 0) {
    my_type.id = INT_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &Z3_mk_div;
  } else  if (strcmp(name, "mod") == 0) {
    my_type.id = INT_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &Z3_mk_mod;
  } else if (strcmp(name, "<=") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &Z3_mk_le;
  } else if (strcmp(name, "<") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &Z3_mk_lt;
  } else if (strcmp(name, ">=") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &Z3_mk_ge;
  } else if (strcmp(name, ">") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = INT_TYPE;
    right_type->id = INT_TYPE;
    mk_op = &Z3_mk_gt;
  } else if (strcmp(name, "=") == 0) {
    // polymorphic; both point to left
    my_type.id = BOOLEAN_TYPE;
    right_type = left_type;
    left_type->id = UNINSTANTIATED_TYPE;
    mk_op = &Z3_mk_eq;
  } else if (strcmp(name, "distinct") == 0) {
    // polymorphic; both point to left
    my_type.id = BOOLEAN_TYPE;
    right_type = left_type;
    left_type->id = UNINSTANTIATED_TYPE;
    mk_op = &distinct_wrapper;
  } else if (strcmp(name, "iff") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = BOOLEAN_TYPE;
    right_type->id = BOOLEAN_TYPE;
    mk_op = &Z3_mk_iff;
  } else if (strcmp(name, "implies") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = BOOLEAN_TYPE;
    right_type->id = BOOLEAN_TYPE;
    mk_op = &Z3_mk_implies;
  } else if (strcmp(name, "xor") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = BOOLEAN_TYPE;
    right_type->id = BOOLEAN_TYPE;
    mk_op = &Z3_mk_xor;
  } else if (strcmp(name, "and") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = BOOLEAN_TYPE;
    right_type->id = BOOLEAN_TYPE;
    mk_op = &and_wrapper;
  } else if (strcmp(name, "or") == 0) {
    my_type.id = BOOLEAN_TYPE;
    left_type->id = BOOLEAN_TYPE;
    right_type->id = BOOLEAN_TYPE;
    mk_op = &or_wrapper;
  } else {
    set_error(prolog_term, "unknown binary operation", &retval);
    error_occurred = 1;
  }

  if (!error_occurred) {
    if (!unify_types(expected_type, &my_type)) {
      set_smt_type_error(prolog_term, &retval);
    } else {
      retval = mk_binary(state, prolog_term, mk_op,
			 left_type, right_type);
    }
  }

  return retval;
} // handle_binary_op

static struct AST handle_unary_op(struct TranslationState* state,
				  term_t prolog_term,
				  const char* name,
				  struct SolverType* expected_type) {
  struct AST retval;
  Z3_ast (*mk_op)(Z3_context, Z3_ast);
  struct SolverType my_type;
  struct SolverType nested_type;
  int error_occurred = 0;

  if (strcmp(name, "-") == 0) {
    my_type.id = INT_TYPE;
    nested_type.id = INT_TYPE;
    mk_op = &Z3_mk_unary_minus;
  } else if (strcmp(name, "abs") == 0) {
    my_type.id = INT_TYPE;
    nested_type.id = INT_TYPE;
    mk_op = &abs_wrapper;
  } else if (strcmp(name, "not") == 0) {
    my_type.id = BOOLEAN_TYPE;
    nested_type.id = BOOLEAN_TYPE;
    mk_op = &abs_wrapper;
  } else if (strcmp(name, "int") == 0) {
    my_type.id = INT_TYPE;
    nested_type.id = INT_TYPE;
    mk_op = &forward_unary;
  } else if (strcmp(name, "bool") == 0) {
    my_type.id = BOOLEAN_TYPE;
    nested_type.id = BOOLEAN_TYPE;
    mk_op = &forward_unary;
  } else {
    set_error(prolog_term, "unknown unary operation", &retval);
    error_occurred = 1;
  }

  if (!error_occurred) {
    if (!unify_types(expected_type, &my_type)) {
      set_smt_type_error(prolog_term, &retval);
    } else {
      retval = mk_unary(state, prolog_term, mk_op,
			&nested_type);
    }
  }

  return retval;
} // handle_unary_op

static struct AST handle_compound_term(struct TranslationState* state,
				       term_t prolog_term,
				       struct SolverType* expected_type) {
  assert(PL_is_compound(prolog_term));
  atom_t atom_name;
  int arity;
  int ensure = PL_get_compound_name_arity(prolog_term,
					  &atom_name,
					  &arity);
  assert(ensure);

  struct AST retval;
  const char* name;
  size_t len;

  name = PL_atom_nchars(atom_name, &len);

  switch (arity) {
  case 1:
    retval = handle_unary_op(state, prolog_term, name,
			     expected_type);
    break;
  case 2:
    retval = handle_binary_op(state, prolog_term, name,
			      expected_type);
    break;
  case 3:
    retval = handle_ternary_op(state, prolog_term, name,
			       expected_type);
    break;
  default:
    set_error(prolog_term, "unknown SMT operation", &retval);
    break;
  } // switch (arity)

  return retval;
} // handle_compound_term

static struct AST handle_integer(struct TranslationState* state,
				 term_t prolog_integer,
				 struct SolverType* expected_type) {
  assert(PL_is_integer(prolog_integer));

  struct AST retval;
  struct SolverType inferred_type;
  int temp_int;
  int ensure = PL_get_integer(prolog_integer, &temp_int);
  assert(ensure);
  inferred_type.id = INT_TYPE;
  unify_types_set_ast(expected_type,
		      &inferred_type,
		      prolog_integer,
		      Z3_mk_int(state->context,
				temp_int,
				Z3_mk_int_sort(state->context)),
		      &retval);
  return retval;
}

static char* get_atom_name(term_t prolog_atom) {
  assert(PL_is_atom(prolog_atom));
  char* retval;
  int ensure = PL_get_atom_chars(prolog_atom, &retval);
  assert(ensure);
  return retval;
}

static struct AST handle_atom(struct TranslationState* state,
			      term_t prolog_atom,
			      struct SolverType* expected_type) {
  assert(PL_is_atom(prolog_atom));

  struct AST retval;
  struct SolverType inferred_type;
  char* my_name = get_atom_name(prolog_atom);

  if (strcmp(my_name, state->true_name) == 0) {
    inferred_type.id = BOOLEAN_TYPE;
    unify_types_set_ast(expected_type, &inferred_type,
			prolog_atom, Z3_mk_true(state->context),
			&retval);
  } else if (strcmp(my_name, state->false_name) == 0) {
    inferred_type.id = BOOLEAN_TYPE;
    unify_types_set_ast(expected_type, &inferred_type,
			prolog_atom, Z3_mk_false(state->context),
			&retval);
  } else {
    set_error(prolog_atom, "unknown constant", &retval);
  }

  return retval;
}
    
// returns the Z3 representation of the variable, or a type error
static struct AST handle_variable(struct TranslationState* state,
				  term_t prolog_variable,
				  struct SolverType* expected_type) {
  assert(PL_is_variable(prolog_variable));
  char* name;
  int ensure = PL_get_chars(prolog_variable, &name, CVT_VARIABLE);
  assert(ensure);

  // See if the variable already exists.  If so, try to use that.
  struct AST retval;
  struct VarMapEntry* existing_variable = get_variable(&(state->list), name);

  if (existing_variable != NULL) {
    // We already have variable.  Make sure the types work
    unify_types_set_ast(expected_type,
			&(existing_variable->solver_type),
			prolog_variable,
			existing_variable->z3_variable,
			&retval);
  } else {
    // introduce a new variable
    Z3_sort sort;
    if (get_sort_for_type(state->context, expected_type, &sort)) {
      struct VarMapEntry entry;
      Z3_ast ast = Z3_mk_const(state->context,
			       Z3_mk_string_symbol(state->context, name),
			       sort);
      entry.name = name;
      entry.prolog_variable = prolog_variable;
      entry.z3_variable = ast;
      entry.solver_type = *expected_type;
      prepend(entry, &(state->list));
      set_ast(ast, &retval);
    } else {
      set_error(prolog_variable, "Unknown SMT variable type", &retval);
    }
  }

  return retval;
}

static struct AST term_to_ast(struct TranslationState* state,
			      term_t term,
			      struct SolverType* expected_type) {
  struct AST retval;
  atom_t atom_name;
  int arity;
  size_t len;
  const char* name;
  int ensure;
  int error_occurred = 0;
  int type_error_occurred = 0;
  Z3_ast (*unary_op)(Z3_context, Z3_ast);
  Z3_ast (*binary_op)(Z3_context, Z3_ast, Z3_ast);
  struct SolverType inferred_type;
  inferred_type.id = UNINSTANTIATED_TYPE;

  switch (PL_term_type(term)) {
  case PL_VARIABLE:
    retval = handle_variable(state, term, expected_type);
    break;

  case PL_ATOM:
    retval = handle_atom(state, term, expected_type);
    break;

  case PL_INTEGER:
    retval = handle_integer(state, term, expected_type);
    break;

  case PL_TERM:
    retval = handle_compound_term(state, term, expected_type);
    break;
  default:
    set_error(term, "bad Prolog value", &retval);
    break;
  } // switch (PL_term_type)

  return retval;
} // term_to_ast

static void free_list(struct List* list) {
  struct Cons* cur = list->contents;
  while (cur != NULL) {
    struct Cons* next = cur->tail;
    free(cur);
    cur = next;
  }
}

static void apply_model_value(struct TranslationState* state,
			      struct VarMapEntry* variable,
			      Z3_ast value_ast) {
  int ensure;
  Z3_bool_opt z3_ensure;
  __int64 value_int;

  switch (variable->solver_type.id) {
  case BOOLEAN_TYPE:
    switch (Z3_get_bool_value(state->context, value_ast)) {
    case Z3_L_FALSE:
      ensure = PL_unify(variable->prolog_variable,
			state->map_false_to);
      assert(ensure);
      break;
    case Z3_L_UNDEF:
      assert(0);
      break;
    case Z3_L_TRUE:
      ensure = PL_unify(variable->prolog_variable,
			state->map_true_to);
      assert(ensure);
      break;
    default:
      assert(0);
      break;
    } // switch (bool value)
    break;
  case INT_TYPE:
    z3_ensure = Z3_get_numeral_int64(state->context,
				     value_ast,
				     &value_int);
    assert(z3_ensure == Z3_L_TRUE);
    ensure = PL_unify_int64(variable->prolog_variable,
			    value_int);
    assert(ensure);
    break;
  default:
    assert(0);
    break;
  } // switch (variable type)
} // apply_model_value
    
static void apply_model(struct TranslationState* state,
			Z3_model model) {
  struct Cons* cur = state->list.contents;
  while (cur != NULL) {
    Z3_ast value_ast;
    __int64 value_int;
    Z3_bool_opt ensure = Z3_model_eval(state->context,
				       model,
				       cur->head.z3_variable,
				       Z3_L_TRUE,
				       &value_ast);
    assert(ensure == Z3_L_TRUE);
    apply_model_value(state, &(cur->head), value_ast);
    cur = cur->tail;
  } // while cur != NULL
}

// returns non-zero if it's an atom, else 0
// and sets the given exception
static int ensure_atom(term_t should_be_atom,
		       term_t* exception) {
  if (!PL_is_atom(should_be_atom)) {
    *exception = make_type_error("must be an atom",
				 should_be_atom);
    return 0;
  }
  return 1;
}

// Returns non-zero if they are ok.
// Sets the given exception if they aren't
static int params_ok(term_t query,
		     term_t map_true_to,
		     term_t map_false_to,
		     foreign_t* exception) {
  if (!ensure_atom(map_true_to, exception) ||
      !ensure_atom(map_false_to, exception)) {
    return 0;
  }
  return 1;
}

// Only externally exposed function
static foreign_t z3_sat(term_t query,
			term_t map_true_to,
			term_t map_false_to) {
  int exception_occurred = 0;
  foreign_t exception;

  if (!params_ok(query,
		 map_true_to,
		 map_false_to,
		 &exception)) {
    return PL_raise_exception(exception);
  }

  foreign_t retval;

  struct TranslationState translation_state;
  Z3_config config = Z3_mk_config();
  translation_state.context = Z3_mk_context(config);
  mk_empty_list(&(translation_state.list));
  translation_state.map_true_to = map_true_to;
  translation_state.true_name = get_atom_name(map_true_to);
  translation_state.map_false_to = map_false_to;
  translation_state.false_name = get_atom_name(map_false_to);

  struct SolverType expected_type;
  expected_type.id = BOOLEAN_TYPE;
  struct AST ast = term_to_ast(&translation_state,
			       query,
			       &expected_type);

  if (ast.which == AST_TYPE) {
    term_t except;
    Z3_solver solver = Z3_mk_solver(translation_state.context);
    Z3_solver_inc_ref(translation_state.context, solver);
    int ensure;

    Z3_solver_assert(translation_state.context,
		     solver,
		     ast.value.ast);

    switch (Z3_solver_check(translation_state.context, solver)) {
    case Z3_L_FALSE:
      retval = FALSE;
      break;
    case Z3_L_UNDEF:
      except = make_type_error("Z3 failed on input", query);
      exception_occurred = 1;
      break;
    case Z3_L_TRUE:
      apply_model(&translation_state,
		  Z3_solver_get_model(translation_state.context,
				      solver));
      retval = TRUE;
      break;
    }
    Z3_solver_dec_ref(translation_state.context, solver);
  } else {
    exception_occurred = 1;
    exception = ast.value.exception;
  }

  free_list(&(translation_state.list));
  Z3_del_context(translation_state.context);
  Z3_del_config(config);

  if (exception_occurred) {
    // TODO: do we have to split things up like this?
    return PL_raise_exception(exception);
  } else {
    return retval;
  }
} // z3_sat

install_t install_z3(void) {
  PL_register_foreign("z3_sat", 3, z3_sat, 0);
}
