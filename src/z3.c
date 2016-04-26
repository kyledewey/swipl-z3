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

struct BinopResult {
  union {
    Z3_ast pair[2];
    term_t exception;
  } value;
  enum ASTType which;
};

struct VarMapEntry {
  term_t prolog_variable;
  Z3_ast z3_variable;
};

struct Cons {
  struct VarMapEntry head;
  struct Cons* tail;
};

struct List {
  struct Cons* contents;
  unsigned int length;
};

static struct List* mk_empty_list(void);
static void prepend(struct VarMapEntry what, struct List* list);
static void free_list(struct List* list);

static void set_ast(Z3_ast ast, struct AST* retval);
static void set_error(term_t term_with_error, char* message, struct AST* ast);
static Z3_ast add_wrapper(Z3_context context, Z3_ast left, Z3_ast right);
static Z3_ast sub_wrapper(Z3_context context, Z3_ast left, Z3_ast right);
static Z3_ast mul_wrapper(Z3_context context, Z3_ast left, Z3_ast right);
static Z3_ast abs_wrapper(Z3_context context, Z3_ast around);
static void mk_unary(Z3_context context,
		     term_t holds_param,
		     Z3_ast (*f)(Z3_context, Z3_ast),
		     struct AST* retval,
		     struct List* list);
static void mk_binop(Z3_context context,
		     term_t holds_params,
		     Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast),
		     struct AST* retval,
		     struct List* list);
static void binop_result_to_ast(Z3_context context,
				struct BinopResult result,
				Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast),
				struct AST* retval);
static struct BinopResult binop_result(Z3_context context,
				       term_t term,
				       struct List* list);
static struct AST term_to_ast(Z3_context context,
			      term_t term,
			      struct List* list);
static foreign_t z3_sat(term_t query);

// For the moment, we only care about the theory of integers

struct List* mk_empty_list(void) {
  struct List* retval = malloc(sizeof(struct List));
  retval->contents = NULL;
  retval->length = 0;
  return retval;
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

static void set_error(term_t term_with_error, char* message, struct AST* retval) {
  int ensure;
  term_t except = PL_new_term_ref();
  ensure = PL_unify_term(except,
			 PL_FUNCTOR_CHARS,
			 "type_error",
			 2,
			 PL_CHARS, message,
			 PL_TERM, term_with_error);
  retval->value.exception = except;
  retval->which = EXCEPTION_TYPE;
}

static Z3_ast add_wrapper(Z3_context context, Z3_ast left, Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_add(context, 2, args);
}

static Z3_ast sub_wrapper(Z3_context context, Z3_ast left, Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_sub(context, 2, args);
}

static Z3_ast mul_wrapper(Z3_context context, Z3_ast left, Z3_ast right) {
  Z3_ast args[2];
  args[0] = left;
  args[1] = right;
  return Z3_mk_mul(context, 2, args);
}

static Z3_ast abs_wrapper(Z3_context context, Z3_ast around) {
  // abs(x) = if (x < 0) -x else x
  return Z3_mk_ite(context,
		   Z3_mk_lt(context,
			    around,
			    Z3_mk_int(context, 0, Z3_mk_int_sort(context))),
		   Z3_mk_unary_minus(context, around),
		   around);
}

static void mk_unary(Z3_context context,
		     term_t holds_param,
		     Z3_ast (*f)(Z3_context, Z3_ast),
		     struct AST* retval,
		     struct List* list) {
  int ensure;
  term_t nested_term = PL_new_term_ref();
  ensure = PL_get_arg(1, holds_param, nested_term);
  assert(ensure);
  struct AST nested = term_to_ast(context, nested_term, list);
  if (nested.which == AST_TYPE) {
    set_ast((*f)(context, nested.value.ast), retval);
  } else {
    retval->value.exception = nested.value.exception;
    retval->which = EXCEPTION_TYPE;
  }
}

static void mk_binop(Z3_context context,
		     term_t holds_params,
		     Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast),
		     struct AST* retval,
		     struct List* list) {
  struct BinopResult binop = binop_result(context, holds_params, list);
  binop_result_to_ast(context, binop, f, retval);
}

static void binop_result_to_ast(Z3_context context,
				struct BinopResult result,
				Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast),
				struct AST* retval) {
  if (result.which == AST_TYPE) {
    set_ast((*f)(context, result.value.pair[0], result.value.pair[1]), retval);
  } else {
    retval->which = EXCEPTION_TYPE;
    retval->value.exception = result.value.exception;
  }
}

static struct BinopResult binop_result(Z3_context context,
				       term_t term,
				       struct List* list) {
  struct BinopResult retval;
  int ensure;
  term_t left_term = PL_new_term_ref();
  ensure = PL_get_arg(1, term, left_term);
  assert(ensure);
  struct AST left = term_to_ast(context, left_term, list);
  if (left.which == AST_TYPE) {
    term_t right_term = PL_new_term_ref();
    ensure = PL_get_arg(2, term, right_term);
    assert(ensure);
    struct AST right = term_to_ast(context, right_term, list);
    if (right.which == AST_TYPE) {
      retval.value.pair[0] = left.value.ast;
      retval.value.pair[1] = right.value.ast;
      retval.which = AST_TYPE;
    } else {
      retval.value.exception = right.value.exception;
      retval.which = EXCEPTION_TYPE;
    }
  } else {
    retval.value.exception = left.value.exception;
    retval.which = EXCEPTION_TYPE;
  }

  return retval;
}

// returns the Z3 representation of the variable
static Z3_ast add_variable(Z3_context context,
			   term_t term,
			   struct List* list) {
  assert(PL_is_variable(term));
  char* name;
  int ensure = PL_get_chars(term, &name, CVT_VARIABLE);

  struct VarMapEntry entry;
  entry.prolog_variable = term;
  Z3_ast ast = Z3_mk_const(context,
			   Z3_mk_string_symbol(context, name),
			   Z3_mk_int_sort(context));
  entry.z3_variable = ast;
  prepend(entry, list);
  return ast;
}

static struct AST term_to_ast(Z3_context context,  // where to make terms
			      term_t term,         // term to convert
			      struct List* list) { // vars to terms
  struct AST retval;
  int temp_int;
  char* temp_string;
  atom_t atom_name;
  int arity;
  size_t len;
  const char* name;
  int ensure;
  int error_occurred = 0;
  char* printing;
  Z3_ast (*unary_op)(Z3_context, Z3_ast);
  Z3_ast (*binary_op)(Z3_context, Z3_ast, Z3_ast);

  switch (PL_term_type(term)) {
  case PL_VARIABLE:
    set_ast(add_variable(context, term, list), &retval);
    break;

  case PL_INTEGER:
    ensure = PL_get_integer(term, &temp_int);
    assert(ensure);
    set_ast(Z3_mk_int(context, temp_int, Z3_mk_int_sort(context)), &retval);
    break;

  case PL_TERM:
    ensure = PL_get_compound_name_arity(term, &atom_name, &arity);
    assert(ensure);
    name = PL_atom_nchars(atom_name, &len);

    switch (arity) {
    case 1:
      if (strcmp(name, "-") == 0) {
	unary_op = &Z3_mk_unary_minus;
      } else if (strcmp(name, "abs") == 0) {
	unary_op = &abs_wrapper;
      } else {
	set_error(term, "unknown unary operation", &retval);
	error_occurred = 1;
      }

      if (!error_occurred) {
	mk_unary(context, term, unary_op, &retval, list);
      }
      break;
    case 2:
      if (strcmp(name, "-") == 0) {
	binary_op = &sub_wrapper;
      } else if (strcmp(name, "+") == 0) {
	binary_op = &add_wrapper;
      } else if (strcmp(name, "*") == 0) {
	binary_op = &mul_wrapper;
      } else if (strcmp(name, "div") == 0) {
	binary_op = &Z3_mk_div;
      } else if (strcmp(name, "mod") == 0) {
	binary_op = &Z3_mk_mod;
      } else if (strcmp(name, "<=") == 0) {
	binary_op = &Z3_mk_le;
      } else if (strcmp(name, "<") == 0) {
	binary_op = &Z3_mk_lt;
      } else if (strcmp(name, ">=") == 0) {
	binary_op = &Z3_mk_ge;
      } else if (strcmp(name, ">") == 0) {
	binary_op = &Z3_mk_gt;
      } else {
	set_error(term, "unknown binary operation", &retval);
	error_occurred = 1;
      }

      if (!error_occurred) {
	mk_binop(context, term, binary_op, &retval, list);
      }
      break;

    default:
      set_error(term, "unknown operation", &retval);
      break;
    } // switch (arity)
    break;

  default:
    set_error(term, "invalid value", &retval);
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
  free(list);
}

static void apply_model(Z3_context context,
			Z3_model model,
			struct List* list) {
  struct Cons* cur = list->contents;
  while (cur != NULL) {
    Z3_ast value_ast;
    __int64 value_int;
    Z3_bool_opt ensure = Z3_model_eval(context,
				       model,
				       cur->head.z3_variable,
				       Z3_L_TRUE,
				       &value_ast);
    assert(ensure == Z3_L_TRUE);
    ensure = Z3_get_numeral_int64(context, value_ast, &value_int);
    assert(ensure == Z3_L_TRUE);
    int ensure_pl = PL_unify_int64(cur->head.prolog_variable, value_int);
    assert(ensure_pl);
    cur = cur->tail;
  }
}
    
// Only externally exposed function
static foreign_t z3_sat(term_t query) {
  int exception_occurred = 0;
  foreign_t exception;
  foreign_t retval;
  Z3_config config = Z3_mk_config();
  Z3_context context = Z3_mk_context(config);
  struct List* list = mk_empty_list();
  struct AST ast = term_to_ast(context, query, list);

  if (ast.which == AST_TYPE) {
    term_t except;
    Z3_solver solver = Z3_mk_solver(context);
    int ensure;

    Z3_solver_assert(context, solver, ast.value.ast);

    switch (Z3_solver_check(context, solver)) {
    case Z3_L_FALSE:
      retval = FALSE;
      break;
    case Z3_L_UNDEF:
      except = PL_new_term_ref();
      ensure = PL_unify_term(except,
			     PL_FUNCTOR_CHARS,
			     "type_error", // can probably do better
			     2,
			     PL_CHARS,
			     "Z3 failed on input",
			     query);
      assert(ensure);
      exception_occurred = 1;
      break;
    case Z3_L_TRUE:
      apply_model(context,
		  Z3_solver_get_model(context, solver),
		  list);
      retval = TRUE;
      break;
    }
    Z3_solver_dec_ref(context, solver);
  } else {
    exception_occurred = 1;
    exception = ast.value.exception;
  }

  free_list(list);
  Z3_del_context(context);
  Z3_del_config(config);

  if (exception_occurred) {
    // TODO: do we have to split things up like this?
    return PL_raise_exception(exception);
  } else {
    return retval;
  }
} // z3_sat

install_t install_z3(void) {
  PL_register_foreign("z3_sat", 1, z3_sat, 0);
}
