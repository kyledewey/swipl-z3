#include <SWI-Prolog.h>
#include <z3.h>
#include <string.h>

enum ASTType {
  AST_TYPE,
  EXCEPTION_TYPE
};

struct AST {
  union {
    Z3_ast ast;
    term_t exception;
  } value;
  ASTType which;
};

struct BinopResult {
  union {
    Z3_ast pair[2];
    term_t exception;
  } value;
  ASTType which;
};

static void set_ast(Z3_ast ast, struct AST* ast);
static void set_error(term_t term_with_error, char* message, struct AST* ast);
static Z3_ast add_wrapper(Z3_context context, Z3_ast left, Z3_ast right);
static Z3_ast sub_wrapper(Z3_context context, Z3_ast left, Z3_ast right);
static Z3_ast abs_wrapper(Z3_context context, Z3_ast around);
static void mk_unary(Z4_context context,
		     term_t holds_param,
		     Z3_ast (f)(Z3_context, Z3_ast),
		     struct AST* retval);
static void mk_binop(Z3_context context,
		     term_t holds_params,
		     Z3_ast (f)(Z3_context, Z3_ast, Z3_ast),
		     struct AST* retval);
static void binop_result_to_ast(Z3_context context,
				BinopResult result,
				Z3_ast (f)(Z3_context, Z3_ast, Z3_ast),
				struct AST* retval);
static BinopResult binop_result(Z3_context context, term_t term);
static struct AST term_to_ast(Z3_context context, term_t term);
static foreign_t z3_sat(term_t query);

// For the moment, we only care about the theory of integers

static void set_ast(Z3_ast ast, struct AST* ast) {
  retval.value.ast = ast;
  retval.which = AST_TYPE;
}

static void set_error(term_t term_with_error, char* message, struct AST* ast) {
  term_t except = PL_new_term_ref();
  PL_unify_term(except,
		PL_FUNCTOR_CHARS,
		"type_error",
		2,
		PL_CHARS, message,
		PL_TERM, term_with_error);
  retval.value.exception = except;
  retval.which = EXCEPTION_TYPE;
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

static Z3_ast abs_wrapper(Z3_context context, Z3_ast around) {
  // abs(x) = if (x < 0) -x else x
  return Z3_mk_ite(context,
		   Z3_mk_lt(context,
			    around,
			    mk_int(context, 0)),
		   Z3_mk_unary_minus(context, around),
		   around);
}

static void mk_unary(Z4_context context,
		     term_t holds_param,
		     Z3_ast (f)(Z3_context, Z3_ast),
		     struct AST* retval) {
  term_t nested_term = PL_new_term_ref();
  PL_get_arg(1, holds_param, nested_term);
  struct AST nested = term_to_ast(context, nested_term);
  if (nested.which == AST_TYPE) {
    set_ast(f(context, nested.value.ast), retval);
  } else {
    retval.value.exception = nested.value.exception;
    retval.which = EXCEPTION_TYPE;
  }
}

static void mk_binop(Z3_context context,
		     term_t holds_params,
		     Z3_ast (f)(Z3_context, Z3_ast, Z3_ast),
		     struct AST* retval) {
  BinopResult binop = binop_result(context, holds_params);
  binop_result_to_ast(context, binop, f, retval);
}

static void binop_result_to_ast(Z3_context context,
				BinopResult result,
				Z3_ast (f)(Z3_context, Z3_ast, Z3_ast),
				struct AST* retval) {
  if (result.which == AST_TYPE) {
    set_ast(f(context, result.value.pair[0], result.value.pair[1]), retval);
  } else {
    retval->which = EXCEPTION_TYPE;
    retval->value.exception = result.exception;
  }
}

static BinopResult binop_result(Z3_context context, term_t term) {
  BinopResult retval;

  term_t left_term = PL_new_term_ref();
  PL_get_arg(1, term, left_term);
  AST left = term_to_ast(context, left_term);
  if (left.which == AST) {
    term_t right_term = PL_new_term_ref();
    PL_get_arg(2, term, right_term);
    AST right = term_to_ast(context, right_term);
    if (right.which == AST) {
      retval.value.pair[0] = left;
      retval.value.pair[1] = right;
      retval.which = AST;
    } else {
      retval.value.exception = right.exception;
      retval.which = EXCEPTION;
    }
  } else {
    retval.value.exception = left.exception;
    retval.which = EXCEPTION;
  }

  return retval;
}
			 
static struct AST term_to_ast(Z3_context context, term_t term) {
  struct AST retval;

  switch (PL_term_type(term)) {
  case PL_INTEGER:
    int temp;
    PL_get_integer(term, &temp);
    set_ast(mk_int(context, temp), &retval);
    break;

  case PL_ATOM:
    // treat it as a variable
    char* temp;
    PL_get_atom_chars(term, &temp);
    set_ast(mk_int_var(context, temp), &retval);
    break;

  case PL_TERM:
    atom_t atom_name;
    size_t arity;
    PL_get_compound_name_arity(term, &name, &arity);
    size_t len;
    const char* name = PL_atom_nchars(atom_name, &len);

    switch (arity) {
    case 1:
      if (strcmp(name, "-")) {
	mk_unary(context, term, Z3_mk_unary_minus, &retval);
      } else if (strcmp(name, "abs")) {
	mk_unary(context, term, abs_wrapper, &retval);
      } else {
	set_error(term, "unknown unary operation", &retval);
      }
      break;
    case 2:
      if (strcmp(name, "-")) {
	mk_binop(context, term, Z3_sub_wrapper, &retval);
      } else if (strcmp(name, "+")) {
	mk_binop(context, term, Z3_add_wrapper, &retval);
      } else if (strcmp(name, "*")) {
	mk_binop(context, term, Z3_mk_mul, &retval);
      } else if (strcmp(name, "div")) {
	mk_binop(context, term, Z3_mk_div, &retval);
      } else if (strcmp(name, "mod")) {
	mk_binop(context, term, Z3_mk_mod, &retval);
      } else if (strcmp(name, "<=")) {
	mk_binop(context, term, Z3_mk_le, &retval);
      } else if (strcmp(name, "<")) {
	mk_binop(context, term, Z3_mk_lt, &retval);
      } else if (strcmp(name, ">=")) {
	mk_binop(context, term, Z3_mk_ge, &retval);
      } else if (strcmp(name, ">")) {
	mk_binop(context, term, Z3_mk_gt, &retval);
      } else {
	set_error(term, "unknown binary operation", &retval);
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


// Only externally exposed function
static foreign_t z3_sat(term_t query) {
  int exception_occurred = 0;
  foreign_t exception;
  foreign_t retval;
  Z3_config config = Z3_mk_config();
  Z3_context context = Z3_mk_context(config);
  
  struct AST ast = term_to_ast(context, query);
  if (ast.which == AST_TYPE) {
    Z3_solver solver = Z3_mk_solver(context);
    Z3_solver_assert(context, solver, ast.value.ast);
    switch (Z3_solver_check(context, solver)) {
    case Z3_L_FALSE:
      retval = FALSE;
      break;
    case Z3_L_UNDEF:
      term_t except = PL_new_term_ref();
      PL_unify_term(except,
		    PL_FUNCTOR_CHARS,
		    "type_error", // can probably do better
		    2,
		    PL_CHARS,
		    "Z3 failed on input",
		    query);
      exception_occurred = 1;
      break;
    case Z3_L_TRUE:
      retval = TRUE;
      break;
    }
    Z3_solver_dec_ref(context, solver);
  } else {
    exception_occurred = 1;
    exception = ast.value.exception;
  }

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
