// Lean compiler output
// Module: Lean.Meta.Sym.InstantiateS
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.LooseBVarsS import Init.Grind
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__2;
static const lean_string_object l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Sym.InstantiateS"};
static const lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Sym.instantiateRevRangeS"};
static const lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__5;
static lean_once_cell_t l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRangeS'"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateAppS!"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRevBetaS'.visitAppBeta"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Meta.Sym.InstantiateS.0.Lean.Meta.Sym.instantiateRevBetaS'.visit"};
static const lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_object* v_00_u03b2_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(lean_object* v_idx_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = l_Lean_Expr_bvar___override(v_idx_6_);
v___x_9_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_8_, v___y_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(lean_object* v_idx_10_, uint8_t v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v_idx_10_, v___y_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(lean_object* v_idx_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
uint8_t v___y_22949__boxed_17_; lean_object* v_res_18_; 
v___y_22949__boxed_17_ = lean_unbox(v___y_15_);
v_res_18_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(v_idx_14_, v___y_22949__boxed_17_, v___y_16_);
return v_res_18_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(lean_object* v_msg_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_3189__overap_29_; lean_object* v___x_30_; 
v___x_28_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0, &l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0);
v___x_3189__overap_29_ = lean_panic_fn_borrowed(v___x_28_, v_msg_20_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
lean_inc(v___y_24_);
lean_inc_ref(v___y_23_);
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
v___x_30_ = lean_apply_7(v___x_3189__overap_29_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, lean_box(0));
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(lean_object* v_msg_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v_msg_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(lean_object* v_x_40_, uint8_t v_bi_41_, lean_object* v_t_42_, lean_object* v_b_43_, lean_object* v___y_44_, uint8_t v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___y_48_; lean_object* v___y_49_; 
if (v___y_45_ == 0)
{
v___y_48_ = v___y_44_;
v___y_49_ = v___y_46_;
goto v___jp_47_;
}
else
{
lean_object* v___x_62_; lean_object* v_snd_63_; lean_object* v___x_64_; lean_object* v_snd_65_; 
lean_inc_ref(v_t_42_);
v___x_62_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_42_, v___y_45_, v___y_46_);
v_snd_63_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_snd_63_);
lean_dec_ref(v___x_62_);
lean_inc_ref(v_b_43_);
v___x_64_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_43_, v___y_45_, v_snd_63_);
v_snd_65_ = lean_ctor_get(v___x_64_, 1);
lean_inc(v_snd_65_);
lean_dec_ref(v___x_64_);
v___y_48_ = v___y_44_;
v___y_49_ = v_snd_65_;
goto v___jp_47_;
}
v___jp_47_:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_fst_52_; lean_object* v_snd_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_61_; 
v___x_50_ = l_Lean_Expr_forallE___override(v_x_40_, v_t_42_, v_b_43_, v_bi_41_);
v___x_51_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_50_, v___y_49_);
v_fst_52_ = lean_ctor_get(v___x_51_, 0);
v_snd_53_ = lean_ctor_get(v___x_51_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_61_ == 0)
{
v___x_55_ = v___x_51_;
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_snd_53_);
lean_inc(v_fst_52_);
lean_dec(v___x_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_61_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v___y_48_);
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_fst_52_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___y_48_);
v___x_58_ = v_reuseFailAlloc_60_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; 
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v_snd_53_);
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(lean_object* v_x_66_, lean_object* v_bi_67_, lean_object* v_t_68_, lean_object* v_b_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
uint8_t v_bi_boxed_73_; uint8_t v___y_22986__boxed_74_; lean_object* v_res_75_; 
v_bi_boxed_73_ = lean_unbox(v_bi_67_);
v___y_22986__boxed_74_ = lean_unbox(v___y_71_);
v_res_75_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_x_66_, v_bi_boxed_73_, v_t_68_, v_b_69_, v___y_70_, v___y_22986__boxed_74_, v___y_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(lean_object* v_msg_83_, lean_object* v___y_84_, uint8_t v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_22615__overap_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___f_87_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
v___f_88_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
v___f_89_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
v___f_90_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
v___f_91_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
v___f_92_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
v___f_93_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___f_87_);
lean_ctor_set(v___x_94_, 1, v___f_88_);
v___x_95_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___f_89_);
lean_ctor_set(v___x_95_, 2, v___f_90_);
lean_ctor_set(v___x_95_, 3, v___f_91_);
lean_ctor_set(v___x_95_, 4, v___f_92_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___f_93_);
lean_inc_ref(v___x_96_);
v___f_97_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_97_, 0, v___x_96_);
lean_inc_ref(v___x_96_);
v___f_98_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_98_, 0, v___x_96_);
lean_inc_ref(v___x_96_);
v___f_99_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_99_, 0, v___x_96_);
lean_inc_ref(v___x_96_);
v___f_100_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_100_, 0, v___x_96_);
lean_inc_ref(v___x_96_);
v___x_101_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_101_, 0, lean_box(0));
lean_closure_set(v___x_101_, 1, lean_box(0));
lean_closure_set(v___x_101_, 2, v___x_96_);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___f_97_);
lean_inc_ref(v___x_96_);
v___x_103_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_103_, 0, lean_box(0));
lean_closure_set(v___x_103_, 1, lean_box(0));
lean_closure_set(v___x_103_, 2, v___x_96_);
v___x_104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
lean_ctor_set(v___x_104_, 2, v___f_98_);
lean_ctor_set(v___x_104_, 3, v___f_99_);
lean_ctor_set(v___x_104_, 4, v___f_100_);
v___x_105_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_105_, 0, lean_box(0));
lean_closure_set(v___x_105_, 1, lean_box(0));
lean_closure_set(v___x_105_, 2, v___x_96_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = l_ReaderT_instMonad___redArg(v___x_106_);
lean_inc_ref(v___x_107_);
v___f_108_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_108_, 0, v___x_107_);
lean_inc_ref(v___x_107_);
v___f_109_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_109_, 0, v___x_107_);
lean_inc_ref(v___x_107_);
v___f_110_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_110_, 0, v___x_107_);
lean_inc_ref(v___x_107_);
v___f_111_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_111_, 0, v___x_107_);
lean_inc_ref(v___x_107_);
v___x_112_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_112_, 0, lean_box(0));
lean_closure_set(v___x_112_, 1, lean_box(0));
lean_closure_set(v___x_112_, 2, v___x_107_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___f_108_);
lean_inc_ref(v___x_107_);
v___x_114_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_114_, 0, lean_box(0));
lean_closure_set(v___x_114_, 1, lean_box(0));
lean_closure_set(v___x_114_, 2, v___x_107_);
v___x_115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
lean_ctor_set(v___x_115_, 2, v___f_109_);
lean_ctor_set(v___x_115_, 3, v___f_110_);
lean_ctor_set(v___x_115_, 4, v___f_111_);
v___x_116_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_116_, 0, lean_box(0));
lean_closure_set(v___x_116_, 1, lean_box(0));
lean_closure_set(v___x_116_, 2, v___x_107_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = l_Lean_instInhabitedExpr;
v___x_119_ = l_instInhabitedOfMonad___redArg(v___x_117_, v___x_118_);
v___x_22615__overap_120_ = lean_panic_fn_borrowed(v___x_119_, v_msg_83_);
lean_dec(v___x_119_);
v___x_121_ = lean_box(v___y_85_);
v___x_122_ = lean_apply_3(v___x_22615__overap_120_, v___y_84_, v___x_121_, v___y_86_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v___y_23049__boxed_127_; lean_object* v_res_128_; 
v___y_23049__boxed_127_ = lean_unbox(v___y_125_);
v_res_128_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v_msg_123_, v___y_124_, v___y_23049__boxed_127_, v___y_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(lean_object* v_structName_129_, lean_object* v_idx_130_, lean_object* v_struct_131_, lean_object* v___y_132_, uint8_t v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___y_136_; lean_object* v___y_137_; 
if (v___y_133_ == 0)
{
v___y_136_ = v___y_132_;
v___y_137_ = v___y_134_;
goto v___jp_135_;
}
else
{
lean_object* v___x_150_; lean_object* v_snd_151_; 
lean_inc_ref(v_struct_131_);
v___x_150_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_131_, v___y_133_, v___y_134_);
v_snd_151_ = lean_ctor_get(v___x_150_, 1);
lean_inc(v_snd_151_);
lean_dec_ref(v___x_150_);
v___y_136_ = v___y_132_;
v___y_137_ = v_snd_151_;
goto v___jp_135_;
}
v___jp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
v___x_138_ = l_Lean_Expr_proj___override(v_structName_129_, v_idx_130_, v_struct_131_);
v___x_139_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_138_, v___y_137_);
v_fst_140_ = lean_ctor_get(v___x_139_, 0);
v_snd_141_ = lean_ctor_get(v___x_139_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v___x_139_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_snd_141_);
lean_inc(v_fst_140_);
lean_dec(v___x_139_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___y_136_);
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_fst_140_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___y_136_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_snd_141_);
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(lean_object* v_structName_152_, lean_object* v_idx_153_, lean_object* v_struct_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v___y_23135__boxed_158_; lean_object* v_res_159_; 
v___y_23135__boxed_158_ = lean_unbox(v___y_156_);
v_res_159_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_structName_152_, v_idx_153_, v_struct_154_, v___y_155_, v___y_23135__boxed_158_, v___y_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(lean_object* v_x_160_, uint8_t v_bi_161_, lean_object* v_t_162_, lean_object* v_b_163_, lean_object* v___y_164_, uint8_t v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___y_168_; lean_object* v___y_169_; 
if (v___y_165_ == 0)
{
v___y_168_ = v___y_164_;
v___y_169_ = v___y_166_;
goto v___jp_167_;
}
else
{
lean_object* v___x_182_; lean_object* v_snd_183_; lean_object* v___x_184_; lean_object* v_snd_185_; 
lean_inc_ref(v_t_162_);
v___x_182_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_162_, v___y_165_, v___y_166_);
v_snd_183_ = lean_ctor_get(v___x_182_, 1);
lean_inc(v_snd_183_);
lean_dec_ref(v___x_182_);
lean_inc_ref(v_b_163_);
v___x_184_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_163_, v___y_165_, v_snd_183_);
v_snd_185_ = lean_ctor_get(v___x_184_, 1);
lean_inc(v_snd_185_);
lean_dec_ref(v___x_184_);
v___y_168_ = v___y_164_;
v___y_169_ = v_snd_185_;
goto v___jp_167_;
}
v___jp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v___x_170_ = l_Lean_Expr_lam___override(v_x_160_, v_t_162_, v_b_163_, v_bi_161_);
v___x_171_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_170_, v___y_169_);
v_fst_172_ = lean_ctor_get(v___x_171_, 0);
v_snd_173_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_171_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snd_173_);
lean_inc(v_fst_172_);
lean_dec(v___x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___y_168_);
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_fst_172_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___y_168_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v_snd_173_);
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(lean_object* v_x_186_, lean_object* v_bi_187_, lean_object* v_t_188_, lean_object* v_b_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v_bi_boxed_193_; uint8_t v___y_23179__boxed_194_; lean_object* v_res_195_; 
v_bi_boxed_193_ = lean_unbox(v_bi_187_);
v___y_23179__boxed_194_ = lean_unbox(v___y_191_);
v_res_195_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_x_186_, v_bi_boxed_193_, v_t_188_, v_b_189_, v___y_190_, v___y_23179__boxed_194_, v___y_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(lean_object* v_d_196_, lean_object* v_e_197_, lean_object* v___y_198_, uint8_t v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___y_202_; lean_object* v___y_203_; 
if (v___y_199_ == 0)
{
v___y_202_ = v___y_198_;
v___y_203_ = v___y_200_;
goto v___jp_201_;
}
else
{
lean_object* v___x_216_; lean_object* v_snd_217_; 
lean_inc_ref(v_e_197_);
v___x_216_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_197_, v___y_199_, v___y_200_);
v_snd_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_snd_217_);
lean_dec_ref(v___x_216_);
v___y_202_ = v___y_198_;
v___y_203_ = v_snd_217_;
goto v___jp_201_;
}
v___jp_201_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_fst_206_; lean_object* v_snd_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v___x_204_ = l_Lean_Expr_mdata___override(v_d_196_, v_e_197_);
v___x_205_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_204_, v___y_203_);
v_fst_206_ = lean_ctor_get(v___x_205_, 0);
v_snd_207_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snd_207_);
lean_inc(v_fst_206_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___y_202_);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___y_202_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v_snd_207_);
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(lean_object* v_d_218_, lean_object* v_e_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v___y_23228__boxed_223_; lean_object* v_res_224_; 
v___y_23228__boxed_223_ = lean_unbox(v___y_221_);
v_res_224_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_d_218_, v_e_219_, v___y_220_, v___y_23228__boxed_223_, v___y_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(lean_object* v_a_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v_key_228_; lean_object* v_value_229_; lean_object* v_tail_230_; uint8_t v___y_232_; lean_object* v_fst_235_; lean_object* v_snd_236_; lean_object* v_fst_237_; lean_object* v_snd_238_; uint8_t v___x_239_; 
v_key_228_ = lean_ctor_get(v_x_226_, 0);
v_value_229_ = lean_ctor_get(v_x_226_, 1);
v_tail_230_ = lean_ctor_get(v_x_226_, 2);
v_fst_235_ = lean_ctor_get(v_key_228_, 0);
v_snd_236_ = lean_ctor_get(v_key_228_, 1);
v_fst_237_ = lean_ctor_get(v_a_225_, 0);
v_snd_238_ = lean_ctor_get(v_a_225_, 1);
v___x_239_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_235_, v_fst_237_);
if (v___x_239_ == 0)
{
v___y_232_ = v___x_239_;
goto v___jp_231_;
}
else
{
uint8_t v___x_240_; 
v___x_240_ = lean_nat_dec_eq(v_snd_236_, v_snd_238_);
v___y_232_ = v___x_240_;
goto v___jp_231_;
}
v___jp_231_:
{
if (v___y_232_ == 0)
{
v_x_226_ = v_tail_230_;
goto _start;
}
else
{
lean_object* v___x_234_; 
lean_inc(v_value_229_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v_value_229_);
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(lean_object* v_a_241_, lean_object* v_x_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_241_, v_x_242_);
lean_dec(v_x_242_);
lean_dec_ref(v_a_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(lean_object* v_m_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_buckets_246_; lean_object* v_fst_247_; lean_object* v_snd_248_; lean_object* v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v_fold_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_buckets_246_ = lean_ctor_get(v_m_244_, 1);
v_fst_247_ = lean_ctor_get(v_a_245_, 0);
v_snd_248_ = lean_ctor_get(v_a_245_, 1);
v___x_249_ = lean_array_get_size(v_buckets_246_);
v___x_250_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_247_);
v___x_251_ = lean_uint64_of_nat(v_snd_248_);
v___x_252_ = lean_uint64_mix_hash(v___x_250_, v___x_251_);
v___x_253_ = 32ULL;
v___x_254_ = lean_uint64_shift_right(v___x_252_, v___x_253_);
v_fold_255_ = lean_uint64_xor(v___x_252_, v___x_254_);
v___x_256_ = 16ULL;
v___x_257_ = lean_uint64_shift_right(v_fold_255_, v___x_256_);
v___x_258_ = lean_uint64_xor(v_fold_255_, v___x_257_);
v___x_259_ = lean_uint64_to_usize(v___x_258_);
v___x_260_ = lean_usize_of_nat(v___x_249_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_sub(v___x_260_, v___x_261_);
v___x_263_ = lean_usize_land(v___x_259_, v___x_262_);
v___x_264_ = lean_array_uget_borrowed(v_buckets_246_, v___x_263_);
v___x_265_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_245_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_m_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_266_, v_a_267_);
lean_dec_ref(v_a_267_);
lean_dec_ref(v_m_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(lean_object* v_f_269_, lean_object* v_a_270_, lean_object* v___y_271_, uint8_t v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___y_275_; lean_object* v___y_276_; 
if (v___y_272_ == 0)
{
v___y_275_ = v___y_271_;
v___y_276_ = v___y_273_;
goto v___jp_274_;
}
else
{
lean_object* v___x_289_; lean_object* v_snd_290_; lean_object* v___x_291_; lean_object* v_snd_292_; 
lean_inc_ref(v_f_269_);
v___x_289_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_269_, v___y_272_, v___y_273_);
v_snd_290_ = lean_ctor_get(v___x_289_, 1);
lean_inc(v_snd_290_);
lean_dec_ref(v___x_289_);
lean_inc_ref(v_a_270_);
v___x_291_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_270_, v___y_272_, v_snd_290_);
v_snd_292_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_snd_292_);
lean_dec_ref(v___x_291_);
v___y_275_ = v___y_271_;
v___y_276_ = v_snd_292_;
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
v___x_277_ = l_Lean_Expr_app___override(v_f_269_, v_a_270_);
v___x_278_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_277_, v___y_276_);
v_fst_279_ = lean_ctor_get(v___x_278_, 0);
v_snd_280_ = lean_ctor_get(v___x_278_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_288_ == 0)
{
v___x_282_ = v___x_278_;
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_snd_280_);
lean_inc(v_fst_279_);
lean_dec(v___x_278_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_288_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___y_275_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_fst_279_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___y_275_);
v___x_285_ = v_reuseFailAlloc_287_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v_snd_280_);
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(lean_object* v_f_293_, lean_object* v_a_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___y_23341__boxed_298_; lean_object* v_res_299_; 
v___y_23341__boxed_298_ = lean_unbox(v___y_296_);
v_res_299_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_f_293_, v_a_294_, v___y_295_, v___y_23341__boxed_298_, v___y_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(lean_object* v_x_300_, lean_object* v_t_301_, lean_object* v_v_302_, lean_object* v_b_303_, uint8_t v_nondep_304_, lean_object* v___y_305_, uint8_t v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___y_309_; lean_object* v___y_310_; 
if (v___y_306_ == 0)
{
v___y_309_ = v___y_305_;
v___y_310_ = v___y_307_;
goto v___jp_308_;
}
else
{
lean_object* v___x_323_; lean_object* v_snd_324_; lean_object* v___x_325_; lean_object* v_snd_326_; lean_object* v___x_327_; lean_object* v_snd_328_; 
lean_inc_ref(v_t_301_);
v___x_323_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_301_, v___y_306_, v___y_307_);
v_snd_324_ = lean_ctor_get(v___x_323_, 1);
lean_inc(v_snd_324_);
lean_dec_ref(v___x_323_);
lean_inc_ref(v_v_302_);
v___x_325_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_302_, v___y_306_, v_snd_324_);
v_snd_326_ = lean_ctor_get(v___x_325_, 1);
lean_inc(v_snd_326_);
lean_dec_ref(v___x_325_);
lean_inc_ref(v_b_303_);
v___x_327_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_303_, v___y_306_, v_snd_326_);
v_snd_328_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_snd_328_);
lean_dec_ref(v___x_327_);
v___y_309_ = v___y_305_;
v___y_310_ = v_snd_328_;
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_fst_313_; lean_object* v_snd_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v___x_311_ = l_Lean_Expr_letE___override(v_x_300_, v_t_301_, v_v_302_, v_b_303_, v_nondep_304_);
v___x_312_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_311_, v___y_310_);
v_fst_313_ = lean_ctor_get(v___x_312_, 0);
v_snd_314_ = lean_ctor_get(v___x_312_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_322_ == 0)
{
v___x_316_ = v___x_312_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_snd_314_);
lean_inc(v_fst_313_);
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v___y_309_);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_fst_313_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___y_309_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_snd_314_);
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(lean_object* v_x_329_, lean_object* v_t_330_, lean_object* v_v_331_, lean_object* v_b_332_, lean_object* v_nondep_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
uint8_t v_nondep_boxed_337_; uint8_t v___y_23390__boxed_338_; lean_object* v_res_339_; 
v_nondep_boxed_337_ = lean_unbox(v_nondep_333_);
v___y_23390__boxed_338_ = lean_unbox(v___y_335_);
v_res_339_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_x_329_, v_t_330_, v_v_331_, v_b_332_, v_nondep_boxed_337_, v___y_334_, v___y_23390__boxed_338_, v___y_336_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_344_ = lean_unsigned_to_nat(67u);
v___x_345_ = lean_unsigned_to_nat(35u);
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1));
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0));
v___x_348_ = l_mkPanicMessageWithDecl(v___x_347_, v___x_346_, v___x_345_, v___x_344_, v___x_343_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(lean_object* v_beginIdx_349_, lean_object* v_n_350_, lean_object* v_subst_351_, lean_object* v_e_352_, lean_object* v_offset_353_, lean_object* v_a_354_, uint8_t v_a_355_, lean_object* v_a_356_){
_start:
{
switch(lean_obj_tag(v_e_352_))
{
case 5:
{
lean_object* v_fn_357_; lean_object* v_arg_358_; lean_object* v___x_359_; lean_object* v_fst_360_; lean_object* v_snd_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_364_; lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_387_; 
v_fn_357_ = lean_ctor_get(v_e_352_, 0);
v_arg_358_ = lean_ctor_get(v_e_352_, 1);
lean_inc(v_offset_353_);
lean_inc_ref(v_fn_357_);
v___x_359_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_fn_357_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_fst_360_);
v_snd_361_ = lean_ctor_get(v___x_359_, 1);
lean_inc(v_snd_361_);
lean_dec_ref(v___x_359_);
v_fst_362_ = lean_ctor_get(v_fst_360_, 0);
lean_inc(v_fst_362_);
v_snd_363_ = lean_ctor_get(v_fst_360_, 1);
lean_inc(v_snd_363_);
lean_dec(v_fst_360_);
lean_inc_ref(v_arg_358_);
v___x_364_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_arg_358_, v_offset_353_, v_snd_363_, v_a_355_, v_snd_361_);
v_fst_365_ = lean_ctor_get(v___x_364_, 0);
v_snd_366_ = lean_ctor_get(v___x_364_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_387_ == 0)
{
v___x_368_ = v___x_364_;
v_isShared_369_ = v_isSharedCheck_387_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_366_);
lean_inc(v_fst_365_);
lean_dec(v___x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_387_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_fst_370_; lean_object* v_snd_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_386_; 
v_fst_370_ = lean_ctor_get(v_fst_365_, 0);
v_snd_371_ = lean_ctor_get(v_fst_365_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_fst_365_);
if (v_isSharedCheck_386_ == 0)
{
v___x_373_ = v_fst_365_;
v_isShared_374_ = v_isSharedCheck_386_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_snd_371_);
lean_inc(v_fst_370_);
lean_dec(v_fst_365_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_386_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
uint8_t v___y_376_; uint8_t v___x_384_; 
v___x_384_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_357_, v_fst_362_);
if (v___x_384_ == 0)
{
v___y_376_ = v___x_384_;
goto v___jp_375_;
}
else
{
uint8_t v___x_385_; 
v___x_385_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_358_, v_fst_370_);
v___y_376_ = v___x_385_;
goto v___jp_375_;
}
v___jp_375_:
{
if (v___y_376_ == 0)
{
lean_object* v___x_377_; 
lean_del_object(v___x_373_);
lean_del_object(v___x_368_);
lean_dec_ref(v_e_352_);
v___x_377_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_362_, v_fst_370_, v_snd_371_, v_a_355_, v_snd_366_);
return v___x_377_;
}
else
{
lean_object* v___x_379_; 
lean_dec(v_fst_370_);
lean_dec(v_fst_362_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v_e_352_);
v___x_379_ = v___x_373_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_snd_371_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_379_);
v___x_381_ = v___x_368_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_snd_366_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_388_; lean_object* v_binderType_389_; lean_object* v_body_390_; uint8_t v_binderInfo_391_; lean_object* v___x_392_; lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_fst_400_; lean_object* v_snd_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_422_; 
v_binderName_388_ = lean_ctor_get(v_e_352_, 0);
v_binderType_389_ = lean_ctor_get(v_e_352_, 1);
v_body_390_ = lean_ctor_get(v_e_352_, 2);
v_binderInfo_391_ = lean_ctor_get_uint8(v_e_352_, sizeof(void*)*3 + 8);
lean_inc(v_offset_353_);
lean_inc_ref(v_binderType_389_);
v___x_392_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_binderType_389_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_fst_393_);
v_snd_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_snd_394_);
lean_dec_ref(v___x_392_);
v_fst_395_ = lean_ctor_get(v_fst_393_, 0);
lean_inc(v_fst_395_);
v_snd_396_ = lean_ctor_get(v_fst_393_, 1);
lean_inc(v_snd_396_);
lean_dec(v_fst_393_);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_offset_353_, v___x_397_);
lean_dec(v_offset_353_);
lean_inc_ref(v_body_390_);
v___x_399_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_body_390_, v___x_398_, v_snd_396_, v_a_355_, v_snd_394_);
v_fst_400_ = lean_ctor_get(v___x_399_, 0);
v_snd_401_ = lean_ctor_get(v___x_399_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_422_ == 0)
{
v___x_403_ = v___x_399_;
v_isShared_404_ = v_isSharedCheck_422_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_snd_401_);
lean_inc(v_fst_400_);
lean_dec(v___x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_422_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_fst_405_; lean_object* v_snd_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_421_; 
v_fst_405_ = lean_ctor_get(v_fst_400_, 0);
v_snd_406_ = lean_ctor_get(v_fst_400_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_fst_400_);
if (v_isSharedCheck_421_ == 0)
{
v___x_408_ = v_fst_400_;
v_isShared_409_ = v_isSharedCheck_421_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_snd_406_);
lean_inc(v_fst_405_);
lean_dec(v_fst_400_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_421_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
uint8_t v___y_411_; uint8_t v___x_419_; 
v___x_419_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_389_, v_fst_395_);
if (v___x_419_ == 0)
{
v___y_411_ = v___x_419_;
goto v___jp_410_;
}
else
{
uint8_t v___x_420_; 
v___x_420_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_390_, v_fst_405_);
v___y_411_ = v___x_420_;
goto v___jp_410_;
}
v___jp_410_:
{
if (v___y_411_ == 0)
{
lean_object* v___x_412_; 
lean_inc(v_binderName_388_);
lean_del_object(v___x_408_);
lean_del_object(v___x_403_);
lean_dec_ref(v_e_352_);
v___x_412_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_388_, v_binderInfo_391_, v_fst_395_, v_fst_405_, v_snd_406_, v_a_355_, v_snd_401_);
return v___x_412_;
}
else
{
lean_object* v___x_414_; 
lean_dec(v_fst_405_);
lean_dec(v_fst_395_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v_e_352_);
v___x_414_ = v___x_408_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_snd_406_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_414_);
v___x_416_ = v___x_403_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_snd_401_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_423_; lean_object* v_binderType_424_; lean_object* v_body_425_; uint8_t v_binderInfo_426_; lean_object* v___x_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_457_; 
v_binderName_423_ = lean_ctor_get(v_e_352_, 0);
v_binderType_424_ = lean_ctor_get(v_e_352_, 1);
v_body_425_ = lean_ctor_get(v_e_352_, 2);
v_binderInfo_426_ = lean_ctor_get_uint8(v_e_352_, sizeof(void*)*3 + 8);
lean_inc(v_offset_353_);
lean_inc_ref(v_binderType_424_);
v___x_427_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_binderType_424_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_fst_428_);
v_snd_429_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_snd_429_);
lean_dec_ref(v___x_427_);
v_fst_430_ = lean_ctor_get(v_fst_428_, 0);
lean_inc(v_fst_430_);
v_snd_431_ = lean_ctor_get(v_fst_428_, 1);
lean_inc(v_snd_431_);
lean_dec(v_fst_428_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_add(v_offset_353_, v___x_432_);
lean_dec(v_offset_353_);
lean_inc_ref(v_body_425_);
v___x_434_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_body_425_, v___x_433_, v_snd_431_, v_a_355_, v_snd_429_);
v_fst_435_ = lean_ctor_get(v___x_434_, 0);
v_snd_436_ = lean_ctor_get(v___x_434_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_457_ == 0)
{
v___x_438_ = v___x_434_;
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_snd_436_);
lean_inc(v_fst_435_);
lean_dec(v___x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_456_; 
v_fst_440_ = lean_ctor_get(v_fst_435_, 0);
v_snd_441_ = lean_ctor_get(v_fst_435_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_fst_435_);
if (v_isSharedCheck_456_ == 0)
{
v___x_443_ = v_fst_435_;
v_isShared_444_ = v_isSharedCheck_456_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_441_);
lean_inc(v_fst_440_);
lean_dec(v_fst_435_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_456_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
uint8_t v___y_446_; uint8_t v___x_454_; 
v___x_454_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_424_, v_fst_430_);
if (v___x_454_ == 0)
{
v___y_446_ = v___x_454_;
goto v___jp_445_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_425_, v_fst_440_);
v___y_446_ = v___x_455_;
goto v___jp_445_;
}
v___jp_445_:
{
if (v___y_446_ == 0)
{
lean_object* v___x_447_; 
lean_inc(v_binderName_423_);
lean_del_object(v___x_443_);
lean_del_object(v___x_438_);
lean_dec_ref(v_e_352_);
v___x_447_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_423_, v_binderInfo_426_, v_fst_430_, v_fst_440_, v_snd_441_, v_a_355_, v_snd_436_);
return v___x_447_;
}
else
{
lean_object* v___x_449_; 
lean_dec(v_fst_440_);
lean_dec(v_fst_430_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_e_352_);
v___x_449_ = v___x_443_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_snd_441_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_449_);
v___x_451_ = v___x_438_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_snd_436_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_458_; lean_object* v_type_459_; lean_object* v_value_460_; lean_object* v_body_461_; uint8_t v_nondep_462_; lean_object* v___x_463_; lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_468_; lean_object* v_fst_469_; lean_object* v_snd_470_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_fst_476_; lean_object* v_snd_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_500_; 
v_declName_458_ = lean_ctor_get(v_e_352_, 0);
v_type_459_ = lean_ctor_get(v_e_352_, 1);
v_value_460_ = lean_ctor_get(v_e_352_, 2);
v_body_461_ = lean_ctor_get(v_e_352_, 3);
v_nondep_462_ = lean_ctor_get_uint8(v_e_352_, sizeof(void*)*4 + 8);
lean_inc(v_offset_353_);
lean_inc_ref(v_type_459_);
v___x_463_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_type_459_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_fst_464_);
v_snd_465_ = lean_ctor_get(v___x_463_, 1);
lean_inc(v_snd_465_);
lean_dec_ref(v___x_463_);
v_fst_466_ = lean_ctor_get(v_fst_464_, 0);
lean_inc(v_fst_466_);
v_snd_467_ = lean_ctor_get(v_fst_464_, 1);
lean_inc(v_snd_467_);
lean_dec(v_fst_464_);
lean_inc(v_offset_353_);
lean_inc_ref(v_value_460_);
v___x_468_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_value_460_, v_offset_353_, v_snd_467_, v_a_355_, v_snd_465_);
v_fst_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_fst_469_);
v_snd_470_ = lean_ctor_get(v___x_468_, 1);
lean_inc(v_snd_470_);
lean_dec_ref(v___x_468_);
v_fst_471_ = lean_ctor_get(v_fst_469_, 0);
lean_inc(v_fst_471_);
v_snd_472_ = lean_ctor_get(v_fst_469_, 1);
lean_inc(v_snd_472_);
lean_dec(v_fst_469_);
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_offset_353_, v___x_473_);
lean_dec(v_offset_353_);
lean_inc_ref(v_body_461_);
v___x_475_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_body_461_, v___x_474_, v_snd_472_, v_a_355_, v_snd_470_);
v_fst_476_ = lean_ctor_get(v___x_475_, 0);
v_snd_477_ = lean_ctor_get(v___x_475_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_500_ == 0)
{
v___x_479_ = v___x_475_;
v_isShared_480_ = v_isSharedCheck_500_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snd_477_);
lean_inc(v_fst_476_);
lean_dec(v___x_475_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_500_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_499_; 
v_fst_481_ = lean_ctor_get(v_fst_476_, 0);
v_snd_482_ = lean_ctor_get(v_fst_476_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_fst_476_);
if (v_isSharedCheck_499_ == 0)
{
v___x_484_ = v_fst_476_;
v_isShared_485_ = v_isSharedCheck_499_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snd_482_);
lean_inc(v_fst_481_);
lean_dec(v_fst_476_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_499_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___y_487_; uint8_t v___x_497_; 
v___x_497_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_459_, v_fst_466_);
if (v___x_497_ == 0)
{
v___y_487_ = v___x_497_;
goto v___jp_486_;
}
else
{
uint8_t v___x_498_; 
v___x_498_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_460_, v_fst_471_);
v___y_487_ = v___x_498_;
goto v___jp_486_;
}
v___jp_486_:
{
if (v___y_487_ == 0)
{
lean_object* v___x_488_; 
lean_inc(v_declName_458_);
lean_del_object(v___x_484_);
lean_del_object(v___x_479_);
lean_dec_ref(v_e_352_);
v___x_488_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_458_, v_fst_466_, v_fst_471_, v_fst_481_, v_nondep_462_, v_snd_482_, v_a_355_, v_snd_477_);
return v___x_488_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_461_, v_fst_481_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_inc(v_declName_458_);
lean_del_object(v___x_484_);
lean_del_object(v___x_479_);
lean_dec_ref(v_e_352_);
v___x_490_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_458_, v_fst_466_, v_fst_471_, v_fst_481_, v_nondep_462_, v_snd_482_, v_a_355_, v_snd_477_);
return v___x_490_;
}
else
{
lean_object* v___x_492_; 
lean_dec(v_fst_481_);
lean_dec(v_fst_471_);
lean_dec(v_fst_466_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_e_352_);
v___x_492_ = v___x_484_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_snd_482_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_492_);
v___x_494_ = v___x_479_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_snd_477_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
}
}
case 10:
{
lean_object* v_data_501_; lean_object* v_expr_502_; lean_object* v___x_503_; lean_object* v_fst_504_; lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_523_; 
v_data_501_ = lean_ctor_get(v_e_352_, 0);
v_expr_502_ = lean_ctor_get(v_e_352_, 1);
lean_inc_ref(v_expr_502_);
v___x_503_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_expr_502_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_504_ = lean_ctor_get(v___x_503_, 0);
v_snd_505_ = lean_ctor_get(v___x_503_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_523_ == 0)
{
v___x_507_ = v___x_503_;
v_isShared_508_ = v_isSharedCheck_523_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_inc(v_fst_504_);
lean_dec(v___x_503_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_523_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_522_; 
v_fst_509_ = lean_ctor_get(v_fst_504_, 0);
v_snd_510_ = lean_ctor_get(v_fst_504_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_fst_504_);
if (v_isSharedCheck_522_ == 0)
{
v___x_512_ = v_fst_504_;
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_inc(v_fst_509_);
lean_dec(v_fst_504_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; 
v___x_514_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_502_, v_fst_509_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_inc(v_data_501_);
lean_del_object(v___x_512_);
lean_del_object(v___x_507_);
lean_dec_ref(v_e_352_);
v___x_515_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_501_, v_fst_509_, v_snd_510_, v_a_355_, v_snd_505_);
return v___x_515_;
}
else
{
lean_object* v___x_517_; 
lean_dec(v_fst_509_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v_e_352_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_snd_510_);
v___x_517_ = v_reuseFailAlloc_521_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_517_);
v___x_519_ = v___x_507_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_snd_505_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_524_; lean_object* v_idx_525_; lean_object* v_struct_526_; lean_object* v___x_527_; lean_object* v_fst_528_; lean_object* v_snd_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_547_; 
v_typeName_524_ = lean_ctor_get(v_e_352_, 0);
v_idx_525_ = lean_ctor_get(v_e_352_, 1);
v_struct_526_ = lean_ctor_get(v_e_352_, 2);
lean_inc_ref(v_struct_526_);
v___x_527_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_349_, v_n_350_, v_subst_351_, v_struct_526_, v_offset_353_, v_a_354_, v_a_355_, v_a_356_);
v_fst_528_ = lean_ctor_get(v___x_527_, 0);
v_snd_529_ = lean_ctor_get(v___x_527_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_547_ == 0)
{
v___x_531_ = v___x_527_;
v_isShared_532_ = v_isSharedCheck_547_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snd_529_);
lean_inc(v_fst_528_);
lean_dec(v___x_527_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_547_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_fst_533_; lean_object* v_snd_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_546_; 
v_fst_533_ = lean_ctor_get(v_fst_528_, 0);
v_snd_534_ = lean_ctor_get(v_fst_528_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_fst_528_);
if (v_isSharedCheck_546_ == 0)
{
v___x_536_ = v_fst_528_;
v_isShared_537_ = v_isSharedCheck_546_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_snd_534_);
lean_inc(v_fst_533_);
lean_dec(v_fst_528_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_546_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
uint8_t v___x_538_; 
v___x_538_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_526_, v_fst_533_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_inc(v_idx_525_);
lean_inc(v_typeName_524_);
lean_del_object(v___x_536_);
lean_del_object(v___x_531_);
lean_dec_ref(v_e_352_);
v___x_539_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_524_, v_idx_525_, v_fst_533_, v_snd_534_, v_a_355_, v_snd_529_);
return v___x_539_;
}
else
{
lean_object* v___x_541_; 
lean_dec(v_fst_533_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v_e_352_);
v___x_541_ = v___x_536_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_e_352_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_snd_534_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_541_);
v___x_543_ = v___x_531_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_snd_529_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v_offset_353_);
lean_dec_ref(v_e_352_);
v___x_548_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
v___x_549_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_548_, v_a_354_, v_a_355_, v_a_356_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(lean_object* v_beginIdx_550_, lean_object* v_n_551_, lean_object* v_subst_552_, lean_object* v_e_553_, lean_object* v_offset_554_, lean_object* v_a_555_, uint8_t v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_key_558_; lean_object* v___x_559_; 
lean_inc(v_offset_554_);
lean_inc_ref(v_e_553_);
v_key_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_558_, 0, v_e_553_);
lean_ctor_set(v_key_558_, 1, v_offset_554_);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_555_, v_key_558_);
if (lean_obj_tag(v___x_559_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v_key_558_);
lean_dec(v_offset_554_);
lean_dec_ref(v_e_553_);
v_val_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_val_560_);
lean_dec_ref(v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_val_560_);
lean_ctor_set(v___x_561_, 1, v_a_555_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_a_557_);
return v___x_562_;
}
else
{
lean_object* v_s_u2081_563_; 
lean_dec(v___x_559_);
v_s_u2081_563_ = lean_nat_add(v_beginIdx_550_, v_offset_554_);
switch(lean_obj_tag(v_e_553_))
{
case 0:
{
lean_object* v_deBruijnIndex_564_; uint8_t v___x_565_; 
v_deBruijnIndex_564_ = lean_ctor_get(v_e_553_, 0);
v___x_565_ = lean_nat_dec_le(v_s_u2081_563_, v_deBruijnIndex_564_);
lean_dec(v_s_u2081_563_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_offset_554_);
v___x_566_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; uint8_t v___x_568_; 
lean_inc(v_deBruijnIndex_564_);
lean_dec_ref(v_e_553_);
v___x_567_ = lean_nat_add(v_offset_554_, v_n_551_);
v___x_568_ = lean_nat_dec_lt(v_deBruijnIndex_564_, v___x_567_);
lean_dec(v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_573_; 
lean_dec(v_offset_554_);
v___x_569_ = lean_nat_sub(v_deBruijnIndex_564_, v_n_551_);
lean_dec(v_deBruijnIndex_564_);
v___x_570_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_569_, v_a_557_);
v_fst_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_fst_571_);
v_snd_572_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_snd_572_);
lean_dec_ref(v___x_570_);
v___x_573_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_fst_571_, v_a_555_, v_a_556_, v_snd_572_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_v_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_583_; 
v___x_574_ = lean_nat_sub(v_deBruijnIndex_564_, v_offset_554_);
lean_dec(v_deBruijnIndex_564_);
v___x_575_ = lean_nat_sub(v_n_551_, v___x_574_);
lean_dec(v___x_574_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_sub(v___x_575_, v___x_576_);
lean_dec(v___x_575_);
v_v_578_ = lean_array_fget_borrowed(v_subst_552_, v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_578_);
v___x_580_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_578_, v___x_579_, v_offset_554_, v_a_556_, v_a_557_);
lean_dec(v_offset_554_);
v_fst_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_fst_581_);
v_snd_582_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_snd_582_);
lean_dec_ref(v___x_580_);
v___x_583_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_fst_581_, v_a_555_, v_a_556_, v_snd_582_);
return v___x_583_;
}
}
}
case 9:
{
lean_object* v___x_584_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_584_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_584_;
}
case 2:
{
lean_object* v___x_585_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_585_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_585_;
}
case 1:
{
lean_object* v___x_586_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_586_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_586_;
}
case 4:
{
lean_object* v___x_587_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_587_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_587_;
}
case 3:
{
lean_object* v___x_588_; 
lean_dec(v_s_u2081_563_);
lean_dec(v_offset_554_);
v___x_588_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_588_;
}
default: 
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = l_Lean_Expr_looseBVarRange(v_e_553_);
v___x_590_ = lean_nat_dec_le(v___x_589_, v_s_u2081_563_);
lean_dec(v_s_u2081_563_);
lean_dec(v___x_589_);
if (v___x_590_ == 0)
{
switch(lean_obj_tag(v_e_553_))
{
case 9:
{
lean_object* v___x_591_; 
lean_dec(v_offset_554_);
v___x_591_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_591_;
}
case 2:
{
lean_object* v___x_592_; 
lean_dec(v_offset_554_);
v___x_592_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_592_;
}
case 0:
{
lean_object* v___x_593_; 
lean_dec(v_offset_554_);
v___x_593_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_593_;
}
case 1:
{
lean_object* v___x_594_; 
lean_dec(v_offset_554_);
v___x_594_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_594_;
}
case 4:
{
lean_object* v___x_595_; 
lean_dec(v_offset_554_);
v___x_595_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_595_;
}
case 3:
{
lean_object* v___x_596_; 
lean_dec(v_offset_554_);
v___x_596_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_596_;
}
default: 
{
lean_object* v___x_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v_fst_600_; lean_object* v_snd_601_; lean_object* v___x_602_; 
v___x_597_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_550_, v_n_551_, v_subst_552_, v_e_553_, v_offset_554_, v_a_555_, v_a_556_, v_a_557_);
v_fst_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_fst_598_);
v_snd_599_ = lean_ctor_get(v___x_597_, 1);
lean_inc(v_snd_599_);
lean_dec_ref(v___x_597_);
v_fst_600_ = lean_ctor_get(v_fst_598_, 0);
lean_inc(v_fst_600_);
v_snd_601_ = lean_ctor_get(v_fst_598_, 1);
lean_inc(v_snd_601_);
lean_dec(v_fst_598_);
v___x_602_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_fst_600_, v_snd_601_, v_a_556_, v_snd_599_);
return v___x_602_;
}
}
}
else
{
lean_object* v___x_603_; 
lean_dec(v_offset_554_);
v___x_603_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_558_, v_e_553_, v_a_555_, v_a_556_, v_a_557_);
return v___x_603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2___boxed(lean_object* v_beginIdx_604_, lean_object* v_n_605_, lean_object* v_subst_606_, lean_object* v_e_607_, lean_object* v_offset_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
uint8_t v_a_boxed_612_; lean_object* v_res_613_; 
v_a_boxed_612_ = lean_unbox(v_a_610_);
v_res_613_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_604_, v_n_605_, v_subst_606_, v_e_607_, v_offset_608_, v_a_609_, v_a_boxed_612_, v_a_611_);
lean_dec_ref(v_subst_606_);
lean_dec(v_n_605_);
lean_dec(v_beginIdx_604_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(lean_object* v_beginIdx_614_, lean_object* v_n_615_, lean_object* v_subst_616_, lean_object* v_e_617_, lean_object* v_offset_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
uint8_t v_a_boxed_622_; lean_object* v_res_623_; 
v_a_boxed_622_ = lean_unbox(v_a_620_);
v_res_623_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_614_, v_n_615_, v_subst_616_, v_e_617_, v_offset_618_, v_a_619_, v_a_boxed_622_, v_a_621_);
lean_dec_ref(v_subst_616_);
lean_dec(v_n_615_);
lean_dec(v_beginIdx_614_);
return v_res_623_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0(void){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(lean_box(0));
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_box(0);
v___x_626_ = lean_unsigned_to_nat(16u);
v___x_627_ = lean_mk_array(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__1, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_634_ = lean_unsigned_to_nat(34u);
v___x_635_ = lean_unsigned_to_nat(20u);
v___x_636_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_637_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_638_ = l_mkPanicMessageWithDecl(v___x_637_, v___x_636_, v___x_635_, v___x_634_, v___x_633_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_640_ = lean_unsigned_to_nat(32u);
v___x_641_ = lean_unsigned_to_nat(19u);
v___x_642_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4));
v___x_643_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_644_ = l_mkPanicMessageWithDecl(v___x_643_, v___x_642_, v___x_641_, v___x_640_, v___x_639_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object* v_e_645_, lean_object* v_beginIdx_646_, lean_object* v_endIdx_647_, lean_object* v_subst_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
uint8_t v___x_656_; 
v___x_656_ = lean_nat_dec_lt(v_endIdx_647_, v_beginIdx_646_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_array_get_size(v_subst_648_);
v___x_658_ = lean_nat_dec_lt(v___x_657_, v_endIdx_647_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v_share_660_; lean_object* v_maxFVar_661_; lean_object* v_proofInstInfo_662_; lean_object* v_inferType_663_; lean_object* v_getLevel_664_; lean_object* v_congrInfo_665_; lean_object* v_defEqI_666_; lean_object* v_extensions_667_; lean_object* v_issues_668_; uint8_t v_debug_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_726_; 
v___x_659_ = lean_st_ref_take(v_a_650_);
v_share_660_ = lean_ctor_get(v___x_659_, 0);
v_maxFVar_661_ = lean_ctor_get(v___x_659_, 1);
v_proofInstInfo_662_ = lean_ctor_get(v___x_659_, 2);
v_inferType_663_ = lean_ctor_get(v___x_659_, 3);
v_getLevel_664_ = lean_ctor_get(v___x_659_, 4);
v_congrInfo_665_ = lean_ctor_get(v___x_659_, 5);
v_defEqI_666_ = lean_ctor_get(v___x_659_, 6);
v_extensions_667_ = lean_ctor_get(v___x_659_, 7);
v_issues_668_ = lean_ctor_get(v___x_659_, 8);
v_debug_669_ = lean_ctor_get_uint8(v___x_659_, sizeof(void*)*9);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_726_ == 0)
{
v___x_671_ = v___x_659_;
v_isShared_672_ = v_isSharedCheck_726_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_issues_668_);
lean_inc(v_extensions_667_);
lean_inc(v_defEqI_666_);
lean_inc(v_congrInfo_665_);
lean_inc(v_getLevel_664_);
lean_inc(v_inferType_663_);
lean_inc(v_proofInstInfo_662_);
lean_inc(v_maxFVar_661_);
lean_inc(v_share_660_);
lean_dec(v___x_659_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_726_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_maxFVar_661_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_proofInstInfo_662_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_inferType_663_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v_getLevel_664_);
lean_ctor_set(v_reuseFailAlloc_725_, 5, v_congrInfo_665_);
lean_ctor_set(v_reuseFailAlloc_725_, 6, v_defEqI_666_);
lean_ctor_set(v_reuseFailAlloc_725_, 7, v_extensions_667_);
lean_ctor_set(v_reuseFailAlloc_725_, 8, v_issues_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_725_, sizeof(void*)*9, v_debug_669_);
v___x_675_ = v_reuseFailAlloc_725_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_fst_679_; lean_object* v_snd_680_; uint8_t v_debug_701_; lean_object* v_n_702_; lean_object* v___x_703_; 
v___x_676_ = lean_st_ref_set(v_a_650_, v___x_675_);
v___x_677_ = lean_st_ref_get(v_a_650_);
v_debug_701_ = lean_ctor_get_uint8(v___x_677_, sizeof(void*)*9);
lean_dec(v___x_677_);
v_n_702_ = lean_nat_sub(v_endIdx_647_, v_beginIdx_646_);
v___x_703_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_645_))
{
case 0:
{
lean_object* v_deBruijnIndex_704_; uint8_t v___x_705_; 
v_deBruijnIndex_704_ = lean_ctor_get(v_e_645_, 0);
v___x_705_ = lean_nat_dec_le(v_beginIdx_646_, v_deBruijnIndex_704_);
if (v___x_705_ == 0)
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
else
{
uint8_t v___x_706_; 
lean_inc(v_deBruijnIndex_704_);
lean_dec_ref(v_e_645_);
v___x_706_ = lean_nat_dec_lt(v_deBruijnIndex_704_, v_n_702_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_fst_709_; lean_object* v_snd_710_; 
v___x_707_ = lean_nat_sub(v_deBruijnIndex_704_, v_n_702_);
lean_dec(v_n_702_);
lean_dec(v_deBruijnIndex_704_);
v___x_708_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_707_, v_share_660_);
v_fst_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_fst_709_);
v_snd_710_ = lean_ctor_get(v___x_708_, 1);
lean_inc(v_snd_710_);
lean_dec_ref(v___x_708_);
v_fst_679_ = v_fst_709_;
v_snd_680_ = v_snd_710_;
goto v___jp_678_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_v_714_; lean_object* v___x_715_; lean_object* v_fst_716_; lean_object* v_snd_717_; 
v___x_711_ = lean_nat_sub(v_n_702_, v_deBruijnIndex_704_);
lean_dec(v_deBruijnIndex_704_);
lean_dec(v_n_702_);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_sub(v___x_711_, v___x_712_);
lean_dec(v___x_711_);
v_v_714_ = lean_array_fget_borrowed(v_subst_648_, v___x_713_);
lean_dec(v___x_713_);
lean_inc(v_v_714_);
v___x_715_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_714_, v___x_703_, v___x_703_, v_debug_701_, v_share_660_);
v_fst_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_fst_716_);
v_snd_717_ = lean_ctor_get(v___x_715_, 1);
lean_inc(v_snd_717_);
lean_dec_ref(v___x_715_);
v_fst_679_ = v_fst_716_;
v_snd_680_ = v_snd_717_;
goto v___jp_678_;
}
}
}
case 9:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 2:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 1:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 4:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 3:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
default: 
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Expr_looseBVarRange(v_e_645_);
v___x_719_ = lean_nat_dec_le(v___x_718_, v_beginIdx_646_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
switch(lean_obj_tag(v_e_645_))
{
case 9:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 2:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 0:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 1:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 4:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
case 3:
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
default: 
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v_fst_724_; 
v___x_720_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_721_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_646_, v_n_702_, v_subst_648_, v_e_645_, v___x_703_, v___x_720_, v_debug_701_, v_share_660_);
lean_dec(v_n_702_);
v_fst_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_fst_722_);
v_snd_723_ = lean_ctor_get(v___x_721_, 1);
lean_inc(v_snd_723_);
lean_dec_ref(v___x_721_);
v_fst_724_ = lean_ctor_get(v_fst_722_, 0);
lean_inc(v_fst_724_);
lean_dec(v_fst_722_);
v_fst_679_ = v_fst_724_;
v_snd_680_ = v_snd_723_;
goto v___jp_678_;
}
}
}
else
{
lean_dec(v_n_702_);
v_fst_679_ = v_e_645_;
v_snd_680_ = v_share_660_;
goto v___jp_678_;
}
}
}
v___jp_678_:
{
lean_object* v___x_681_; lean_object* v_maxFVar_682_; lean_object* v_proofInstInfo_683_; lean_object* v_inferType_684_; lean_object* v_getLevel_685_; lean_object* v_congrInfo_686_; lean_object* v_defEqI_687_; lean_object* v_extensions_688_; lean_object* v_issues_689_; uint8_t v_debug_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_699_; 
v___x_681_ = lean_st_ref_take(v_a_650_);
v_maxFVar_682_ = lean_ctor_get(v___x_681_, 1);
v_proofInstInfo_683_ = lean_ctor_get(v___x_681_, 2);
v_inferType_684_ = lean_ctor_get(v___x_681_, 3);
v_getLevel_685_ = lean_ctor_get(v___x_681_, 4);
v_congrInfo_686_ = lean_ctor_get(v___x_681_, 5);
v_defEqI_687_ = lean_ctor_get(v___x_681_, 6);
v_extensions_688_ = lean_ctor_get(v___x_681_, 7);
v_issues_689_ = lean_ctor_get(v___x_681_, 8);
v_debug_690_ = lean_ctor_get_uint8(v___x_681_, sizeof(void*)*9);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_700_);
v___x_692_ = v___x_681_;
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_issues_689_);
lean_inc(v_extensions_688_);
lean_inc(v_defEqI_687_);
lean_inc(v_congrInfo_686_);
lean_inc(v_getLevel_685_);
lean_inc(v_inferType_684_);
lean_inc(v_proofInstInfo_683_);
lean_inc(v_maxFVar_682_);
lean_dec(v___x_681_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_snd_680_);
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_snd_680_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_maxFVar_682_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_proofInstInfo_683_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_inferType_684_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_getLevel_685_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v_congrInfo_686_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_defEqI_687_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_extensions_688_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_issues_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_698_, sizeof(void*)*9, v_debug_690_);
v___x_695_ = v_reuseFailAlloc_698_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_st_ref_set(v_a_650_, v___x_695_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v_fst_679_);
return v___x_697_;
}
}
}
}
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref(v_e_645_);
v___x_727_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__5, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5);
v___x_728_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v___x_727_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_728_;
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v_e_645_);
v___x_729_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__6, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6);
v___x_730_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(v___x_729_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevRangeS___boxed(lean_object* v_e_731_, lean_object* v_beginIdx_732_, lean_object* v_endIdx_733_, lean_object* v_subst_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_731_, v_beginIdx_732_, v_endIdx_733_, v_subst_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec_ref(v_subst_734_);
lean_dec(v_endIdx_733_);
lean_dec(v_beginIdx_732_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_743_, lean_object* v_m_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_744_, v_a_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_747_, lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(v_00_u03b2_747_, v_m_748_, v_a_749_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_m_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_751_, lean_object* v_a_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_752_, v_x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(lean_object* v_00_u03b2_755_, lean_object* v_a_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_755_, v_a_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec_ref(v_a_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS(lean_object* v_e_759_, lean_object* v_subst_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_subst_760_);
v___x_770_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_759_, v___x_768_, v___x_769_, v_subst_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevS___boxed(lean_object* v_e_771_, lean_object* v_subst_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Meta_Sym_instantiateRevS(v_e_771_, v_subst_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec_ref(v_subst_772_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(lean_object* v_msg_781_, uint8_t v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___x_3111__overap_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___f_784_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0));
v___f_785_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1));
v___f_786_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2));
v___f_787_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3));
v___f_788_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4));
v___f_789_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5));
v___f_790_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6));
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___f_784_);
lean_ctor_set(v___x_791_, 1, v___f_785_);
v___x_792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___f_786_);
lean_ctor_set(v___x_792_, 2, v___f_787_);
lean_ctor_set(v___x_792_, 3, v___f_788_);
lean_ctor_set(v___x_792_, 4, v___f_789_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___f_790_);
lean_inc_ref(v___x_793_);
v___f_794_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_794_, 0, v___x_793_);
lean_inc_ref(v___x_793_);
v___f_795_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_795_, 0, v___x_793_);
lean_inc_ref(v___x_793_);
v___f_796_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_796_, 0, v___x_793_);
lean_inc_ref(v___x_793_);
v___f_797_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_797_, 0, v___x_793_);
lean_inc_ref(v___x_793_);
v___x_798_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_798_, 0, lean_box(0));
lean_closure_set(v___x_798_, 1, lean_box(0));
lean_closure_set(v___x_798_, 2, v___x_793_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set(v___x_799_, 1, v___f_794_);
lean_inc_ref(v___x_793_);
v___x_800_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_800_, 0, lean_box(0));
lean_closure_set(v___x_800_, 1, lean_box(0));
lean_closure_set(v___x_800_, 2, v___x_793_);
v___x_801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_801_, 0, v___x_799_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
lean_ctor_set(v___x_801_, 2, v___f_795_);
lean_ctor_set(v___x_801_, 3, v___f_796_);
lean_ctor_set(v___x_801_, 4, v___f_797_);
v___x_802_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_802_, 0, lean_box(0));
lean_closure_set(v___x_802_, 1, lean_box(0));
lean_closure_set(v___x_802_, 2, v___x_793_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_instInhabitedExpr;
v___x_805_ = l_instInhabitedOfMonad___redArg(v___x_803_, v___x_804_);
v___f_806_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_806_, 0, v___x_805_);
v___x_3111__overap_807_ = lean_panic_fn_borrowed(v___f_806_, v_msg_781_);
lean_dec_ref(v___f_806_);
v___x_808_ = lean_box(v___y_782_);
v___x_809_ = lean_apply_2(v___x_3111__overap_807_, v___x_808_, v___y_783_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(lean_object* v_msg_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v___y_3548__boxed_813_; lean_object* v_res_814_; 
v___y_3548__boxed_813_ = lean_unbox(v___y_811_);
v_res_814_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_810_, v___y_3548__boxed_813_, v___y_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(lean_object* v_n_815_, lean_object* v_beginIdx_816_, lean_object* v_subst_817_, lean_object* v_e_818_, lean_object* v_offset_819_, lean_object* v_a_820_, uint8_t v_a_821_, lean_object* v_a_822_){
_start:
{
switch(lean_obj_tag(v_e_818_))
{
case 5:
{
lean_object* v_fn_823_; lean_object* v_arg_824_; lean_object* v___x_825_; lean_object* v_fst_826_; lean_object* v_snd_827_; lean_object* v_fst_828_; lean_object* v_snd_829_; lean_object* v___x_830_; lean_object* v_fst_831_; lean_object* v_snd_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_853_; 
v_fn_823_ = lean_ctor_get(v_e_818_, 0);
v_arg_824_ = lean_ctor_get(v_e_818_, 1);
lean_inc(v_offset_819_);
lean_inc_ref(v_fn_823_);
v___x_825_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_fn_823_, v_offset_819_, v_a_820_, v_a_821_, v_a_822_);
v_fst_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_fst_826_);
v_snd_827_ = lean_ctor_get(v___x_825_, 1);
lean_inc(v_snd_827_);
lean_dec_ref(v___x_825_);
v_fst_828_ = lean_ctor_get(v_fst_826_, 0);
lean_inc(v_fst_828_);
v_snd_829_ = lean_ctor_get(v_fst_826_, 1);
lean_inc(v_snd_829_);
lean_dec(v_fst_826_);
lean_inc_ref(v_arg_824_);
v___x_830_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_arg_824_, v_offset_819_, v_snd_829_, v_a_821_, v_snd_827_);
v_fst_831_ = lean_ctor_get(v___x_830_, 0);
v_snd_832_ = lean_ctor_get(v___x_830_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_853_ == 0)
{
v___x_834_ = v___x_830_;
v_isShared_835_ = v_isSharedCheck_853_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snd_832_);
lean_inc(v_fst_831_);
lean_dec(v___x_830_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_853_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_fst_836_; lean_object* v_snd_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_852_; 
v_fst_836_ = lean_ctor_get(v_fst_831_, 0);
v_snd_837_ = lean_ctor_get(v_fst_831_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_fst_831_);
if (v_isSharedCheck_852_ == 0)
{
v___x_839_ = v_fst_831_;
v_isShared_840_ = v_isSharedCheck_852_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_snd_837_);
lean_inc(v_fst_836_);
lean_dec(v_fst_831_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_852_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___y_842_; uint8_t v___x_850_; 
v___x_850_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_823_, v_fst_828_);
if (v___x_850_ == 0)
{
v___y_842_ = v___x_850_;
goto v___jp_841_;
}
else
{
uint8_t v___x_851_; 
v___x_851_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_824_, v_fst_836_);
v___y_842_ = v___x_851_;
goto v___jp_841_;
}
v___jp_841_:
{
if (v___y_842_ == 0)
{
lean_object* v___x_843_; 
lean_del_object(v___x_839_);
lean_del_object(v___x_834_);
lean_dec_ref(v_e_818_);
v___x_843_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_828_, v_fst_836_, v_snd_837_, v_a_821_, v_snd_832_);
return v___x_843_;
}
else
{
lean_object* v___x_845_; 
lean_dec(v_fst_836_);
lean_dec(v_fst_828_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v_e_818_);
v___x_845_ = v___x_839_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_e_818_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_snd_837_);
v___x_845_ = v_reuseFailAlloc_849_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_845_);
v___x_847_ = v___x_834_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_snd_832_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_854_; lean_object* v_binderType_855_; lean_object* v_body_856_; uint8_t v_binderInfo_857_; lean_object* v___x_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_fst_866_; lean_object* v_snd_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_888_; 
v_binderName_854_ = lean_ctor_get(v_e_818_, 0);
v_binderType_855_ = lean_ctor_get(v_e_818_, 1);
v_body_856_ = lean_ctor_get(v_e_818_, 2);
v_binderInfo_857_ = lean_ctor_get_uint8(v_e_818_, sizeof(void*)*3 + 8);
lean_inc(v_offset_819_);
lean_inc_ref(v_binderType_855_);
v___x_858_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_binderType_855_, v_offset_819_, v_a_820_, v_a_821_, v_a_822_);
v_fst_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_fst_859_);
v_snd_860_ = lean_ctor_get(v___x_858_, 1);
lean_inc(v_snd_860_);
lean_dec_ref(v___x_858_);
v_fst_861_ = lean_ctor_get(v_fst_859_, 0);
lean_inc(v_fst_861_);
v_snd_862_ = lean_ctor_get(v_fst_859_, 1);
lean_inc(v_snd_862_);
lean_dec(v_fst_859_);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_nat_add(v_offset_819_, v___x_863_);
lean_dec(v_offset_819_);
lean_inc_ref(v_body_856_);
v___x_865_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_body_856_, v___x_864_, v_snd_862_, v_a_821_, v_snd_860_);
v_fst_866_ = lean_ctor_get(v___x_865_, 0);
v_snd_867_ = lean_ctor_get(v___x_865_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_888_ == 0)
{
v___x_869_ = v___x_865_;
v_isShared_870_ = v_isSharedCheck_888_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_snd_867_);
lean_inc(v_fst_866_);
lean_dec(v___x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_888_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_887_; 
v_fst_871_ = lean_ctor_get(v_fst_866_, 0);
v_snd_872_ = lean_ctor_get(v_fst_866_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_fst_866_);
if (v_isSharedCheck_887_ == 0)
{
v___x_874_ = v_fst_866_;
v_isShared_875_ = v_isSharedCheck_887_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_snd_872_);
lean_inc(v_fst_871_);
lean_dec(v_fst_866_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_887_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
uint8_t v___y_877_; uint8_t v___x_885_; 
v___x_885_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_855_, v_fst_861_);
if (v___x_885_ == 0)
{
v___y_877_ = v___x_885_;
goto v___jp_876_;
}
else
{
uint8_t v___x_886_; 
v___x_886_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_856_, v_fst_871_);
v___y_877_ = v___x_886_;
goto v___jp_876_;
}
v___jp_876_:
{
if (v___y_877_ == 0)
{
lean_object* v___x_878_; 
lean_inc(v_binderName_854_);
lean_del_object(v___x_874_);
lean_del_object(v___x_869_);
lean_dec_ref(v_e_818_);
v___x_878_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_854_, v_binderInfo_857_, v_fst_861_, v_fst_871_, v_snd_872_, v_a_821_, v_snd_867_);
return v___x_878_;
}
else
{
lean_object* v___x_880_; 
lean_dec(v_fst_871_);
lean_dec(v_fst_861_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_e_818_);
v___x_880_ = v___x_874_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_e_818_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_snd_872_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_880_);
v___x_882_ = v___x_869_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_snd_867_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_889_; lean_object* v_binderType_890_; lean_object* v_body_891_; uint8_t v_binderInfo_892_; lean_object* v___x_893_; lean_object* v_fst_894_; lean_object* v_snd_895_; lean_object* v_fst_896_; lean_object* v_snd_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_fst_901_; lean_object* v_snd_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_923_; 
v_binderName_889_ = lean_ctor_get(v_e_818_, 0);
v_binderType_890_ = lean_ctor_get(v_e_818_, 1);
v_body_891_ = lean_ctor_get(v_e_818_, 2);
v_binderInfo_892_ = lean_ctor_get_uint8(v_e_818_, sizeof(void*)*3 + 8);
lean_inc(v_offset_819_);
lean_inc_ref(v_binderType_890_);
v___x_893_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_binderType_890_, v_offset_819_, v_a_820_, v_a_821_, v_a_822_);
v_fst_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_fst_894_);
v_snd_895_ = lean_ctor_get(v___x_893_, 1);
lean_inc(v_snd_895_);
lean_dec_ref(v___x_893_);
v_fst_896_ = lean_ctor_get(v_fst_894_, 0);
lean_inc(v_fst_896_);
v_snd_897_ = lean_ctor_get(v_fst_894_, 1);
lean_inc(v_snd_897_);
lean_dec(v_fst_894_);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_offset_819_, v___x_898_);
lean_dec(v_offset_819_);
lean_inc_ref(v_body_891_);
v___x_900_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_body_891_, v___x_899_, v_snd_897_, v_a_821_, v_snd_895_);
v_fst_901_ = lean_ctor_get(v___x_900_, 0);
v_snd_902_ = lean_ctor_get(v___x_900_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_923_ == 0)
{
v___x_904_ = v___x_900_;
v_isShared_905_ = v_isSharedCheck_923_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_snd_902_);
lean_inc(v_fst_901_);
lean_dec(v___x_900_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_923_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_922_; 
v_fst_906_ = lean_ctor_get(v_fst_901_, 0);
v_snd_907_ = lean_ctor_get(v_fst_901_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_fst_901_);
if (v_isSharedCheck_922_ == 0)
{
v___x_909_ = v_fst_901_;
v_isShared_910_ = v_isSharedCheck_922_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snd_907_);
lean_inc(v_fst_906_);
lean_dec(v_fst_901_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_922_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___y_912_; uint8_t v___x_920_; 
v___x_920_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_890_, v_fst_896_);
if (v___x_920_ == 0)
{
v___y_912_ = v___x_920_;
goto v___jp_911_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_891_, v_fst_906_);
v___y_912_ = v___x_921_;
goto v___jp_911_;
}
v___jp_911_:
{
if (v___y_912_ == 0)
{
lean_object* v___x_913_; 
lean_inc(v_binderName_889_);
lean_del_object(v___x_909_);
lean_del_object(v___x_904_);
lean_dec_ref(v_e_818_);
v___x_913_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_889_, v_binderInfo_892_, v_fst_896_, v_fst_906_, v_snd_907_, v_a_821_, v_snd_902_);
return v___x_913_;
}
else
{
lean_object* v___x_915_; 
lean_dec(v_fst_906_);
lean_dec(v_fst_896_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_e_818_);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_e_818_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_snd_907_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_915_);
v___x_917_ = v___x_904_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_snd_902_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_924_; lean_object* v_type_925_; lean_object* v_value_926_; lean_object* v_body_927_; uint8_t v_nondep_928_; lean_object* v___x_929_; lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v_fst_932_; lean_object* v_snd_933_; lean_object* v___x_934_; lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_fst_942_; lean_object* v_snd_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_966_; 
v_declName_924_ = lean_ctor_get(v_e_818_, 0);
v_type_925_ = lean_ctor_get(v_e_818_, 1);
v_value_926_ = lean_ctor_get(v_e_818_, 2);
v_body_927_ = lean_ctor_get(v_e_818_, 3);
v_nondep_928_ = lean_ctor_get_uint8(v_e_818_, sizeof(void*)*4 + 8);
lean_inc(v_offset_819_);
lean_inc_ref(v_type_925_);
v___x_929_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_type_925_, v_offset_819_, v_a_820_, v_a_821_, v_a_822_);
v_fst_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_fst_930_);
v_snd_931_ = lean_ctor_get(v___x_929_, 1);
lean_inc(v_snd_931_);
lean_dec_ref(v___x_929_);
v_fst_932_ = lean_ctor_get(v_fst_930_, 0);
lean_inc(v_fst_932_);
v_snd_933_ = lean_ctor_get(v_fst_930_, 1);
lean_inc(v_snd_933_);
lean_dec(v_fst_930_);
lean_inc(v_offset_819_);
lean_inc_ref(v_value_926_);
v___x_934_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_value_926_, v_offset_819_, v_snd_933_, v_a_821_, v_snd_931_);
v_fst_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_fst_935_);
v_snd_936_ = lean_ctor_get(v___x_934_, 1);
lean_inc(v_snd_936_);
lean_dec_ref(v___x_934_);
v_fst_937_ = lean_ctor_get(v_fst_935_, 0);
lean_inc(v_fst_937_);
v_snd_938_ = lean_ctor_get(v_fst_935_, 1);
lean_inc(v_snd_938_);
lean_dec(v_fst_935_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_offset_819_, v___x_939_);
lean_dec(v_offset_819_);
lean_inc_ref(v_body_927_);
v___x_941_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_body_927_, v___x_940_, v_snd_938_, v_a_821_, v_snd_936_);
v_fst_942_ = lean_ctor_get(v___x_941_, 0);
v_snd_943_ = lean_ctor_get(v___x_941_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_966_ == 0)
{
v___x_945_ = v___x_941_;
v_isShared_946_ = v_isSharedCheck_966_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_snd_943_);
lean_inc(v_fst_942_);
lean_dec(v___x_941_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_966_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; lean_object* v_snd_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_965_; 
v_fst_947_ = lean_ctor_get(v_fst_942_, 0);
v_snd_948_ = lean_ctor_get(v_fst_942_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_fst_942_);
if (v_isSharedCheck_965_ == 0)
{
v___x_950_ = v_fst_942_;
v_isShared_951_ = v_isSharedCheck_965_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_948_);
lean_inc(v_fst_947_);
lean_dec(v_fst_942_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_965_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
uint8_t v___y_953_; uint8_t v___x_963_; 
v___x_963_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_925_, v_fst_932_);
if (v___x_963_ == 0)
{
v___y_953_ = v___x_963_;
goto v___jp_952_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_926_, v_fst_937_);
v___y_953_ = v___x_964_;
goto v___jp_952_;
}
v___jp_952_:
{
if (v___y_953_ == 0)
{
lean_object* v___x_954_; 
lean_inc(v_declName_924_);
lean_del_object(v___x_950_);
lean_del_object(v___x_945_);
lean_dec_ref(v_e_818_);
v___x_954_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_924_, v_fst_932_, v_fst_937_, v_fst_947_, v_nondep_928_, v_snd_948_, v_a_821_, v_snd_943_);
return v___x_954_;
}
else
{
uint8_t v___x_955_; 
v___x_955_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_927_, v_fst_947_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_inc(v_declName_924_);
lean_del_object(v___x_950_);
lean_del_object(v___x_945_);
lean_dec_ref(v_e_818_);
v___x_956_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_924_, v_fst_932_, v_fst_937_, v_fst_947_, v_nondep_928_, v_snd_948_, v_a_821_, v_snd_943_);
return v___x_956_;
}
else
{
lean_object* v___x_958_; 
lean_dec(v_fst_947_);
lean_dec(v_fst_937_);
lean_dec(v_fst_932_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_e_818_);
v___x_958_ = v___x_950_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_e_818_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_snd_948_);
v___x_958_ = v_reuseFailAlloc_962_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_958_);
v___x_960_ = v___x_945_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_snd_943_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
}
}
case 10:
{
lean_object* v_data_967_; lean_object* v_expr_968_; lean_object* v___x_969_; lean_object* v_fst_970_; lean_object* v_snd_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_989_; 
v_data_967_ = lean_ctor_get(v_e_818_, 0);
v_expr_968_ = lean_ctor_get(v_e_818_, 1);
lean_inc_ref(v_expr_968_);
v___x_969_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_expr_968_, v_offset_819_, v_a_820_, v_a_821_, v_a_822_);
v_fst_970_ = lean_ctor_get(v___x_969_, 0);
v_snd_971_ = lean_ctor_get(v___x_969_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_989_ == 0)
{
v___x_973_ = v___x_969_;
v_isShared_974_ = v_isSharedCheck_989_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_snd_971_);
lean_inc(v_fst_970_);
lean_dec(v___x_969_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_989_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_988_; 
v_fst_975_ = lean_ctor_get(v_fst_970_, 0);
v_snd_976_ = lean_ctor_get(v_fst_970_, 1);
v_isSharedCheck_988_ = !lean_is_exclusive(v_fst_970_);
if (v_isSharedCheck_988_ == 0)
{
v___x_978_ = v_fst_970_;
v_isShared_979_ = v_isSharedCheck_988_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snd_976_);
lean_inc(v_fst_975_);
lean_dec(v_fst_970_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_988_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
uint8_t v___x_980_; 
v___x_980_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_968_, v_fst_975_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_inc(v_data_967_);
lean_del_object(v___x_978_);
lean_del_object(v___x_973_);
lean_dec_ref(v_e_818_);
v___x_981_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_967_, v_fst_975_, v_snd_976_, v_a_821_, v_snd_971_);
return v___x_981_;
}
else
{
lean_object* v___x_983_; 
lean_dec(v_fst_975_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_e_818_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_e_818_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_snd_976_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_985_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_983_);
v___x_985_ = v___x_973_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_snd_971_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_990_; lean_object* v_idx_991_; lean_object* v_struct_992_; lean_object* v___x_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1013_; 
v_typeName_990_ = lean_ctor_get(v_e_818_, 0);
v_idx_991_ = lean_ctor_get(v_e_818_, 1);
v_struct_992_ = lean_ctor_get(v_e_818_, 2);
lean_inc_ref(v_struct_992_);
v___x_993_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_815_, v_beginIdx_816_, v_subst_817_, v_struct_992_, v_offset_819_, v_a_820_, v_a_821_, v_a_822_);
v_fst_994_ = lean_ctor_get(v___x_993_, 0);
v_snd_995_ = lean_ctor_get(v___x_993_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_997_ = v___x_993_;
v_isShared_998_ = v_isSharedCheck_1013_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_snd_995_);
lean_inc(v_fst_994_);
lean_dec(v___x_993_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1013_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_fst_999_; lean_object* v_snd_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1012_; 
v_fst_999_ = lean_ctor_get(v_fst_994_, 0);
v_snd_1000_ = lean_ctor_get(v_fst_994_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_fst_994_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1002_ = v_fst_994_;
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_snd_1000_);
lean_inc(v_fst_999_);
lean_dec(v_fst_994_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1012_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
uint8_t v___x_1004_; 
v___x_1004_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_992_, v_fst_999_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_inc(v_idx_991_);
lean_inc(v_typeName_990_);
lean_del_object(v___x_1002_);
lean_del_object(v___x_997_);
lean_dec_ref(v_e_818_);
v___x_1005_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_990_, v_idx_991_, v_fst_999_, v_snd_1000_, v_a_821_, v_snd_995_);
return v___x_1005_;
}
else
{
lean_object* v___x_1007_; 
lean_dec(v_fst_999_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_e_818_);
v___x_1007_ = v___x_1002_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_e_818_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_snd_1000_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1007_);
v___x_1009_ = v___x_997_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_snd_995_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v_offset_819_);
lean_dec_ref(v_e_818_);
v___x_1014_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
v___x_1015_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1014_, v_a_820_, v_a_821_, v_a_822_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(lean_object* v_n_1016_, lean_object* v_beginIdx_1017_, lean_object* v_subst_1018_, lean_object* v_e_1019_, lean_object* v_offset_1020_, lean_object* v_a_1021_, uint8_t v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_key_1024_; lean_object* v___x_1025_; 
lean_inc(v_offset_1020_);
lean_inc_ref(v_e_1019_);
v_key_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1024_, 0, v_e_1019_);
lean_ctor_set(v_key_1024_, 1, v_offset_1020_);
v___x_1025_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1021_, v_key_1024_);
if (lean_obj_tag(v___x_1025_) == 1)
{
lean_object* v_val_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_key_1024_);
lean_dec(v_offset_1020_);
lean_dec_ref(v_e_1019_);
v_val_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_val_1026_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_val_1026_);
lean_ctor_set(v___x_1027_, 1, v_a_1021_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v_a_1023_);
return v___x_1028_;
}
else
{
lean_dec(v___x_1025_);
switch(lean_obj_tag(v_e_1019_))
{
case 0:
{
lean_object* v_deBruijnIndex_1029_; uint8_t v___x_1030_; 
v_deBruijnIndex_1029_ = lean_ctor_get(v_e_1019_, 0);
v___x_1030_ = lean_nat_dec_le(v_offset_1020_, v_deBruijnIndex_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_dec(v_offset_1020_);
v___x_1031_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1031_;
}
else
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
lean_inc(v_deBruijnIndex_1029_);
lean_dec_ref(v_e_1019_);
v___x_1032_ = lean_nat_add(v_offset_1020_, v_n_1016_);
v___x_1033_ = lean_nat_dec_lt(v_deBruijnIndex_1029_, v___x_1032_);
lean_dec(v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___x_1038_; 
lean_dec(v_offset_1020_);
v___x_1034_ = lean_nat_sub(v_deBruijnIndex_1029_, v_n_1016_);
lean_dec(v_deBruijnIndex_1029_);
v___x_1035_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_1034_, v_a_1023_);
v_fst_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_fst_1036_);
v_snd_1037_ = lean_ctor_get(v___x_1035_, 1);
lean_inc(v_snd_1037_);
lean_dec_ref(v___x_1035_);
v___x_1038_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_fst_1036_, v_a_1021_, v_a_1022_, v_snd_1037_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_v_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1046_; 
v___x_1039_ = lean_nat_add(v_beginIdx_1017_, v_deBruijnIndex_1029_);
lean_dec(v_deBruijnIndex_1029_);
v___x_1040_ = lean_nat_sub(v___x_1039_, v_offset_1020_);
lean_dec(v___x_1039_);
v_v_1041_ = lean_array_fget_borrowed(v_subst_1018_, v___x_1040_);
lean_dec(v___x_1040_);
v___x_1042_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1041_);
v___x_1043_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1041_, v___x_1042_, v_offset_1020_, v_a_1022_, v_a_1023_);
lean_dec(v_offset_1020_);
v_fst_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_fst_1044_);
v_snd_1045_ = lean_ctor_get(v___x_1043_, 1);
lean_inc(v_snd_1045_);
lean_dec_ref(v___x_1043_);
v___x_1046_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_fst_1044_, v_a_1021_, v_a_1022_, v_snd_1045_);
return v___x_1046_;
}
}
}
case 9:
{
lean_object* v___x_1047_; 
lean_dec(v_offset_1020_);
v___x_1047_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1047_;
}
case 2:
{
lean_object* v___x_1048_; 
lean_dec(v_offset_1020_);
v___x_1048_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1048_;
}
case 1:
{
lean_object* v___x_1049_; 
lean_dec(v_offset_1020_);
v___x_1049_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1049_;
}
case 4:
{
lean_object* v___x_1050_; 
lean_dec(v_offset_1020_);
v___x_1050_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1050_;
}
case 3:
{
lean_object* v___x_1051_; 
lean_dec(v_offset_1020_);
v___x_1051_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1051_;
}
default: 
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = l_Lean_Expr_looseBVarRange(v_e_1019_);
v___x_1053_ = lean_nat_dec_le(v___x_1052_, v_offset_1020_);
lean_dec(v___x_1052_);
if (v___x_1053_ == 0)
{
switch(lean_obj_tag(v_e_1019_))
{
case 9:
{
lean_object* v___x_1054_; 
lean_dec(v_offset_1020_);
v___x_1054_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1054_;
}
case 2:
{
lean_object* v___x_1055_; 
lean_dec(v_offset_1020_);
v___x_1055_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1055_;
}
case 0:
{
lean_object* v___x_1056_; 
lean_dec(v_offset_1020_);
v___x_1056_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1056_;
}
case 1:
{
lean_object* v___x_1057_; 
lean_dec(v_offset_1020_);
v___x_1057_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1057_;
}
case 4:
{
lean_object* v___x_1058_; 
lean_dec(v_offset_1020_);
v___x_1058_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1058_;
}
case 3:
{
lean_object* v___x_1059_; 
lean_dec(v_offset_1020_);
v___x_1059_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1059_;
}
default: 
{
lean_object* v___x_1060_; lean_object* v_fst_1061_; lean_object* v_snd_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1065_; 
v___x_1060_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1016_, v_beginIdx_1017_, v_subst_1018_, v_e_1019_, v_offset_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
v_fst_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_fst_1061_);
v_snd_1062_ = lean_ctor_get(v___x_1060_, 1);
lean_inc(v_snd_1062_);
lean_dec_ref(v___x_1060_);
v_fst_1063_ = lean_ctor_get(v_fst_1061_, 0);
lean_inc(v_fst_1063_);
v_snd_1064_ = lean_ctor_get(v_fst_1061_, 1);
lean_inc(v_snd_1064_);
lean_dec(v_fst_1061_);
v___x_1065_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_fst_1063_, v_snd_1064_, v_a_1022_, v_snd_1062_);
return v___x_1065_;
}
}
}
else
{
lean_object* v___x_1066_; 
lean_dec(v_offset_1020_);
v___x_1066_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1024_, v_e_1019_, v_a_1021_, v_a_1022_, v_a_1023_);
return v___x_1066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(lean_object* v_n_1067_, lean_object* v_beginIdx_1068_, lean_object* v_subst_1069_, lean_object* v_e_1070_, lean_object* v_offset_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
uint8_t v_a_boxed_1075_; lean_object* v_res_1076_; 
v_a_boxed_1075_ = lean_unbox(v_a_1073_);
v_res_1076_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_1067_, v_beginIdx_1068_, v_subst_1069_, v_e_1070_, v_offset_1071_, v_a_1072_, v_a_boxed_1075_, v_a_1074_);
lean_dec_ref(v_subst_1069_);
lean_dec(v_beginIdx_1068_);
lean_dec(v_n_1067_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(lean_object* v_n_1077_, lean_object* v_beginIdx_1078_, lean_object* v_subst_1079_, lean_object* v_e_1080_, lean_object* v_offset_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
uint8_t v_a_boxed_1085_; lean_object* v_res_1086_; 
v_a_boxed_1085_ = lean_unbox(v_a_1083_);
v_res_1086_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1077_, v_beginIdx_1078_, v_subst_1079_, v_e_1080_, v_offset_1081_, v_a_1082_, v_a_boxed_1085_, v_a_1084_);
lean_dec_ref(v_subst_1079_);
lean_dec(v_beginIdx_1078_);
lean_dec(v_n_1077_);
return v_res_1086_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1088_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1089_ = lean_unsigned_to_nat(34u);
v___x_1090_ = lean_unsigned_to_nat(57u);
v___x_1091_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1092_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1093_ = l_mkPanicMessageWithDecl(v___x_1092_, v___x_1091_, v___x_1090_, v___x_1089_, v___x_1088_);
return v___x_1093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1095_ = lean_unsigned_to_nat(32u);
v___x_1096_ = lean_unsigned_to_nat(56u);
v___x_1097_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0));
v___x_1098_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1099_ = l_mkPanicMessageWithDecl(v___x_1098_, v___x_1097_, v___x_1096_, v___x_1095_, v___x_1094_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(lean_object* v_e_1100_, lean_object* v_beginIdx_1101_, lean_object* v_endIdx_1102_, lean_object* v_subst_1103_, uint8_t v_a_1104_, lean_object* v_a_1105_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_nat_dec_lt(v_endIdx_1102_, v_beginIdx_1101_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_array_get_size(v_subst_1103_);
v___x_1108_ = lean_nat_dec_lt(v___x_1107_, v_endIdx_1102_);
if (v___x_1108_ == 0)
{
lean_object* v_n_1109_; lean_object* v___x_1110_; 
v_n_1109_ = lean_nat_sub(v_endIdx_1102_, v_beginIdx_1101_);
v___x_1110_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_1100_))
{
case 0:
{
lean_object* v_deBruijnIndex_1111_; uint8_t v___x_1112_; 
v_deBruijnIndex_1111_ = lean_ctor_get(v_e_1100_, 0);
v___x_1112_ = lean_nat_dec_le(v___x_1110_, v_deBruijnIndex_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec(v_n_1109_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v_e_1100_);
lean_ctor_set(v___x_1113_, 1, v_a_1105_);
return v___x_1113_;
}
else
{
uint8_t v___x_1114_; 
lean_inc(v_deBruijnIndex_1111_);
lean_dec_ref(v_e_1100_);
v___x_1114_ = lean_nat_dec_lt(v_deBruijnIndex_1111_, v_n_1109_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_nat_sub(v_deBruijnIndex_1111_, v_n_1109_);
lean_dec(v_n_1109_);
lean_dec(v_deBruijnIndex_1111_);
v___x_1116_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_1115_, v_a_1105_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; lean_object* v_v_1118_; lean_object* v___x_1119_; 
lean_dec(v_n_1109_);
v___x_1117_ = lean_nat_add(v_beginIdx_1101_, v_deBruijnIndex_1111_);
lean_dec(v_deBruijnIndex_1111_);
v_v_1118_ = lean_array_fget_borrowed(v_subst_1103_, v___x_1117_);
lean_dec(v___x_1117_);
lean_inc(v_v_1118_);
v___x_1119_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1118_, v___x_1110_, v___x_1110_, v_a_1104_, v_a_1105_);
return v___x_1119_;
}
}
}
case 9:
{
lean_object* v___x_1120_; 
lean_dec(v_n_1109_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_e_1100_);
lean_ctor_set(v___x_1120_, 1, v_a_1105_);
return v___x_1120_;
}
case 2:
{
lean_object* v___x_1121_; 
lean_dec(v_n_1109_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_e_1100_);
lean_ctor_set(v___x_1121_, 1, v_a_1105_);
return v___x_1121_;
}
case 1:
{
lean_object* v___x_1122_; 
lean_dec(v_n_1109_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_e_1100_);
lean_ctor_set(v___x_1122_, 1, v_a_1105_);
return v___x_1122_;
}
case 4:
{
lean_object* v___x_1123_; 
lean_dec(v_n_1109_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_e_1100_);
lean_ctor_set(v___x_1123_, 1, v_a_1105_);
return v___x_1123_;
}
case 3:
{
lean_object* v___x_1124_; 
lean_dec(v_n_1109_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_e_1100_);
lean_ctor_set(v___x_1124_, 1, v_a_1105_);
return v___x_1124_;
}
default: 
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = l_Lean_Expr_looseBVarRange(v_e_1100_);
v___x_1126_ = lean_nat_dec_le(v___x_1125_, v___x_1110_);
lean_dec(v___x_1125_);
if (v___x_1126_ == 0)
{
switch(lean_obj_tag(v_e_1100_))
{
case 9:
{
lean_object* v___x_1127_; 
lean_dec(v_n_1109_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_e_1100_);
lean_ctor_set(v___x_1127_, 1, v_a_1105_);
return v___x_1127_;
}
case 2:
{
lean_object* v___x_1128_; 
lean_dec(v_n_1109_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_e_1100_);
lean_ctor_set(v___x_1128_, 1, v_a_1105_);
return v___x_1128_;
}
case 0:
{
lean_object* v___x_1129_; 
lean_dec(v_n_1109_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v_e_1100_);
lean_ctor_set(v___x_1129_, 1, v_a_1105_);
return v___x_1129_;
}
case 1:
{
lean_object* v___x_1130_; 
lean_dec(v_n_1109_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_e_1100_);
lean_ctor_set(v___x_1130_, 1, v_a_1105_);
return v___x_1130_;
}
case 4:
{
lean_object* v___x_1131_; 
lean_dec(v_n_1109_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_e_1100_);
lean_ctor_set(v___x_1131_, 1, v_a_1105_);
return v___x_1131_;
}
case 3:
{
lean_object* v___x_1132_; 
lean_dec(v_n_1109_);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_e_1100_);
lean_ctor_set(v___x_1132_, 1, v_a_1105_);
return v___x_1132_;
}
default: 
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v_fst_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
v___x_1133_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_1134_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_1109_, v_beginIdx_1101_, v_subst_1103_, v_e_1100_, v___x_1110_, v___x_1133_, v_a_1104_, v_a_1105_);
lean_dec(v_n_1109_);
v_fst_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_fst_1135_);
v_snd_1136_ = lean_ctor_get(v___x_1134_, 1);
lean_inc(v_snd_1136_);
lean_dec_ref(v___x_1134_);
v_fst_1137_ = lean_ctor_get(v_fst_1135_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_fst_1135_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_fst_1135_, 1);
lean_dec(v_unused_1145_);
v___x_1139_ = v_fst_1135_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_fst_1137_);
lean_dec(v_fst_1135_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_snd_1136_);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_fst_1137_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_snd_1136_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
else
{
lean_object* v___x_1146_; 
lean_dec(v_n_1109_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_e_1100_);
lean_ctor_set(v___x_1146_, 1, v_a_1105_);
return v___x_1146_;
}
}
}
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_dec_ref(v_e_1100_);
v___x_1147_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
v___x_1148_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1147_, v_a_1104_, v_a_1105_);
return v___x_1148_;
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec_ref(v_e_1100_);
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
v___x_1150_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_1149_, v_a_1104_, v_a_1105_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(lean_object* v_e_1151_, lean_object* v_beginIdx_1152_, lean_object* v_endIdx_1153_, lean_object* v_subst_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
uint8_t v_a_boxed_1157_; lean_object* v_res_1158_; 
v_a_boxed_1157_ = lean_unbox(v_a_1155_);
v_res_1158_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1151_, v_beginIdx_1152_, v_endIdx_1153_, v_subst_1154_, v_a_boxed_1157_, v_a_1156_);
lean_dec_ref(v_subst_1154_);
lean_dec(v_endIdx_1153_);
lean_dec(v_beginIdx_1152_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(lean_object* v_e_1159_, lean_object* v_subst_1160_, uint8_t v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_array_get_size(v_subst_1160_);
v___x_1165_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1159_, v___x_1163_, v___x_1164_, v_subst_1160_, v_a_1161_, v_a_1162_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(lean_object* v_e_1166_, lean_object* v_subst_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
uint8_t v_a_boxed_1170_; lean_object* v_res_1171_; 
v_a_boxed_1170_ = lean_unbox(v_a_1168_);
v_res_1171_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1166_, v_subst_1167_, v_a_boxed_1170_, v_a_1169_);
lean_dec_ref(v_subst_1167_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg(lean_object* v_e_1172_, lean_object* v_subst_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v_share_1177_; lean_object* v_maxFVar_1178_; lean_object* v_proofInstInfo_1179_; lean_object* v_inferType_1180_; lean_object* v_getLevel_1181_; lean_object* v_congrInfo_1182_; lean_object* v_defEqI_1183_; lean_object* v_extensions_1184_; lean_object* v_issues_1185_; uint8_t v_debug_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1220_; 
v___x_1176_ = lean_st_ref_take(v_a_1174_);
v_share_1177_ = lean_ctor_get(v___x_1176_, 0);
v_maxFVar_1178_ = lean_ctor_get(v___x_1176_, 1);
v_proofInstInfo_1179_ = lean_ctor_get(v___x_1176_, 2);
v_inferType_1180_ = lean_ctor_get(v___x_1176_, 3);
v_getLevel_1181_ = lean_ctor_get(v___x_1176_, 4);
v_congrInfo_1182_ = lean_ctor_get(v___x_1176_, 5);
v_defEqI_1183_ = lean_ctor_get(v___x_1176_, 6);
v_extensions_1184_ = lean_ctor_get(v___x_1176_, 7);
v_issues_1185_ = lean_ctor_get(v___x_1176_, 8);
v_debug_1186_ = lean_ctor_get_uint8(v___x_1176_, sizeof(void*)*9);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1188_ = v___x_1176_;
v_isShared_1189_ = v_isSharedCheck_1220_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_issues_1185_);
lean_inc(v_extensions_1184_);
lean_inc(v_defEqI_1183_);
lean_inc(v_congrInfo_1182_);
lean_inc(v_getLevel_1181_);
lean_inc(v_inferType_1180_);
lean_inc(v_proofInstInfo_1179_);
lean_inc(v_maxFVar_1178_);
lean_inc(v_share_1177_);
lean_dec(v___x_1176_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1220_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_maxFVar_1178_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_proofInstInfo_1179_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_inferType_1180_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v_getLevel_1181_);
lean_ctor_set(v_reuseFailAlloc_1219_, 5, v_congrInfo_1182_);
lean_ctor_set(v_reuseFailAlloc_1219_, 6, v_defEqI_1183_);
lean_ctor_set(v_reuseFailAlloc_1219_, 7, v_extensions_1184_);
lean_ctor_set(v_reuseFailAlloc_1219_, 8, v_issues_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*9, v_debug_1186_);
v___x_1192_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v_debug_1195_; lean_object* v___x_1196_; lean_object* v_fst_1197_; lean_object* v_snd_1198_; lean_object* v___x_1199_; lean_object* v_maxFVar_1200_; lean_object* v_proofInstInfo_1201_; lean_object* v_inferType_1202_; lean_object* v_getLevel_1203_; lean_object* v_congrInfo_1204_; lean_object* v_defEqI_1205_; lean_object* v_extensions_1206_; lean_object* v_issues_1207_; uint8_t v_debug_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1217_; 
v___x_1193_ = lean_st_ref_set(v_a_1174_, v___x_1192_);
v___x_1194_ = lean_st_ref_get(v_a_1174_);
v_debug_1195_ = lean_ctor_get_uint8(v___x_1194_, sizeof(void*)*9);
lean_dec(v___x_1194_);
v___x_1196_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_e_1172_, v_subst_1173_, v_debug_1195_, v_share_1177_);
v_fst_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_fst_1197_);
v_snd_1198_ = lean_ctor_get(v___x_1196_, 1);
lean_inc(v_snd_1198_);
lean_dec_ref(v___x_1196_);
v___x_1199_ = lean_st_ref_take(v_a_1174_);
v_maxFVar_1200_ = lean_ctor_get(v___x_1199_, 1);
v_proofInstInfo_1201_ = lean_ctor_get(v___x_1199_, 2);
v_inferType_1202_ = lean_ctor_get(v___x_1199_, 3);
v_getLevel_1203_ = lean_ctor_get(v___x_1199_, 4);
v_congrInfo_1204_ = lean_ctor_get(v___x_1199_, 5);
v_defEqI_1205_ = lean_ctor_get(v___x_1199_, 6);
v_extensions_1206_ = lean_ctor_get(v___x_1199_, 7);
v_issues_1207_ = lean_ctor_get(v___x_1199_, 8);
v_debug_1208_ = lean_ctor_get_uint8(v___x_1199_, sizeof(void*)*9);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v___x_1199_, 0);
lean_dec(v_unused_1218_);
v___x_1210_ = v___x_1199_;
v_isShared_1211_ = v_isSharedCheck_1217_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_issues_1207_);
lean_inc(v_extensions_1206_);
lean_inc(v_defEqI_1205_);
lean_inc(v_congrInfo_1204_);
lean_inc(v_getLevel_1203_);
lean_inc(v_inferType_1202_);
lean_inc(v_proofInstInfo_1201_);
lean_inc(v_maxFVar_1200_);
lean_dec(v___x_1199_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1217_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v_snd_1198_);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_snd_1198_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_maxFVar_1200_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_proofInstInfo_1201_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_inferType_1202_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_getLevel_1203_);
lean_ctor_set(v_reuseFailAlloc_1216_, 5, v_congrInfo_1204_);
lean_ctor_set(v_reuseFailAlloc_1216_, 6, v_defEqI_1205_);
lean_ctor_set(v_reuseFailAlloc_1216_, 7, v_extensions_1206_);
lean_ctor_set(v_reuseFailAlloc_1216_, 8, v_issues_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1216_, sizeof(void*)*9, v_debug_1208_);
v___x_1213_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_st_ref_set(v_a_1174_, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v_fst_1197_);
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___redArg___boxed(lean_object* v_e_1221_, lean_object* v_subst_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_1221_, v_subst_1222_, v_a_1223_);
lean_dec(v_a_1223_);
lean_dec_ref(v_subst_1222_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS(lean_object* v_e_1226_, lean_object* v_subst_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_1226_, v_subst_1227_, v_a_1229_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateS___boxed(lean_object* v_e_1236_, lean_object* v_subst_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Meta_Sym_instantiateS(v_e_1236_, v_subst_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec_ref(v_subst_1237_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(lean_object* v_f_1246_, lean_object* v_a_1247_, uint8_t v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___y_1251_; 
if (v___y_1248_ == 0)
{
v___y_1251_ = v___y_1249_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1254_; lean_object* v_snd_1255_; lean_object* v___x_1256_; lean_object* v_snd_1257_; 
lean_inc_ref(v_f_1246_);
v___x_1254_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1246_, v___y_1248_, v___y_1249_);
v_snd_1255_ = lean_ctor_get(v___x_1254_, 1);
lean_inc(v_snd_1255_);
lean_dec_ref(v___x_1254_);
lean_inc_ref(v_a_1247_);
v___x_1256_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1247_, v___y_1248_, v_snd_1255_);
v_snd_1257_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_snd_1257_);
lean_dec_ref(v___x_1256_);
v___y_1251_ = v_snd_1257_;
goto v___jp_1250_;
}
v___jp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lean_Expr_app___override(v_f_1246_, v_a_1247_);
v___x_1253_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1252_, v___y_1251_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0___boxed(lean_object* v_f_1258_, lean_object* v_a_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v___y_1244__boxed_1262_; lean_object* v_res_1263_; 
v___y_1244__boxed_1262_ = lean_unbox(v___y_1260_);
v_res_1263_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(v_f_1258_, v_a_1259_, v___y_1244__boxed_1262_, v___y_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(lean_object* v_revArgs_1264_, lean_object* v_start_1265_, lean_object* v_b_1266_, lean_object* v_i_1267_, uint8_t v_a_1268_, lean_object* v_a_1269_){
_start:
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_le(v_i_1267_, v_start_1265_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v_i_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_fst_1276_; lean_object* v_snd_1277_; 
v___x_1271_ = lean_unsigned_to_nat(1u);
v_i_1272_ = lean_nat_sub(v_i_1267_, v___x_1271_);
lean_dec(v_i_1267_);
v___x_1273_ = l_Lean_instInhabitedExpr;
v___x_1274_ = lean_array_get_borrowed(v___x_1273_, v_revArgs_1264_, v_i_1272_);
lean_inc(v___x_1274_);
v___x_1275_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop_spec__0(v_b_1266_, v___x_1274_, v_a_1268_, v_a_1269_);
v_fst_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_fst_1276_);
v_snd_1277_ = lean_ctor_get(v___x_1275_, 1);
lean_inc(v_snd_1277_);
lean_dec_ref(v___x_1275_);
v_b_1266_ = v_fst_1276_;
v_i_1267_ = v_i_1272_;
v_a_1269_ = v_snd_1277_;
goto _start;
}
else
{
lean_object* v___x_1279_; 
lean_dec(v_i_1267_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_b_1266_);
lean_ctor_set(v___x_1279_, 1, v_a_1269_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop___boxed(lean_object* v_revArgs_1280_, lean_object* v_start_1281_, lean_object* v_b_1282_, lean_object* v_i_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
uint8_t v_a_boxed_1286_; lean_object* v_res_1287_; 
v_a_boxed_1286_ = lean_unbox(v_a_1284_);
v_res_1287_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1280_, v_start_1281_, v_b_1282_, v_i_1283_, v_a_boxed_1286_, v_a_1285_);
lean_dec(v_start_1281_);
lean_dec_ref(v_revArgs_1280_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(lean_object* v_f_1288_, lean_object* v_beginIdx_1289_, lean_object* v_endIdx_1290_, lean_object* v_revArgs_1291_, uint8_t v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1291_, v_beginIdx_1289_, v_f_1288_, v_endIdx_1290_, v_a_1292_, v_a_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS___boxed(lean_object* v_f_1295_, lean_object* v_beginIdx_1296_, lean_object* v_endIdx_1297_, lean_object* v_revArgs_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
uint8_t v_a_boxed_1301_; lean_object* v_res_1302_; 
v_a_boxed_1301_ = lean_unbox(v_a_1299_);
v_res_1302_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS(v_f_1295_, v_beginIdx_1296_, v_endIdx_1297_, v_revArgs_1298_, v_a_boxed_1301_, v_a_1300_);
lean_dec_ref(v_revArgs_1298_);
lean_dec(v_beginIdx_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(lean_object* v_revArgs_1303_, lean_object* v_sz_1304_, lean_object* v_e_1305_, lean_object* v_i_1306_, uint8_t v_a_1307_, lean_object* v_a_1308_){
_start:
{
switch(lean_obj_tag(v_e_1305_))
{
case 6:
{
lean_object* v_body_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_body_1309_ = lean_ctor_get(v_e_1305_, 2);
lean_inc_ref(v_body_1309_);
lean_dec_ref(v_e_1305_);
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_nat_add(v_i_1306_, v___x_1310_);
lean_dec(v_i_1306_);
v___x_1312_ = lean_nat_dec_lt(v___x_1311_, v_sz_1304_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v___x_1311_);
v___x_1313_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_1309_, v_revArgs_1303_, v_a_1307_, v_a_1308_);
return v___x_1313_;
}
else
{
v_e_1305_ = v_body_1309_;
v_i_1306_ = v___x_1311_;
goto _start;
}
}
case 10:
{
lean_object* v_expr_1315_; 
v_expr_1315_ = lean_ctor_get(v_e_1305_, 1);
lean_inc_ref(v_expr_1315_);
lean_dec_ref(v_e_1305_);
v_e_1305_ = v_expr_1315_;
goto _start;
}
default: 
{
lean_object* v_n_1317_; lean_object* v___x_1318_; lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_n_1317_ = lean_nat_sub(v_sz_1304_, v_i_1306_);
lean_dec(v_i_1306_);
v___x_1318_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_1305_, v_n_1317_, v_sz_1304_, v_revArgs_1303_, v_a_1307_, v_a_1308_);
v_fst_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_fst_1319_);
v_snd_1320_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_snd_1320_);
lean_dec_ref(v___x_1318_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_mkAppRevRangeS_loop(v_revArgs_1303_, v___x_1321_, v_fst_1319_, v_n_1317_, v_a_1307_, v_snd_1320_);
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go___boxed(lean_object* v_revArgs_1323_, lean_object* v_sz_1324_, lean_object* v_e_1325_, lean_object* v_i_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
uint8_t v_a_boxed_1329_; lean_object* v_res_1330_; 
v_a_boxed_1329_ = lean_unbox(v_a_1327_);
v_res_1330_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(v_revArgs_1323_, v_sz_1324_, v_e_1325_, v_i_1326_, v_a_boxed_1329_, v_a_1328_);
lean_dec(v_sz_1324_);
lean_dec_ref(v_revArgs_1323_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(lean_object* v_f_1331_, lean_object* v_revArgs_1332_, uint8_t v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_sz_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_sz_1335_ = lean_array_get_size(v_revArgs_1332_);
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_nat_dec_eq(v_sz_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_go(v_revArgs_1332_, v_sz_1335_, v_f_1331_, v___x_1336_, v_a_1333_, v_a_1334_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_f_1331_);
lean_ctor_set(v___x_1339_, 1, v_a_1334_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS___boxed(lean_object* v_f_1340_, lean_object* v_revArgs_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
uint8_t v_a_boxed_1344_; lean_object* v_res_1345_; 
v_a_boxed_1344_ = lean_unbox(v_a_1342_);
v_res_1345_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(v_f_1340_, v_revArgs_1341_, v_a_boxed_1344_, v_a_1343_);
lean_dec_ref(v_revArgs_1341_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
if (lean_obj_tag(v_x_1347_) == 0)
{
return v_x_1346_;
}
else
{
lean_object* v_key_1348_; lean_object* v_value_1349_; lean_object* v_tail_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1377_; 
v_key_1348_ = lean_ctor_get(v_x_1347_, 0);
v_value_1349_ = lean_ctor_get(v_x_1347_, 1);
v_tail_1350_ = lean_ctor_get(v_x_1347_, 2);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1347_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1352_ = v_x_1347_;
v_isShared_1353_ = v_isSharedCheck_1377_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_tail_1350_);
lean_inc(v_value_1349_);
lean_inc(v_key_1348_);
lean_dec(v_x_1347_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1377_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; uint64_t v___x_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; uint64_t v_fold_1362_; uint64_t v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; size_t v___x_1368_; size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v_fst_1354_ = lean_ctor_get(v_key_1348_, 0);
v_snd_1355_ = lean_ctor_get(v_key_1348_, 1);
v___x_1356_ = lean_array_get_size(v_x_1346_);
v___x_1357_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1354_);
v___x_1358_ = lean_uint64_of_nat(v_snd_1355_);
v___x_1359_ = lean_uint64_mix_hash(v___x_1357_, v___x_1358_);
v___x_1360_ = 32ULL;
v___x_1361_ = lean_uint64_shift_right(v___x_1359_, v___x_1360_);
v_fold_1362_ = lean_uint64_xor(v___x_1359_, v___x_1361_);
v___x_1363_ = 16ULL;
v___x_1364_ = lean_uint64_shift_right(v_fold_1362_, v___x_1363_);
v___x_1365_ = lean_uint64_xor(v_fold_1362_, v___x_1364_);
v___x_1366_ = lean_uint64_to_usize(v___x_1365_);
v___x_1367_ = lean_usize_of_nat(v___x_1356_);
v___x_1368_ = ((size_t)1ULL);
v___x_1369_ = lean_usize_sub(v___x_1367_, v___x_1368_);
v___x_1370_ = lean_usize_land(v___x_1366_, v___x_1369_);
v___x_1371_ = lean_array_uget_borrowed(v_x_1346_, v___x_1370_);
lean_inc(v___x_1371_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 2, v___x_1371_);
v___x_1373_ = v___x_1352_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_key_1348_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_value_1349_);
lean_ctor_set(v_reuseFailAlloc_1376_, 2, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_array_uset(v_x_1346_, v___x_1370_, v___x_1373_);
v_x_1346_ = v___x_1374_;
v_x_1347_ = v_tail_1350_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1378_, lean_object* v_source_1379_, lean_object* v_target_1380_){
_start:
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = lean_array_get_size(v_source_1379_);
v___x_1382_ = lean_nat_dec_lt(v_i_1378_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v_source_1379_);
lean_dec(v_i_1378_);
return v_target_1380_;
}
else
{
lean_object* v_es_1383_; lean_object* v___x_1384_; lean_object* v_source_1385_; lean_object* v_target_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_es_1383_ = lean_array_fget(v_source_1379_, v_i_1378_);
v___x_1384_ = lean_box(0);
v_source_1385_ = lean_array_fset(v_source_1379_, v_i_1378_, v___x_1384_);
v_target_1386_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1380_, v_es_1383_);
v___x_1387_ = lean_unsigned_to_nat(1u);
v___x_1388_ = lean_nat_add(v_i_1378_, v___x_1387_);
lean_dec(v_i_1378_);
v_i_1378_ = v___x_1388_;
v_source_1379_ = v_source_1385_;
v_target_1380_ = v_target_1386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(lean_object* v_data_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_nbuckets_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1391_ = lean_array_get_size(v_data_1390_);
v___x_1392_ = lean_unsigned_to_nat(2u);
v_nbuckets_1393_ = lean_nat_mul(v___x_1391_, v___x_1392_);
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_mk_array(v_nbuckets_1393_, v___x_1395_);
v___x_1397_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_1394_, v_data_1390_, v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(lean_object* v_a_1398_, lean_object* v_b_1399_, lean_object* v_x_1400_){
_start:
{
if (lean_obj_tag(v_x_1400_) == 0)
{
lean_dec(v_b_1399_);
lean_dec_ref(v_a_1398_);
return v_x_1400_;
}
else
{
lean_object* v_key_1401_; lean_object* v_value_1402_; lean_object* v_tail_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1422_; 
v_key_1401_ = lean_ctor_get(v_x_1400_, 0);
v_value_1402_ = lean_ctor_get(v_x_1400_, 1);
v_tail_1403_ = lean_ctor_get(v_x_1400_, 2);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1400_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1405_ = v_x_1400_;
v_isShared_1406_ = v_isSharedCheck_1422_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_tail_1403_);
lean_inc(v_value_1402_);
lean_inc(v_key_1401_);
lean_dec(v_x_1400_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1422_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
uint8_t v___y_1408_; lean_object* v_fst_1416_; lean_object* v_snd_1417_; lean_object* v_fst_1418_; lean_object* v_snd_1419_; uint8_t v___x_1420_; 
v_fst_1416_ = lean_ctor_get(v_key_1401_, 0);
v_snd_1417_ = lean_ctor_get(v_key_1401_, 1);
v_fst_1418_ = lean_ctor_get(v_a_1398_, 0);
v_snd_1419_ = lean_ctor_get(v_a_1398_, 1);
v___x_1420_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1416_, v_fst_1418_);
if (v___x_1420_ == 0)
{
v___y_1408_ = v___x_1420_;
goto v___jp_1407_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_nat_dec_eq(v_snd_1417_, v_snd_1419_);
v___y_1408_ = v___x_1421_;
goto v___jp_1407_;
}
v___jp_1407_:
{
if (v___y_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1398_, v_b_1399_, v_tail_1403_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 2, v___x_1409_);
v___x_1411_ = v___x_1405_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_key_1401_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_value_1402_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
else
{
lean_object* v___x_1414_; 
lean_dec(v_value_1402_);
lean_dec(v_key_1401_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 1, v_b_1399_);
lean_ctor_set(v___x_1405_, 0, v_a_1398_);
v___x_1414_ = v___x_1405_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1398_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_b_1399_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_tail_1403_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(lean_object* v_a_1423_, lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = 0;
return v___x_1425_;
}
else
{
lean_object* v_key_1426_; lean_object* v_tail_1427_; uint8_t v___y_1429_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v_fst_1433_; lean_object* v_snd_1434_; uint8_t v___x_1435_; 
v_key_1426_ = lean_ctor_get(v_x_1424_, 0);
v_tail_1427_ = lean_ctor_get(v_x_1424_, 2);
v_fst_1431_ = lean_ctor_get(v_key_1426_, 0);
v_snd_1432_ = lean_ctor_get(v_key_1426_, 1);
v_fst_1433_ = lean_ctor_get(v_a_1423_, 0);
v_snd_1434_ = lean_ctor_get(v_a_1423_, 1);
v___x_1435_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1431_, v_fst_1433_);
if (v___x_1435_ == 0)
{
v___y_1429_ = v___x_1435_;
goto v___jp_1428_;
}
else
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_nat_dec_eq(v_snd_1432_, v_snd_1434_);
v___y_1429_ = v___x_1436_;
goto v___jp_1428_;
}
v___jp_1428_:
{
if (v___y_1429_ == 0)
{
v_x_1424_ = v_tail_1427_;
goto _start;
}
else
{
return v___y_1429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(lean_object* v_a_1437_, lean_object* v_x_1438_){
_start:
{
uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_res_1439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1437_, v_x_1438_);
lean_dec(v_x_1438_);
lean_dec_ref(v_a_1437_);
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(lean_object* v_m_1441_, lean_object* v_a_1442_, lean_object* v_b_1443_){
_start:
{
lean_object* v_size_1444_; lean_object* v_buckets_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1492_; 
v_size_1444_ = lean_ctor_get(v_m_1441_, 0);
v_buckets_1445_ = lean_ctor_get(v_m_1441_, 1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_m_1441_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1447_ = v_m_1441_;
v_isShared_1448_ = v_isSharedCheck_1492_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_buckets_1445_);
lean_inc(v_size_1444_);
lean_dec(v_m_1441_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1492_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_fst_1449_; lean_object* v_snd_1450_; lean_object* v___x_1451_; uint64_t v___x_1452_; uint64_t v___x_1453_; uint64_t v___x_1454_; uint64_t v___x_1455_; uint64_t v___x_1456_; uint64_t v_fold_1457_; uint64_t v___x_1458_; uint64_t v___x_1459_; uint64_t v___x_1460_; size_t v___x_1461_; size_t v___x_1462_; size_t v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; lean_object* v_bkt_1466_; uint8_t v___x_1467_; 
v_fst_1449_ = lean_ctor_get(v_a_1442_, 0);
v_snd_1450_ = lean_ctor_get(v_a_1442_, 1);
v___x_1451_ = lean_array_get_size(v_buckets_1445_);
v___x_1452_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1449_);
v___x_1453_ = lean_uint64_of_nat(v_snd_1450_);
v___x_1454_ = lean_uint64_mix_hash(v___x_1452_, v___x_1453_);
v___x_1455_ = 32ULL;
v___x_1456_ = lean_uint64_shift_right(v___x_1454_, v___x_1455_);
v_fold_1457_ = lean_uint64_xor(v___x_1454_, v___x_1456_);
v___x_1458_ = 16ULL;
v___x_1459_ = lean_uint64_shift_right(v_fold_1457_, v___x_1458_);
v___x_1460_ = lean_uint64_xor(v_fold_1457_, v___x_1459_);
v___x_1461_ = lean_uint64_to_usize(v___x_1460_);
v___x_1462_ = lean_usize_of_nat(v___x_1451_);
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_sub(v___x_1462_, v___x_1463_);
v___x_1465_ = lean_usize_land(v___x_1461_, v___x_1464_);
v_bkt_1466_ = lean_array_uget_borrowed(v_buckets_1445_, v___x_1465_);
v___x_1467_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1442_, v_bkt_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v_size_x27_1469_; lean_object* v___x_1470_; lean_object* v_buckets_x27_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v___x_1468_ = lean_unsigned_to_nat(1u);
v_size_x27_1469_ = lean_nat_add(v_size_1444_, v___x_1468_);
lean_dec(v_size_1444_);
lean_inc(v_bkt_1466_);
v___x_1470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1442_);
lean_ctor_set(v___x_1470_, 1, v_b_1443_);
lean_ctor_set(v___x_1470_, 2, v_bkt_1466_);
v_buckets_x27_1471_ = lean_array_uset(v_buckets_1445_, v___x_1465_, v___x_1470_);
v___x_1472_ = lean_unsigned_to_nat(4u);
v___x_1473_ = lean_nat_mul(v_size_x27_1469_, v___x_1472_);
v___x_1474_ = lean_unsigned_to_nat(3u);
v___x_1475_ = lean_nat_div(v___x_1473_, v___x_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_array_get_size(v_buckets_x27_1471_);
v___x_1477_ = lean_nat_dec_le(v___x_1475_, v___x_1476_);
lean_dec(v___x_1475_);
if (v___x_1477_ == 0)
{
lean_object* v_val_1478_; lean_object* v___x_1480_; 
v_val_1478_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_1471_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 1, v_val_1478_);
lean_ctor_set(v___x_1447_, 0, v_size_x27_1469_);
v___x_1480_ = v___x_1447_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_size_x27_1469_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_val_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
else
{
lean_object* v___x_1483_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 1, v_buckets_x27_1471_);
lean_ctor_set(v___x_1447_, 0, v_size_x27_1469_);
v___x_1483_ = v___x_1447_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_size_x27_1469_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_buckets_x27_1471_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
lean_object* v___x_1485_; lean_object* v_buckets_x27_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
lean_inc(v_bkt_1466_);
v___x_1485_ = lean_box(0);
v_buckets_x27_1486_ = lean_array_uset(v_buckets_1445_, v___x_1465_, v___x_1485_);
v___x_1487_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1442_, v_b_1443_, v_bkt_1466_);
v___x_1488_ = lean_array_uset(v_buckets_x27_1486_, v___x_1465_, v___x_1487_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 1, v___x_1488_);
v___x_1490_ = v___x_1447_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_size_1444_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(lean_object* v_key_1493_, lean_object* v_r_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_inc_ref(v_r_1494_);
v___x_1497_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_1495_, v_key_1493_, v_r_1494_);
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v_r_1494_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v_a_1496_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(lean_object* v_key_1500_, lean_object* v_r_1501_, lean_object* v_a_1502_, uint8_t v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1500_, v_r_1501_, v_a_1502_, v_a_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(lean_object* v_key_1506_, lean_object* v_r_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
uint8_t v_a_boxed_1511_; lean_object* v_res_1512_; 
v_a_boxed_1511_ = lean_unbox(v_a_1509_);
v_res_1512_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(v_key_1506_, v_r_1507_, v_a_1508_, v_a_boxed_1511_, v_a_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(lean_object* v_00_u03b2_1513_, lean_object* v_m_1514_, lean_object* v_a_1515_, lean_object* v_b_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_1514_, v_a_1515_, v_b_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(lean_object* v_00_u03b2_1518_, lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_1519_, v_x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1522_, lean_object* v_a_1523_, lean_object* v_x_1524_){
_start:
{
uint8_t v_res_1525_; lean_object* v_r_1526_; 
v_res_1525_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_1522_, v_a_1523_, v_x_1524_);
lean_dec(v_x_1524_);
lean_dec_ref(v_a_1523_);
v_r_1526_ = lean_box(v_res_1525_);
return v_r_1526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(lean_object* v_00_u03b2_1527_, lean_object* v_data_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(lean_object* v_00_u03b2_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_, lean_object* v_x_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_1531_, v_b_1532_, v_x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1535_, lean_object* v_i_1536_, lean_object* v_source_1537_, lean_object* v_target_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_1536_, v_source_1537_, v_target_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1541_, v_x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(lean_object* v_idx_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v_fst_1549_; lean_object* v_snd_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1558_; 
v___x_1547_ = l_Lean_Expr_bvar___override(v_idx_1544_);
v___x_1548_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1547_, v___y_1546_);
v_fst_1549_ = lean_ctor_get(v___x_1548_, 0);
v_snd_1550_ = lean_ctor_get(v___x_1548_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1552_ = v___x_1548_;
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_snd_1550_);
lean_inc(v_fst_1549_);
lean_dec(v___x_1548_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1558_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 1, v___y_1545_);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_fst_1549_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___y_1545_);
v___x_1555_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_snd_1550_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(lean_object* v_idx_1559_, lean_object* v___y_1560_, uint8_t v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_1559_, v___y_1560_, v___y_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(lean_object* v_idx_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v___y_1291__boxed_1568_; lean_object* v_res_1569_; 
v___y_1291__boxed_1568_ = lean_unbox(v___y_1566_);
v_res_1569_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_1564_, v___y_1565_, v___y_1291__boxed_1568_, v___y_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(lean_object* v_subst_1570_, lean_object* v_e_1571_, lean_object* v_bidx_1572_, lean_object* v_offset_1573_, lean_object* v_a_1574_, uint8_t v_a_1575_, lean_object* v_a_1576_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_le(v_offset_1573_, v_bidx_1572_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v_e_1571_);
lean_ctor_set(v___x_1578_, 1, v_a_1574_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v_a_1576_);
return v___x_1579_;
}
else
{
lean_object* v_n_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
lean_dec_ref(v_e_1571_);
v_n_1580_ = lean_array_get_size(v_subst_1570_);
v___x_1581_ = lean_nat_add(v_offset_1573_, v_n_1580_);
v___x_1582_ = lean_nat_dec_lt(v_bidx_1572_, v___x_1581_);
lean_dec(v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_nat_sub(v_bidx_1572_, v_n_1580_);
v___x_1584_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_1583_, v_a_1574_, v_a_1576_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_v_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v_fst_1592_; lean_object* v_snd_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1601_; 
v___x_1585_ = lean_nat_sub(v_bidx_1572_, v_offset_1573_);
v___x_1586_ = lean_nat_sub(v_n_1580_, v___x_1585_);
lean_dec(v___x_1585_);
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = lean_nat_sub(v___x_1586_, v___x_1587_);
lean_dec(v___x_1586_);
v_v_1589_ = lean_array_fget_borrowed(v_subst_1570_, v___x_1588_);
lean_dec(v___x_1588_);
v___x_1590_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_1589_);
v___x_1591_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_v_1589_, v___x_1590_, v_offset_1573_, v_a_1575_, v_a_1576_);
v_fst_1592_ = lean_ctor_get(v___x_1591_, 0);
v_snd_1593_ = lean_ctor_get(v___x_1591_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1595_ = v___x_1591_;
v_isShared_1596_ = v_isSharedCheck_1601_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_snd_1593_);
lean_inc(v_fst_1592_);
lean_dec(v___x_1591_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1601_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 1, v_a_1574_);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_fst_1592_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_a_1574_);
v___x_1598_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
lean_ctor_set(v___x_1599_, 1, v_snd_1593_);
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(lean_object* v_subst_1602_, lean_object* v_e_1603_, lean_object* v_bidx_1604_, lean_object* v_offset_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
uint8_t v_a_boxed_1609_; lean_object* v_res_1610_; 
v_a_boxed_1609_ = lean_unbox(v_a_1607_);
v_res_1610_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1602_, v_e_1603_, v_bidx_1604_, v_offset_1605_, v_a_1606_, v_a_boxed_1609_, v_a_1608_);
lean_dec(v_offset_1605_);
lean_dec(v_bidx_1604_);
lean_dec_ref(v_subst_1602_);
return v_res_1610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2));
v___x_1615_ = lean_unsigned_to_nat(25u);
v___x_1616_ = lean_unsigned_to_nat(148u);
v___x_1617_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1));
v___x_1618_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0));
v___x_1619_ = l_mkPanicMessageWithDecl(v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_, v___x_1614_);
return v___x_1619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1622_ = lean_unsigned_to_nat(11u);
v___x_1623_ = lean_unsigned_to_nat(179u);
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0));
v___x_1625_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1626_ = l_mkPanicMessageWithDecl(v___x_1625_, v___x_1624_, v___x_1623_, v___x_1622_, v___x_1621_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(lean_object* v_subst_1627_, lean_object* v_e_1628_, lean_object* v_f_1629_, lean_object* v_argsRev_1630_, lean_object* v_offset_1631_, uint8_t v_modified_1632_, lean_object* v_a_1633_, uint8_t v_a_1634_, lean_object* v_a_1635_){
_start:
{
switch(lean_obj_tag(v_f_1629_))
{
case 5:
{
lean_object* v_fn_1636_; lean_object* v_arg_1637_; lean_object* v___x_1638_; lean_object* v_fst_1639_; lean_object* v_snd_1640_; lean_object* v_fst_1641_; lean_object* v_snd_1642_; lean_object* v___x_1643_; 
v_fn_1636_ = lean_ctor_get(v_f_1629_, 0);
lean_inc_ref(v_fn_1636_);
v_arg_1637_ = lean_ctor_get(v_f_1629_, 1);
lean_inc_ref(v_arg_1637_);
lean_dec_ref(v_f_1629_);
lean_inc(v_offset_1631_);
lean_inc_ref(v_arg_1637_);
v___x_1638_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1627_, v_arg_1637_, v_offset_1631_, v_a_1633_, v_a_1634_, v_a_1635_);
v_fst_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_fst_1639_);
v_snd_1640_ = lean_ctor_get(v___x_1638_, 1);
lean_inc(v_snd_1640_);
lean_dec_ref(v___x_1638_);
v_fst_1641_ = lean_ctor_get(v_fst_1639_, 0);
lean_inc(v_fst_1641_);
v_snd_1642_ = lean_ctor_get(v_fst_1639_, 1);
lean_inc(v_snd_1642_);
lean_dec(v_fst_1639_);
lean_inc(v_fst_1641_);
v___x_1643_ = lean_array_push(v_argsRev_1630_, v_fst_1641_);
if (v_modified_1632_ == 0)
{
uint8_t v___x_1644_; 
v___x_1644_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1637_, v_fst_1641_);
lean_dec(v_fst_1641_);
lean_dec_ref(v_arg_1637_);
if (v___x_1644_ == 0)
{
uint8_t v___x_1645_; 
v___x_1645_ = 1;
v_f_1629_ = v_fn_1636_;
v_argsRev_1630_ = v___x_1643_;
v_modified_1632_ = v___x_1645_;
v_a_1633_ = v_snd_1642_;
v_a_1635_ = v_snd_1640_;
goto _start;
}
else
{
v_f_1629_ = v_fn_1636_;
v_argsRev_1630_ = v___x_1643_;
v_a_1633_ = v_snd_1642_;
v_a_1635_ = v_snd_1640_;
goto _start;
}
}
else
{
lean_dec(v_fst_1641_);
lean_dec_ref(v_arg_1637_);
v_f_1629_ = v_fn_1636_;
v_argsRev_1630_ = v___x_1643_;
v_a_1633_ = v_snd_1642_;
v_a_1635_ = v_snd_1640_;
goto _start;
}
}
case 0:
{
lean_object* v_deBruijnIndex_1649_; lean_object* v___x_1650_; lean_object* v_fst_1651_; lean_object* v_snd_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1681_; 
v_deBruijnIndex_1649_ = lean_ctor_get(v_f_1629_, 0);
lean_inc_ref(v_f_1629_);
v___x_1650_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1627_, v_f_1629_, v_deBruijnIndex_1649_, v_offset_1631_, v_a_1633_, v_a_1634_, v_a_1635_);
lean_dec(v_offset_1631_);
v_fst_1651_ = lean_ctor_get(v___x_1650_, 0);
v_snd_1652_ = lean_ctor_get(v___x_1650_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1654_ = v___x_1650_;
v_isShared_1655_ = v_isSharedCheck_1681_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_snd_1652_);
lean_inc(v_fst_1651_);
lean_dec(v___x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1681_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_fst_1656_; lean_object* v_snd_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1680_; 
v_fst_1656_ = lean_ctor_get(v_fst_1651_, 0);
v_snd_1657_ = lean_ctor_get(v_fst_1651_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_fst_1651_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1659_ = v_fst_1651_;
v_isShared_1660_ = v_isSharedCheck_1680_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_snd_1657_);
lean_inc(v_fst_1656_);
lean_dec(v_fst_1651_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1680_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
if (v_modified_1632_ == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_f_1629_, v_fst_1656_);
lean_dec_ref(v_f_1629_);
if (v___x_1675_ == 0)
{
lean_del_object(v___x_1654_);
lean_dec_ref(v_e_1628_);
goto v___jp_1661_;
}
else
{
lean_object* v___x_1677_; 
lean_del_object(v___x_1659_);
lean_dec(v_fst_1656_);
lean_dec_ref(v_argsRev_1630_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v_snd_1657_);
lean_ctor_set(v___x_1654_, 0, v_e_1628_);
v___x_1677_ = v___x_1654_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_e_1628_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_snd_1657_);
v___x_1677_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_snd_1652_);
return v___x_1678_;
}
}
}
else
{
lean_del_object(v___x_1654_);
lean_dec_ref(v_f_1629_);
lean_dec_ref(v_e_1628_);
goto v___jp_1661_;
}
v___jp_1661_:
{
lean_object* v___x_1662_; lean_object* v_fst_1663_; lean_object* v_snd_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1674_; 
v___x_1662_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS(v_fst_1656_, v_argsRev_1630_, v_a_1634_, v_snd_1652_);
lean_dec_ref(v_argsRev_1630_);
v_fst_1663_ = lean_ctor_get(v___x_1662_, 0);
v_snd_1664_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1666_ = v___x_1662_;
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_snd_1664_);
lean_inc(v_fst_1663_);
lean_dec(v___x_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v_snd_1657_);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_fst_1663_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_snd_1657_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v_snd_1664_);
lean_ctor_set(v___x_1659_, 0, v___x_1669_);
v___x_1671_ = v___x_1659_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_snd_1664_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec(v_offset_1631_);
lean_dec_ref(v_argsRev_1630_);
lean_dec_ref(v_f_1629_);
lean_dec_ref(v_e_1628_);
v___x_1682_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
v___x_1683_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1682_, v_a_1633_, v_a_1634_, v_a_1635_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(lean_object* v_subst_1684_, lean_object* v_e_1685_, lean_object* v_f_1686_, lean_object* v_arg_1687_, lean_object* v_offset_1688_, lean_object* v_a_1689_, uint8_t v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v_fst_1693_; lean_object* v_snd_1694_; lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
lean_inc(v_offset_1688_);
lean_inc_ref(v_arg_1687_);
v___x_1692_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1684_, v_arg_1687_, v_offset_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
v_fst_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_fst_1693_);
v_snd_1694_ = lean_ctor_get(v___x_1692_, 1);
lean_inc(v_snd_1694_);
lean_dec_ref(v___x_1692_);
v_fst_1695_ = lean_ctor_get(v_fst_1693_, 0);
lean_inc(v_fst_1695_);
v_snd_1696_ = lean_ctor_get(v_fst_1693_, 1);
lean_inc(v_snd_1696_);
lean_dec(v_fst_1693_);
v___x_1697_ = l_Lean_Expr_getAppFn(v_f_1686_);
v___x_1698_ = l_Lean_Expr_isBVar(v___x_1697_);
lean_dec_ref(v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v_fst_1700_; lean_object* v_snd_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v_arg_1687_);
v___x_1699_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1684_, v_f_1686_, v_offset_1688_, v_snd_1696_, v_a_1690_, v_snd_1694_);
v_fst_1700_ = lean_ctor_get(v___x_1699_, 0);
v_snd_1701_ = lean_ctor_get(v___x_1699_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1703_ = v___x_1699_;
v_isShared_1704_ = v_isSharedCheck_1726_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snd_1701_);
lean_inc(v_fst_1700_);
lean_dec(v___x_1699_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1726_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_fst_1705_; lean_object* v_snd_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1725_; 
v_fst_1705_ = lean_ctor_get(v_fst_1700_, 0);
v_snd_1706_ = lean_ctor_get(v_fst_1700_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_fst_1700_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1708_ = v_fst_1700_;
v_isShared_1709_ = v_isSharedCheck_1725_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snd_1706_);
lean_inc(v_fst_1705_);
lean_dec(v_fst_1700_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1725_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
uint8_t v___y_1711_; 
if (lean_obj_tag(v_e_1685_) == 5)
{
lean_object* v_fn_1719_; lean_object* v_arg_1720_; uint8_t v___x_1721_; 
v_fn_1719_ = lean_ctor_get(v_e_1685_, 0);
v_arg_1720_ = lean_ctor_get(v_e_1685_, 1);
v___x_1721_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1719_, v_fst_1705_);
if (v___x_1721_ == 0)
{
v___y_1711_ = v___x_1721_;
goto v___jp_1710_;
}
else
{
uint8_t v___x_1722_; 
v___x_1722_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1720_, v_fst_1695_);
v___y_1711_ = v___x_1722_;
goto v___jp_1710_;
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
lean_del_object(v___x_1708_);
lean_dec(v_fst_1705_);
lean_del_object(v___x_1703_);
lean_dec(v_fst_1695_);
lean_dec_ref(v_e_1685_);
v___x_1723_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3);
v___x_1724_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1723_, v_snd_1706_, v_a_1690_, v_snd_1701_);
return v___x_1724_;
}
v___jp_1710_:
{
if (v___y_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_del_object(v___x_1708_);
lean_del_object(v___x_1703_);
lean_dec_ref(v_e_1685_);
v___x_1712_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1705_, v_fst_1695_, v_snd_1706_, v_a_1690_, v_snd_1701_);
return v___x_1712_;
}
else
{
lean_object* v___x_1714_; 
lean_dec(v_fst_1705_);
lean_dec(v_fst_1695_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v_e_1685_);
v___x_1714_ = v___x_1708_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_e_1685_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_snd_1706_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1714_);
v___x_1716_ = v___x_1703_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_snd_1701_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_mk_empty_array_with_capacity(v___x_1727_);
lean_inc(v_fst_1695_);
v___x_1729_ = lean_array_push(v___x_1728_, v_fst_1695_);
v___x_1730_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1687_, v_fst_1695_);
lean_dec(v_fst_1695_);
lean_dec_ref(v_arg_1687_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
v___x_1731_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1684_, v_e_1685_, v_f_1686_, v___x_1729_, v_offset_1688_, v___x_1698_, v_snd_1696_, v_a_1690_, v_snd_1694_);
return v___x_1731_;
}
else
{
uint8_t v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = 0;
v___x_1733_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_1684_, v_e_1685_, v_f_1686_, v___x_1729_, v_offset_1688_, v___x_1732_, v_snd_1696_, v_a_1690_, v_snd_1694_);
return v___x_1733_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1(void){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2));
v___x_1736_ = lean_unsigned_to_nat(59u);
v___x_1737_ = lean_unsigned_to_nat(190u);
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0));
v___x_1739_ = ((lean_object*)(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3));
v___x_1740_ = l_mkPanicMessageWithDecl(v___x_1739_, v___x_1738_, v___x_1737_, v___x_1736_, v___x_1735_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(lean_object* v_subst_1741_, lean_object* v_e_1742_, lean_object* v_offset_1743_, lean_object* v_a_1744_, uint8_t v_a_1745_, lean_object* v_a_1746_){
_start:
{
switch(lean_obj_tag(v_e_1742_))
{
case 0:
{
lean_object* v_deBruijnIndex_1747_; lean_object* v___x_1748_; 
v_deBruijnIndex_1747_ = lean_ctor_get(v_e_1742_, 0);
lean_inc(v_deBruijnIndex_1747_);
v___x_1748_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1741_, v_e_1742_, v_deBruijnIndex_1747_, v_offset_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_offset_1743_);
lean_dec(v_deBruijnIndex_1747_);
return v___x_1748_;
}
case 5:
{
lean_object* v_fn_1749_; lean_object* v_arg_1750_; lean_object* v___x_1751_; 
v_fn_1749_ = lean_ctor_get(v_e_1742_, 0);
lean_inc_ref(v_fn_1749_);
v_arg_1750_ = lean_ctor_get(v_e_1742_, 1);
lean_inc_ref(v_arg_1750_);
v___x_1751_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1741_, v_e_1742_, v_fn_1749_, v_arg_1750_, v_offset_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
return v___x_1751_;
}
case 6:
{
lean_object* v_binderName_1752_; lean_object* v_binderType_1753_; lean_object* v_body_1754_; uint8_t v_binderInfo_1755_; lean_object* v___x_1756_; lean_object* v_fst_1757_; lean_object* v_snd_1758_; lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v_fst_1764_; lean_object* v_snd_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1786_; 
v_binderName_1752_ = lean_ctor_get(v_e_1742_, 0);
v_binderType_1753_ = lean_ctor_get(v_e_1742_, 1);
v_body_1754_ = lean_ctor_get(v_e_1742_, 2);
v_binderInfo_1755_ = lean_ctor_get_uint8(v_e_1742_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1743_);
lean_inc_ref(v_binderType_1753_);
v___x_1756_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_binderType_1753_, v_offset_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
v_fst_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_fst_1757_);
v_snd_1758_ = lean_ctor_get(v___x_1756_, 1);
lean_inc(v_snd_1758_);
lean_dec_ref(v___x_1756_);
v_fst_1759_ = lean_ctor_get(v_fst_1757_, 0);
lean_inc(v_fst_1759_);
v_snd_1760_ = lean_ctor_get(v_fst_1757_, 1);
lean_inc(v_snd_1760_);
lean_dec(v_fst_1757_);
v___x_1761_ = lean_unsigned_to_nat(1u);
v___x_1762_ = lean_nat_add(v_offset_1743_, v___x_1761_);
lean_dec(v_offset_1743_);
lean_inc_ref(v_body_1754_);
v___x_1763_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_body_1754_, v___x_1762_, v_snd_1760_, v_a_1745_, v_snd_1758_);
v_fst_1764_ = lean_ctor_get(v___x_1763_, 0);
v_snd_1765_ = lean_ctor_get(v___x_1763_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1767_ = v___x_1763_;
v_isShared_1768_ = v_isSharedCheck_1786_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snd_1765_);
lean_inc(v_fst_1764_);
lean_dec(v___x_1763_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1786_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1785_; 
v_fst_1769_ = lean_ctor_get(v_fst_1764_, 0);
v_snd_1770_ = lean_ctor_get(v_fst_1764_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_fst_1764_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1772_ = v_fst_1764_;
v_isShared_1773_ = v_isSharedCheck_1785_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_snd_1770_);
lean_inc(v_fst_1769_);
lean_dec(v_fst_1764_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1785_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
uint8_t v___y_1775_; uint8_t v___x_1783_; 
v___x_1783_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1753_, v_fst_1759_);
if (v___x_1783_ == 0)
{
v___y_1775_ = v___x_1783_;
goto v___jp_1774_;
}
else
{
uint8_t v___x_1784_; 
v___x_1784_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1754_, v_fst_1769_);
v___y_1775_ = v___x_1784_;
goto v___jp_1774_;
}
v___jp_1774_:
{
if (v___y_1775_ == 0)
{
lean_object* v___x_1776_; 
lean_inc(v_binderName_1752_);
lean_del_object(v___x_1772_);
lean_del_object(v___x_1767_);
lean_dec_ref(v_e_1742_);
v___x_1776_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_1752_, v_binderInfo_1755_, v_fst_1759_, v_fst_1769_, v_snd_1770_, v_a_1745_, v_snd_1765_);
return v___x_1776_;
}
else
{
lean_object* v___x_1778_; 
lean_dec(v_fst_1769_);
lean_dec(v_fst_1759_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v_e_1742_);
v___x_1778_ = v___x_1772_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_e_1742_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_snd_1770_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1778_);
v___x_1780_ = v___x_1767_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_snd_1765_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1787_; lean_object* v_binderType_1788_; lean_object* v_body_1789_; uint8_t v_binderInfo_1790_; lean_object* v___x_1791_; lean_object* v_fst_1792_; lean_object* v_snd_1793_; lean_object* v_fst_1794_; lean_object* v_snd_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1821_; 
v_binderName_1787_ = lean_ctor_get(v_e_1742_, 0);
v_binderType_1788_ = lean_ctor_get(v_e_1742_, 1);
v_body_1789_ = lean_ctor_get(v_e_1742_, 2);
v_binderInfo_1790_ = lean_ctor_get_uint8(v_e_1742_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1743_);
lean_inc_ref(v_binderType_1788_);
v___x_1791_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_binderType_1788_, v_offset_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
v_fst_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_fst_1792_);
v_snd_1793_ = lean_ctor_get(v___x_1791_, 1);
lean_inc(v_snd_1793_);
lean_dec_ref(v___x_1791_);
v_fst_1794_ = lean_ctor_get(v_fst_1792_, 0);
lean_inc(v_fst_1794_);
v_snd_1795_ = lean_ctor_get(v_fst_1792_, 1);
lean_inc(v_snd_1795_);
lean_dec(v_fst_1792_);
v___x_1796_ = lean_unsigned_to_nat(1u);
v___x_1797_ = lean_nat_add(v_offset_1743_, v___x_1796_);
lean_dec(v_offset_1743_);
lean_inc_ref(v_body_1789_);
v___x_1798_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_body_1789_, v___x_1797_, v_snd_1795_, v_a_1745_, v_snd_1793_);
v_fst_1799_ = lean_ctor_get(v___x_1798_, 0);
v_snd_1800_ = lean_ctor_get(v___x_1798_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1802_ = v___x_1798_;
v_isShared_1803_ = v_isSharedCheck_1821_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_snd_1800_);
lean_inc(v_fst_1799_);
lean_dec(v___x_1798_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1821_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_fst_1804_; lean_object* v_snd_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1820_; 
v_fst_1804_ = lean_ctor_get(v_fst_1799_, 0);
v_snd_1805_ = lean_ctor_get(v_fst_1799_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_fst_1799_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1807_ = v_fst_1799_;
v_isShared_1808_ = v_isSharedCheck_1820_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_snd_1805_);
lean_inc(v_fst_1804_);
lean_dec(v_fst_1799_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1820_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
uint8_t v___y_1810_; uint8_t v___x_1818_; 
v___x_1818_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1788_, v_fst_1794_);
if (v___x_1818_ == 0)
{
v___y_1810_ = v___x_1818_;
goto v___jp_1809_;
}
else
{
uint8_t v___x_1819_; 
v___x_1819_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1789_, v_fst_1804_);
v___y_1810_ = v___x_1819_;
goto v___jp_1809_;
}
v___jp_1809_:
{
if (v___y_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_inc(v_binderName_1787_);
lean_del_object(v___x_1807_);
lean_del_object(v___x_1802_);
lean_dec_ref(v_e_1742_);
v___x_1811_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_1787_, v_binderInfo_1790_, v_fst_1794_, v_fst_1804_, v_snd_1805_, v_a_1745_, v_snd_1800_);
return v___x_1811_;
}
else
{
lean_object* v___x_1813_; 
lean_dec(v_fst_1804_);
lean_dec(v_fst_1794_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v_e_1742_);
v___x_1813_ = v___x_1807_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_e_1742_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_snd_1805_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1813_);
v___x_1815_ = v___x_1802_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_snd_1800_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1822_; lean_object* v_type_1823_; lean_object* v_value_1824_; lean_object* v_body_1825_; uint8_t v_nondep_1826_; lean_object* v___x_1827_; lean_object* v_fst_1828_; lean_object* v_snd_1829_; lean_object* v_fst_1830_; lean_object* v_snd_1831_; lean_object* v___x_1832_; lean_object* v_fst_1833_; lean_object* v_snd_1834_; lean_object* v_fst_1835_; lean_object* v_snd_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1864_; 
v_declName_1822_ = lean_ctor_get(v_e_1742_, 0);
v_type_1823_ = lean_ctor_get(v_e_1742_, 1);
v_value_1824_ = lean_ctor_get(v_e_1742_, 2);
v_body_1825_ = lean_ctor_get(v_e_1742_, 3);
v_nondep_1826_ = lean_ctor_get_uint8(v_e_1742_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1743_);
lean_inc_ref(v_type_1823_);
v___x_1827_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_type_1823_, v_offset_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
v_fst_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_fst_1828_);
v_snd_1829_ = lean_ctor_get(v___x_1827_, 1);
lean_inc(v_snd_1829_);
lean_dec_ref(v___x_1827_);
v_fst_1830_ = lean_ctor_get(v_fst_1828_, 0);
lean_inc(v_fst_1830_);
v_snd_1831_ = lean_ctor_get(v_fst_1828_, 1);
lean_inc(v_snd_1831_);
lean_dec(v_fst_1828_);
lean_inc(v_offset_1743_);
lean_inc_ref(v_value_1824_);
v___x_1832_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_value_1824_, v_offset_1743_, v_snd_1831_, v_a_1745_, v_snd_1829_);
v_fst_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_fst_1833_);
v_snd_1834_ = lean_ctor_get(v___x_1832_, 1);
lean_inc(v_snd_1834_);
lean_dec_ref(v___x_1832_);
v_fst_1835_ = lean_ctor_get(v_fst_1833_, 0);
lean_inc(v_fst_1835_);
v_snd_1836_ = lean_ctor_get(v_fst_1833_, 1);
lean_inc(v_snd_1836_);
lean_dec(v_fst_1833_);
v___x_1837_ = lean_unsigned_to_nat(1u);
v___x_1838_ = lean_nat_add(v_offset_1743_, v___x_1837_);
lean_dec(v_offset_1743_);
lean_inc_ref(v_body_1825_);
v___x_1839_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_body_1825_, v___x_1838_, v_snd_1836_, v_a_1745_, v_snd_1834_);
v_fst_1840_ = lean_ctor_get(v___x_1839_, 0);
v_snd_1841_ = lean_ctor_get(v___x_1839_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1843_ = v___x_1839_;
v_isShared_1844_ = v_isSharedCheck_1864_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_snd_1841_);
lean_inc(v_fst_1840_);
lean_dec(v___x_1839_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1864_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_fst_1845_; lean_object* v_snd_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1863_; 
v_fst_1845_ = lean_ctor_get(v_fst_1840_, 0);
v_snd_1846_ = lean_ctor_get(v_fst_1840_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_fst_1840_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1848_ = v_fst_1840_;
v_isShared_1849_ = v_isSharedCheck_1863_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_snd_1846_);
lean_inc(v_fst_1845_);
lean_dec(v_fst_1840_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1863_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint8_t v___y_1851_; uint8_t v___x_1861_; 
v___x_1861_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1823_, v_fst_1830_);
if (v___x_1861_ == 0)
{
v___y_1851_ = v___x_1861_;
goto v___jp_1850_;
}
else
{
uint8_t v___x_1862_; 
v___x_1862_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1824_, v_fst_1835_);
v___y_1851_ = v___x_1862_;
goto v___jp_1850_;
}
v___jp_1850_:
{
if (v___y_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_inc(v_declName_1822_);
lean_del_object(v___x_1848_);
lean_del_object(v___x_1843_);
lean_dec_ref(v_e_1742_);
v___x_1852_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1822_, v_fst_1830_, v_fst_1835_, v_fst_1845_, v_nondep_1826_, v_snd_1846_, v_a_1745_, v_snd_1841_);
return v___x_1852_;
}
else
{
uint8_t v___x_1853_; 
v___x_1853_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1825_, v_fst_1845_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_inc(v_declName_1822_);
lean_del_object(v___x_1848_);
lean_del_object(v___x_1843_);
lean_dec_ref(v_e_1742_);
v___x_1854_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_1822_, v_fst_1830_, v_fst_1835_, v_fst_1845_, v_nondep_1826_, v_snd_1846_, v_a_1745_, v_snd_1841_);
return v___x_1854_;
}
else
{
lean_object* v___x_1856_; 
lean_dec(v_fst_1845_);
lean_dec(v_fst_1835_);
lean_dec(v_fst_1830_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v_e_1742_);
v___x_1856_ = v___x_1848_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_e_1742_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_snd_1846_);
v___x_1856_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1858_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1856_);
v___x_1858_ = v___x_1843_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_snd_1841_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
}
}
case 10:
{
lean_object* v_data_1865_; lean_object* v_expr_1866_; lean_object* v___x_1867_; lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1887_; 
v_data_1865_ = lean_ctor_get(v_e_1742_, 0);
v_expr_1866_ = lean_ctor_get(v_e_1742_, 1);
lean_inc_ref(v_expr_1866_);
v___x_1867_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_expr_1866_, v_offset_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
v_fst_1868_ = lean_ctor_get(v___x_1867_, 0);
v_snd_1869_ = lean_ctor_get(v___x_1867_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1871_ = v___x_1867_;
v_isShared_1872_ = v_isSharedCheck_1887_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_snd_1869_);
lean_inc(v_fst_1868_);
lean_dec(v___x_1867_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1887_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v_fst_1873_; lean_object* v_snd_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1886_; 
v_fst_1873_ = lean_ctor_get(v_fst_1868_, 0);
v_snd_1874_ = lean_ctor_get(v_fst_1868_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_fst_1868_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1876_ = v_fst_1868_;
v_isShared_1877_ = v_isSharedCheck_1886_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_snd_1874_);
lean_inc(v_fst_1873_);
lean_dec(v_fst_1868_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1886_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
uint8_t v___x_1878_; 
v___x_1878_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1866_, v_fst_1873_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_inc(v_data_1865_);
lean_del_object(v___x_1876_);
lean_del_object(v___x_1871_);
lean_dec_ref(v_e_1742_);
v___x_1879_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_1865_, v_fst_1873_, v_snd_1874_, v_a_1745_, v_snd_1869_);
return v___x_1879_;
}
else
{
lean_object* v___x_1881_; 
lean_dec(v_fst_1873_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v_e_1742_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_e_1742_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_snd_1874_);
v___x_1881_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1881_);
v___x_1883_ = v___x_1871_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_snd_1869_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1888_; lean_object* v_idx_1889_; lean_object* v_struct_1890_; lean_object* v___x_1891_; lean_object* v_fst_1892_; lean_object* v_snd_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1911_; 
v_typeName_1888_ = lean_ctor_get(v_e_1742_, 0);
v_idx_1889_ = lean_ctor_get(v_e_1742_, 1);
v_struct_1890_ = lean_ctor_get(v_e_1742_, 2);
lean_inc_ref(v_struct_1890_);
v___x_1891_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1741_, v_struct_1890_, v_offset_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
v_fst_1892_ = lean_ctor_get(v___x_1891_, 0);
v_snd_1893_ = lean_ctor_get(v___x_1891_, 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1895_ = v___x_1891_;
v_isShared_1896_ = v_isSharedCheck_1911_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_snd_1893_);
lean_inc(v_fst_1892_);
lean_dec(v___x_1891_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1911_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v_fst_1897_; lean_object* v_snd_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1910_; 
v_fst_1897_ = lean_ctor_get(v_fst_1892_, 0);
v_snd_1898_ = lean_ctor_get(v_fst_1892_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_fst_1892_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1900_ = v_fst_1892_;
v_isShared_1901_ = v_isSharedCheck_1910_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_snd_1898_);
lean_inc(v_fst_1897_);
lean_dec(v_fst_1892_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1910_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
uint8_t v___x_1902_; 
v___x_1902_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1890_, v_fst_1897_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_inc(v_idx_1889_);
lean_inc(v_typeName_1888_);
lean_del_object(v___x_1900_);
lean_del_object(v___x_1895_);
lean_dec_ref(v_e_1742_);
v___x_1903_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_1888_, v_idx_1889_, v_fst_1897_, v_snd_1898_, v_a_1745_, v_snd_1893_);
return v___x_1903_;
}
else
{
lean_object* v___x_1905_; 
lean_dec(v_fst_1897_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v_e_1742_);
v___x_1905_ = v___x_1900_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_e_1742_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_snd_1898_);
v___x_1905_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1907_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1905_);
v___x_1907_ = v___x_1895_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_snd_1893_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec(v_offset_1743_);
lean_dec_ref(v_e_1742_);
v___x_1912_ = lean_obj_once(&l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1, &l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once, _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
v___x_1913_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_1912_, v_a_1744_, v_a_1745_, v_a_1746_);
return v___x_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(lean_object* v_subst_1914_, lean_object* v_e_1915_, lean_object* v_offset_1916_, lean_object* v_a_1917_, uint8_t v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = l_Lean_Expr_looseBVarRange(v_e_1915_);
v___x_1921_ = lean_nat_dec_le(v___x_1920_, v_offset_1916_);
lean_dec(v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v_key_1922_; lean_object* v___x_1923_; 
lean_inc(v_offset_1916_);
lean_inc_ref(v_e_1915_);
v_key_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1922_, 0, v_e_1915_);
lean_ctor_set(v_key_1922_, 1, v_offset_1916_);
v___x_1923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1917_, v_key_1922_);
if (lean_obj_tag(v___x_1923_) == 1)
{
lean_object* v_val_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v_key_1922_);
lean_dec(v_offset_1916_);
lean_dec_ref(v_e_1915_);
v_val_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_val_1924_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_val_1924_);
lean_ctor_set(v___x_1925_, 1, v_a_1917_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v_a_1919_);
return v___x_1926_;
}
else
{
lean_dec(v___x_1923_);
switch(lean_obj_tag(v_e_1915_))
{
case 0:
{
lean_object* v_deBruijnIndex_1927_; lean_object* v___x_1928_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v_fst_1931_; lean_object* v_snd_1932_; lean_object* v___x_1933_; 
v_deBruijnIndex_1927_ = lean_ctor_get(v_e_1915_, 0);
lean_inc(v_deBruijnIndex_1927_);
v___x_1928_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_1914_, v_e_1915_, v_deBruijnIndex_1927_, v_offset_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
lean_dec(v_offset_1916_);
lean_dec(v_deBruijnIndex_1927_);
v_fst_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_fst_1929_);
v_snd_1930_ = lean_ctor_get(v___x_1928_, 1);
lean_inc(v_snd_1930_);
lean_dec_ref(v___x_1928_);
v_fst_1931_ = lean_ctor_get(v_fst_1929_, 0);
lean_inc(v_fst_1931_);
v_snd_1932_ = lean_ctor_get(v_fst_1929_, 1);
lean_inc(v_snd_1932_);
lean_dec(v_fst_1929_);
v___x_1933_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1922_, v_fst_1931_, v_snd_1932_, v_snd_1930_);
return v___x_1933_;
}
case 9:
{
lean_object* v___x_1934_; 
lean_dec(v_offset_1916_);
v___x_1934_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1922_, v_e_1915_, v_a_1917_, v_a_1919_);
return v___x_1934_;
}
case 2:
{
lean_object* v___x_1935_; 
lean_dec(v_offset_1916_);
v___x_1935_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1922_, v_e_1915_, v_a_1917_, v_a_1919_);
return v___x_1935_;
}
case 1:
{
lean_object* v___x_1936_; 
lean_dec(v_offset_1916_);
v___x_1936_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1922_, v_e_1915_, v_a_1917_, v_a_1919_);
return v___x_1936_;
}
case 4:
{
lean_object* v___x_1937_; 
lean_dec(v_offset_1916_);
v___x_1937_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1922_, v_e_1915_, v_a_1917_, v_a_1919_);
return v___x_1937_;
}
case 3:
{
lean_object* v___x_1938_; 
lean_dec(v_offset_1916_);
v___x_1938_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1922_, v_e_1915_, v_a_1917_, v_a_1919_);
return v___x_1938_;
}
default: 
{
lean_object* v___x_1939_; lean_object* v_fst_1940_; lean_object* v_snd_1941_; lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1944_; 
v___x_1939_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_1914_, v_e_1915_, v_offset_1916_, v_a_1917_, v_a_1918_, v_a_1919_);
v_fst_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_fst_1940_);
v_snd_1941_ = lean_ctor_get(v___x_1939_, 1);
lean_inc(v_snd_1941_);
lean_dec_ref(v___x_1939_);
v_fst_1942_ = lean_ctor_get(v_fst_1940_, 0);
lean_inc(v_fst_1942_);
v_snd_1943_ = lean_ctor_get(v_fst_1940_, 1);
lean_inc(v_snd_1943_);
lean_dec(v_fst_1940_);
v___x_1944_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1922_, v_fst_1942_, v_snd_1943_, v_snd_1941_);
return v___x_1944_;
}
}
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
lean_dec(v_offset_1916_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_e_1915_);
lean_ctor_set(v___x_1945_, 1, v_a_1917_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v_a_1919_);
return v___x_1946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(lean_object* v_subst_1947_, lean_object* v_e_1948_, lean_object* v_offset_1949_, lean_object* v_a_1950_, uint8_t v_a_1951_, lean_object* v_a_1952_){
_start:
{
if (lean_obj_tag(v_e_1948_) == 5)
{
lean_object* v_fn_1953_; lean_object* v_arg_1954_; lean_object* v_key_1955_; lean_object* v___x_1956_; 
v_fn_1953_ = lean_ctor_get(v_e_1948_, 0);
v_arg_1954_ = lean_ctor_get(v_e_1948_, 1);
lean_inc(v_offset_1949_);
lean_inc_ref(v_e_1948_);
v_key_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1955_, 0, v_e_1948_);
lean_ctor_set(v_key_1955_, 1, v_offset_1949_);
v___x_1956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_1950_, v_key_1955_);
if (lean_obj_tag(v___x_1956_) == 1)
{
lean_object* v_val_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec_ref(v_key_1955_);
lean_dec_ref(v_e_1948_);
lean_dec(v_offset_1949_);
v_val_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_val_1957_);
lean_dec_ref(v___x_1956_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_val_1957_);
lean_ctor_set(v___x_1958_, 1, v_a_1950_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set(v___x_1959_, 1, v_a_1952_);
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v_fst_1961_; lean_object* v_snd_1962_; lean_object* v_fst_1963_; lean_object* v_snd_1964_; lean_object* v___x_1965_; lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v_fst_1968_; lean_object* v_snd_1969_; uint8_t v___y_1971_; uint8_t v___x_1979_; 
lean_dec(v___x_1956_);
lean_inc(v_offset_1949_);
lean_inc_ref(v_fn_1953_);
v___x_1960_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1947_, v_fn_1953_, v_offset_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
v_fst_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_fst_1961_);
v_snd_1962_ = lean_ctor_get(v___x_1960_, 1);
lean_inc(v_snd_1962_);
lean_dec_ref(v___x_1960_);
v_fst_1963_ = lean_ctor_get(v_fst_1961_, 0);
lean_inc(v_fst_1963_);
v_snd_1964_ = lean_ctor_get(v_fst_1961_, 1);
lean_inc(v_snd_1964_);
lean_dec(v_fst_1961_);
lean_inc_ref(v_arg_1954_);
v___x_1965_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1947_, v_arg_1954_, v_offset_1949_, v_snd_1964_, v_a_1951_, v_snd_1962_);
v_fst_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_fst_1966_);
v_snd_1967_ = lean_ctor_get(v___x_1965_, 1);
lean_inc(v_snd_1967_);
lean_dec_ref(v___x_1965_);
v_fst_1968_ = lean_ctor_get(v_fst_1966_, 0);
lean_inc(v_fst_1968_);
v_snd_1969_ = lean_ctor_get(v_fst_1966_, 1);
lean_inc(v_snd_1969_);
lean_dec(v_fst_1966_);
v___x_1979_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1953_, v_fst_1963_);
if (v___x_1979_ == 0)
{
v___y_1971_ = v___x_1979_;
goto v___jp_1970_;
}
else
{
uint8_t v___x_1980_; 
v___x_1980_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1954_, v_fst_1968_);
v___y_1971_ = v___x_1980_;
goto v___jp_1970_;
}
v___jp_1970_:
{
if (v___y_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v_fst_1973_; lean_object* v_snd_1974_; lean_object* v_fst_1975_; lean_object* v_snd_1976_; lean_object* v___x_1977_; 
lean_dec_ref(v_e_1948_);
v___x_1972_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_1963_, v_fst_1968_, v_snd_1969_, v_a_1951_, v_snd_1967_);
v_fst_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_fst_1973_);
v_snd_1974_ = lean_ctor_get(v___x_1972_, 1);
lean_inc(v_snd_1974_);
lean_dec_ref(v___x_1972_);
v_fst_1975_ = lean_ctor_get(v_fst_1973_, 0);
lean_inc(v_fst_1975_);
v_snd_1976_ = lean_ctor_get(v_fst_1973_, 1);
lean_inc(v_snd_1976_);
lean_dec(v_fst_1973_);
v___x_1977_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1955_, v_fst_1975_, v_snd_1976_, v_snd_1974_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; 
lean_dec(v_fst_1968_);
lean_dec(v_fst_1963_);
v___x_1978_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(v_key_1955_, v_e_1948_, v_snd_1969_, v_snd_1967_);
return v___x_1978_;
}
}
}
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1947_, v_e_1948_, v_offset_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(lean_object* v_subst_1982_, lean_object* v_e_1983_, lean_object* v_offset_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
uint8_t v_a_boxed_1988_; lean_object* v_res_1989_; 
v_a_boxed_1988_ = lean_unbox(v_a_1986_);
v_res_1989_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_1982_, v_e_1983_, v_offset_1984_, v_a_1985_, v_a_boxed_1988_, v_a_1987_);
lean_dec_ref(v_subst_1982_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(lean_object* v_subst_1990_, lean_object* v_e_1991_, lean_object* v_offset_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
uint8_t v_a_boxed_1996_; lean_object* v_res_1997_; 
v_a_boxed_1996_ = lean_unbox(v_a_1994_);
v_res_1997_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_1990_, v_e_1991_, v_offset_1992_, v_a_1993_, v_a_boxed_1996_, v_a_1995_);
lean_dec_ref(v_subst_1990_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(lean_object* v_subst_1998_, lean_object* v_e_1999_, lean_object* v_f_2000_, lean_object* v_arg_2001_, lean_object* v_offset_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
uint8_t v_a_boxed_2006_; lean_object* v_res_2007_; 
v_a_boxed_2006_ = lean_unbox(v_a_2004_);
v_res_2007_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_1998_, v_e_1999_, v_f_2000_, v_arg_2001_, v_offset_2002_, v_a_2003_, v_a_boxed_2006_, v_a_2005_);
lean_dec_ref(v_subst_1998_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(lean_object* v_subst_2008_, lean_object* v_e_2009_, lean_object* v_f_2010_, lean_object* v_argsRev_2011_, lean_object* v_offset_2012_, lean_object* v_modified_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
uint8_t v_modified_boxed_2017_; uint8_t v_a_boxed_2018_; lean_object* v_res_2019_; 
v_modified_boxed_2017_ = lean_unbox(v_modified_2013_);
v_a_boxed_2018_ = lean_unbox(v_a_2015_);
v_res_2019_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_2008_, v_e_2009_, v_f_2010_, v_argsRev_2011_, v_offset_2012_, v_modified_boxed_2017_, v_a_2014_, v_a_boxed_2018_, v_a_2016_);
lean_dec_ref(v_subst_2008_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(lean_object* v_subst_2020_, lean_object* v_e_2021_, lean_object* v_offset_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
uint8_t v_a_boxed_2026_; lean_object* v_res_2027_; 
v_a_boxed_2026_ = lean_unbox(v_a_2024_);
v_res_2027_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2020_, v_e_2021_, v_offset_2022_, v_a_2023_, v_a_boxed_2026_, v_a_2025_);
lean_dec_ref(v_subst_2020_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(lean_object* v_subst_2028_, lean_object* v_e_2029_, lean_object* v_f_2030_, lean_object* v_arg_2031_, lean_object* v_offset_2032_, lean_object* v_x_2033_, lean_object* v_a_2034_, uint8_t v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_2028_, v_e_2029_, v_f_2030_, v_arg_2031_, v_offset_2032_, v_a_2034_, v_a_2035_, v_a_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(lean_object* v_subst_2038_, lean_object* v_e_2039_, lean_object* v_f_2040_, lean_object* v_arg_2041_, lean_object* v_offset_2042_, lean_object* v_x_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
uint8_t v_a_boxed_2047_; lean_object* v_res_2048_; 
v_a_boxed_2047_ = lean_unbox(v_a_2045_);
v_res_2048_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(v_subst_2038_, v_e_2039_, v_f_2040_, v_arg_2041_, v_offset_2042_, v_x_2043_, v_a_2044_, v_a_boxed_2047_, v_a_2046_);
lean_dec_ref(v_subst_2038_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(lean_object* v_e_2049_, lean_object* v_subst_2050_, uint8_t v_a_2051_, lean_object* v_a_2052_){
_start:
{
uint8_t v___y_2054_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = lean_array_get_size(v_subst_2050_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_nat_dec_eq(v___x_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
uint8_t v___x_2073_; 
v___x_2073_ = l_Lean_Expr_hasLooseBVars(v_e_2049_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_e_2049_);
lean_ctor_set(v___x_2074_, 1, v_a_2052_);
return v___x_2074_;
}
else
{
v___y_2054_ = v___x_2072_;
goto v___jp_2053_;
}
}
else
{
v___y_2054_ = v___x_2072_;
goto v___jp_2053_;
}
v___jp_2053_:
{
if (v___y_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_fst_2058_; lean_object* v_snd_2059_; lean_object* v_fst_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__2, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
v___x_2057_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_2050_, v_e_2049_, v___x_2055_, v___x_2056_, v_a_2051_, v_a_2052_);
v_fst_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_fst_2058_);
v_snd_2059_ = lean_ctor_get(v___x_2057_, 1);
lean_inc(v_snd_2059_);
lean_dec_ref(v___x_2057_);
v_fst_2060_ = lean_ctor_get(v_fst_2058_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_fst_2058_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; 
v_unused_2068_ = lean_ctor_get(v_fst_2058_, 1);
lean_dec(v_unused_2068_);
v___x_2062_ = v_fst_2058_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_fst_2060_);
lean_dec(v_fst_2058_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v_snd_2059_);
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_fst_2060_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_snd_2059_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_e_2049_);
lean_ctor_set(v___x_2069_, 1, v_a_2052_);
return v___x_2069_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(lean_object* v_e_2075_, lean_object* v_subst_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
uint8_t v_a_boxed_2079_; lean_object* v_res_2080_; 
v_a_boxed_2079_ = lean_unbox(v_a_2077_);
v_res_2080_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2075_, v_subst_2076_, v_a_boxed_2079_, v_a_2078_);
lean_dec_ref(v_subst_2076_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object* v_e_2081_, lean_object* v_subst_2082_, lean_object* v_a_2083_){
_start:
{
uint8_t v___x_2085_; 
v___x_2085_ = l_Lean_Expr_hasLooseBVars(v_e_2081_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_e_2081_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = lean_array_get_size(v_subst_2082_);
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = lean_nat_dec_eq(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v_share_2091_; lean_object* v_maxFVar_2092_; lean_object* v_proofInstInfo_2093_; lean_object* v_inferType_2094_; lean_object* v_getLevel_2095_; lean_object* v_congrInfo_2096_; lean_object* v_defEqI_2097_; lean_object* v_extensions_2098_; lean_object* v_issues_2099_; uint8_t v_debug_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2134_; 
v___x_2090_ = lean_st_ref_take(v_a_2083_);
v_share_2091_ = lean_ctor_get(v___x_2090_, 0);
v_maxFVar_2092_ = lean_ctor_get(v___x_2090_, 1);
v_proofInstInfo_2093_ = lean_ctor_get(v___x_2090_, 2);
v_inferType_2094_ = lean_ctor_get(v___x_2090_, 3);
v_getLevel_2095_ = lean_ctor_get(v___x_2090_, 4);
v_congrInfo_2096_ = lean_ctor_get(v___x_2090_, 5);
v_defEqI_2097_ = lean_ctor_get(v___x_2090_, 6);
v_extensions_2098_ = lean_ctor_get(v___x_2090_, 7);
v_issues_2099_ = lean_ctor_get(v___x_2090_, 8);
v_debug_2100_ = lean_ctor_get_uint8(v___x_2090_, sizeof(void*)*9);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2102_ = v___x_2090_;
v_isShared_2103_ = v_isSharedCheck_2134_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_issues_2099_);
lean_inc(v_extensions_2098_);
lean_inc(v_defEqI_2097_);
lean_inc(v_congrInfo_2096_);
lean_inc(v_getLevel_2095_);
lean_inc(v_inferType_2094_);
lean_inc(v_proofInstInfo_2093_);
lean_inc(v_maxFVar_2092_);
lean_inc(v_share_2091_);
lean_dec(v___x_2090_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2134_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_obj_once(&l_Lean_Meta_Sym_instantiateRevRangeS___closed__0, &l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once, _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_maxFVar_2092_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_proofInstInfo_2093_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_inferType_2094_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v_getLevel_2095_);
lean_ctor_set(v_reuseFailAlloc_2133_, 5, v_congrInfo_2096_);
lean_ctor_set(v_reuseFailAlloc_2133_, 6, v_defEqI_2097_);
lean_ctor_set(v_reuseFailAlloc_2133_, 7, v_extensions_2098_);
lean_ctor_set(v_reuseFailAlloc_2133_, 8, v_issues_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2133_, sizeof(void*)*9, v_debug_2100_);
v___x_2106_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v_debug_2109_; lean_object* v___x_2110_; lean_object* v_fst_2111_; lean_object* v_snd_2112_; lean_object* v___x_2113_; lean_object* v_maxFVar_2114_; lean_object* v_proofInstInfo_2115_; lean_object* v_inferType_2116_; lean_object* v_getLevel_2117_; lean_object* v_congrInfo_2118_; lean_object* v_defEqI_2119_; lean_object* v_extensions_2120_; lean_object* v_issues_2121_; uint8_t v_debug_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2131_; 
v___x_2107_ = lean_st_ref_set(v_a_2083_, v___x_2106_);
v___x_2108_ = lean_st_ref_get(v_a_2083_);
v_debug_2109_ = lean_ctor_get_uint8(v___x_2108_, sizeof(void*)*9);
lean_dec(v___x_2108_);
v___x_2110_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(v_e_2081_, v_subst_2082_, v_debug_2109_, v_share_2091_);
v_fst_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_fst_2111_);
v_snd_2112_ = lean_ctor_get(v___x_2110_, 1);
lean_inc(v_snd_2112_);
lean_dec_ref(v___x_2110_);
v___x_2113_ = lean_st_ref_take(v_a_2083_);
v_maxFVar_2114_ = lean_ctor_get(v___x_2113_, 1);
v_proofInstInfo_2115_ = lean_ctor_get(v___x_2113_, 2);
v_inferType_2116_ = lean_ctor_get(v___x_2113_, 3);
v_getLevel_2117_ = lean_ctor_get(v___x_2113_, 4);
v_congrInfo_2118_ = lean_ctor_get(v___x_2113_, 5);
v_defEqI_2119_ = lean_ctor_get(v___x_2113_, 6);
v_extensions_2120_ = lean_ctor_get(v___x_2113_, 7);
v_issues_2121_ = lean_ctor_get(v___x_2113_, 8);
v_debug_2122_ = lean_ctor_get_uint8(v___x_2113_, sizeof(void*)*9);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2113_, 0);
lean_dec(v_unused_2132_);
v___x_2124_ = v___x_2113_;
v_isShared_2125_ = v_isSharedCheck_2131_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_issues_2121_);
lean_inc(v_extensions_2120_);
lean_inc(v_defEqI_2119_);
lean_inc(v_congrInfo_2118_);
lean_inc(v_getLevel_2117_);
lean_inc(v_inferType_2116_);
lean_inc(v_proofInstInfo_2115_);
lean_inc(v_maxFVar_2114_);
lean_dec(v___x_2113_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2131_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_snd_2112_);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_snd_2112_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_maxFVar_2114_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_proofInstInfo_2115_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v_inferType_2116_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v_getLevel_2117_);
lean_ctor_set(v_reuseFailAlloc_2130_, 5, v_congrInfo_2118_);
lean_ctor_set(v_reuseFailAlloc_2130_, 6, v_defEqI_2119_);
lean_ctor_set(v_reuseFailAlloc_2130_, 7, v_extensions_2120_);
lean_ctor_set(v_reuseFailAlloc_2130_, 8, v_issues_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2130_, sizeof(void*)*9, v_debug_2122_);
v___x_2127_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = lean_st_ref_set(v_a_2083_, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_fst_2111_);
return v___x_2129_;
}
}
}
}
}
else
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_e_2081_);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(lean_object* v_e_2136_, lean_object* v_subst_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2136_, v_subst_2137_, v_a_2138_);
lean_dec(v_a_2138_);
lean_dec_ref(v_subst_2137_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object* v_e_2141_, lean_object* v_subst_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_2141_, v_subst_2142_, v_a_2144_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___boxed(lean_object* v_e_2151_, lean_object* v_subst_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_e_2151_, v_subst_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec_ref(v_subst_2152_);
return v_res_2160_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_InstantiateS(builtin);
}
#ifdef __cplusplus
}
#endif
