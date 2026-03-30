// Lean compiler output
// Module: Lean.Meta.Sym.LooseBVarsS
// Imports: public import Lean.Meta.Sym.ReplaceS
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(lean_object* v_idx_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = l_Lean_Expr_bvar___override(v_idx_1_);
v___x_4_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3_, v___y_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(lean_object* v_idx_5_, uint8_t v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v_idx_5_, v___y_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___boxed(lean_object* v_idx_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
uint8_t v___y_21034__boxed_12_; lean_object* v_res_13_; 
v___y_21034__boxed_12_ = lean_unbox(v___y_10_);
v_res_13_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0(v_idx_9_, v___y_21034__boxed_12_, v___y_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(lean_object* v_x_14_, uint8_t v_bi_15_, lean_object* v_t_16_, lean_object* v_b_17_, lean_object* v___y_18_, uint8_t v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___y_22_; lean_object* v___y_23_; 
if (v___y_19_ == 0)
{
v___y_22_ = v___y_18_;
v___y_23_ = v___y_20_;
goto v___jp_21_;
}
else
{
lean_object* v___x_36_; lean_object* v_snd_37_; lean_object* v___x_38_; lean_object* v_snd_39_; 
lean_inc_ref(v_t_16_);
v___x_36_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_16_, v___y_19_, v___y_20_);
v_snd_37_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_snd_37_);
lean_dec_ref(v___x_36_);
lean_inc_ref(v_b_17_);
v___x_38_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_17_, v___y_19_, v_snd_37_);
v_snd_39_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_snd_39_);
lean_dec_ref(v___x_38_);
v___y_22_ = v___y_18_;
v___y_23_ = v_snd_39_;
goto v___jp_21_;
}
v___jp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_fst_26_; lean_object* v_snd_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_35_; 
v___x_24_ = l_Lean_Expr_forallE___override(v_x_14_, v_t_16_, v_b_17_, v_bi_15_);
v___x_25_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_24_, v___y_23_);
v_fst_26_ = lean_ctor_get(v___x_25_, 0);
v_snd_27_ = lean_ctor_get(v___x_25_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_35_ == 0)
{
v___x_29_ = v___x_25_;
v_isShared_30_ = v_isSharedCheck_35_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_snd_27_);
lean_inc(v_fst_26_);
lean_dec(v___x_25_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_35_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v___y_22_);
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_fst_26_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___y_22_);
v___x_32_ = v_reuseFailAlloc_34_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_snd_27_);
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4___boxed(lean_object* v_x_40_, lean_object* v_bi_41_, lean_object* v_t_42_, lean_object* v_b_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
uint8_t v_bi_boxed_47_; uint8_t v___y_21043__boxed_48_; lean_object* v_res_49_; 
v_bi_boxed_47_ = lean_unbox(v_bi_41_);
v___y_21043__boxed_48_ = lean_unbox(v___y_45_);
v_res_49_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_x_40_, v_bi_boxed_47_, v_t_42_, v_b_43_, v___y_44_, v___y_21043__boxed_48_, v___y_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(lean_object* v_structName_50_, lean_object* v_idx_51_, lean_object* v_struct_52_, lean_object* v___y_53_, uint8_t v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___y_57_; lean_object* v___y_58_; 
if (v___y_54_ == 0)
{
v___y_57_ = v___y_53_;
v___y_58_ = v___y_55_;
goto v___jp_56_;
}
else
{
lean_object* v___x_71_; lean_object* v_snd_72_; 
lean_inc_ref(v_struct_52_);
v___x_71_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_52_, v___y_54_, v___y_55_);
v_snd_72_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_snd_72_);
lean_dec_ref(v___x_71_);
v___y_57_ = v___y_53_;
v___y_58_ = v_snd_72_;
goto v___jp_56_;
}
v___jp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_fst_61_; lean_object* v_snd_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_70_; 
v___x_59_ = l_Lean_Expr_proj___override(v_structName_50_, v_idx_51_, v_struct_52_);
v___x_60_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_59_, v___y_58_);
v_fst_61_ = lean_ctor_get(v___x_60_, 0);
v_snd_62_ = lean_ctor_get(v___x_60_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_70_ == 0)
{
v___x_64_ = v___x_60_;
v_isShared_65_ = v_isSharedCheck_70_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_snd_62_);
lean_inc(v_fst_61_);
lean_dec(v___x_60_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_70_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___y_57_);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_fst_61_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___y_57_);
v___x_67_ = v_reuseFailAlloc_69_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_snd_62_);
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7___boxed(lean_object* v_structName_73_, lean_object* v_idx_74_, lean_object* v_struct_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v___y_21092__boxed_79_; lean_object* v_res_80_; 
v___y_21092__boxed_79_ = lean_unbox(v___y_77_);
v_res_80_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_structName_73_, v_idx_74_, v_struct_75_, v___y_76_, v___y_21092__boxed_79_, v___y_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(lean_object* v_x_81_, uint8_t v_bi_82_, lean_object* v_t_83_, lean_object* v_b_84_, lean_object* v___y_85_, uint8_t v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___y_89_; lean_object* v___y_90_; 
if (v___y_86_ == 0)
{
v___y_89_ = v___y_85_;
v___y_90_ = v___y_87_;
goto v___jp_88_;
}
else
{
lean_object* v___x_103_; lean_object* v_snd_104_; lean_object* v___x_105_; lean_object* v_snd_106_; 
lean_inc_ref(v_t_83_);
v___x_103_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_83_, v___y_86_, v___y_87_);
v_snd_104_ = lean_ctor_get(v___x_103_, 1);
lean_inc(v_snd_104_);
lean_dec_ref(v___x_103_);
lean_inc_ref(v_b_84_);
v___x_105_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_84_, v___y_86_, v_snd_104_);
v_snd_106_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_snd_106_);
lean_dec_ref(v___x_105_);
v___y_89_ = v___y_85_;
v___y_90_ = v_snd_106_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_fst_93_; lean_object* v_snd_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_102_; 
v___x_91_ = l_Lean_Expr_lam___override(v_x_81_, v_t_83_, v_b_84_, v_bi_82_);
v___x_92_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_91_, v___y_90_);
v_fst_93_ = lean_ctor_get(v___x_92_, 0);
v_snd_94_ = lean_ctor_get(v___x_92_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_102_ == 0)
{
v___x_96_ = v___x_92_;
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_snd_94_);
lean_inc(v_fst_93_);
lean_dec(v___x_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_102_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___y_89_);
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_fst_93_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___y_89_);
v___x_99_ = v_reuseFailAlloc_101_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_snd_94_);
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3___boxed(lean_object* v_x_107_, lean_object* v_bi_108_, lean_object* v_t_109_, lean_object* v_b_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
uint8_t v_bi_boxed_114_; uint8_t v___y_21136__boxed_115_; lean_object* v_res_116_; 
v_bi_boxed_114_ = lean_unbox(v_bi_108_);
v___y_21136__boxed_115_ = lean_unbox(v___y_112_);
v_res_116_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_x_107_, v_bi_boxed_114_, v_t_109_, v_b_110_, v___y_111_, v___y_21136__boxed_115_, v___y_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(lean_object* v_msg_124_, lean_object* v___y_125_, uint8_t v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_20767__overap_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___f_128_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__0));
v___f_129_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__1));
v___f_130_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__2));
v___f_131_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__3));
v___f_132_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__4));
v___f_133_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__5));
v___f_134_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___closed__6));
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___f_128_);
lean_ctor_set(v___x_135_, 1, v___f_129_);
v___x_136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___f_130_);
lean_ctor_set(v___x_136_, 2, v___f_131_);
lean_ctor_set(v___x_136_, 3, v___f_132_);
lean_ctor_set(v___x_136_, 4, v___f_133_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___f_134_);
lean_inc_ref(v___x_137_);
v___f_138_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_138_, 0, v___x_137_);
lean_inc_ref(v___x_137_);
v___f_139_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_139_, 0, v___x_137_);
lean_inc_ref(v___x_137_);
v___f_140_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_140_, 0, v___x_137_);
lean_inc_ref(v___x_137_);
v___f_141_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_141_, 0, v___x_137_);
lean_inc_ref(v___x_137_);
v___x_142_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_142_, 0, lean_box(0));
lean_closure_set(v___x_142_, 1, lean_box(0));
lean_closure_set(v___x_142_, 2, v___x_137_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___f_138_);
lean_inc_ref(v___x_137_);
v___x_144_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_144_, 0, lean_box(0));
lean_closure_set(v___x_144_, 1, lean_box(0));
lean_closure_set(v___x_144_, 2, v___x_137_);
v___x_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
lean_ctor_set(v___x_145_, 2, v___f_139_);
lean_ctor_set(v___x_145_, 3, v___f_140_);
lean_ctor_set(v___x_145_, 4, v___f_141_);
v___x_146_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_146_, 0, lean_box(0));
lean_closure_set(v___x_146_, 1, lean_box(0));
lean_closure_set(v___x_146_, 2, v___x_137_);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = l_ReaderT_instMonad___redArg(v___x_147_);
lean_inc_ref(v___x_148_);
v___f_149_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_149_, 0, v___x_148_);
lean_inc_ref(v___x_148_);
v___f_150_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_150_, 0, v___x_148_);
lean_inc_ref(v___x_148_);
v___f_151_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_151_, 0, v___x_148_);
lean_inc_ref(v___x_148_);
v___f_152_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_152_, 0, v___x_148_);
lean_inc_ref(v___x_148_);
v___x_153_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_153_, 0, lean_box(0));
lean_closure_set(v___x_153_, 1, lean_box(0));
lean_closure_set(v___x_153_, 2, v___x_148_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___f_149_);
lean_inc_ref(v___x_148_);
v___x_155_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_155_, 0, lean_box(0));
lean_closure_set(v___x_155_, 1, lean_box(0));
lean_closure_set(v___x_155_, 2, v___x_148_);
v___x_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
lean_ctor_set(v___x_156_, 2, v___f_150_);
lean_ctor_set(v___x_156_, 3, v___f_151_);
lean_ctor_set(v___x_156_, 4, v___f_152_);
v___x_157_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_157_, 0, lean_box(0));
lean_closure_set(v___x_157_, 1, lean_box(0));
lean_closure_set(v___x_157_, 2, v___x_148_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = l_Lean_instInhabitedExpr;
v___x_160_ = l_instInhabitedOfMonad___redArg(v___x_158_, v___x_159_);
v___x_20767__overap_161_ = lean_panic_fn_borrowed(v___x_160_, v_msg_124_);
lean_dec(v___x_160_);
v___x_162_ = lean_box(v___y_126_);
v___x_163_ = lean_apply_3(v___x_20767__overap_161_, v___y_125_, v___x_162_, v___y_127_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8___boxed(lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v___y_21199__boxed_168_; lean_object* v_res_169_; 
v___y_21199__boxed_168_ = lean_unbox(v___y_166_);
v_res_169_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v_msg_164_, v___y_165_, v___y_21199__boxed_168_, v___y_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(lean_object* v_f_170_, lean_object* v_a_171_, lean_object* v___y_172_, uint8_t v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___y_176_; lean_object* v___y_177_; 
if (v___y_173_ == 0)
{
v___y_176_ = v___y_172_;
v___y_177_ = v___y_174_;
goto v___jp_175_;
}
else
{
lean_object* v___x_190_; lean_object* v_snd_191_; lean_object* v___x_192_; lean_object* v_snd_193_; 
lean_inc_ref(v_f_170_);
v___x_190_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_170_, v___y_173_, v___y_174_);
v_snd_191_ = lean_ctor_get(v___x_190_, 1);
lean_inc(v_snd_191_);
lean_dec_ref(v___x_190_);
lean_inc_ref(v_a_171_);
v___x_192_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_171_, v___y_173_, v_snd_191_);
v_snd_193_ = lean_ctor_get(v___x_192_, 1);
lean_inc(v_snd_193_);
lean_dec_ref(v___x_192_);
v___y_176_ = v___y_172_;
v___y_177_ = v_snd_193_;
goto v___jp_175_;
}
v___jp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_189_; 
v___x_178_ = l_Lean_Expr_app___override(v_f_170_, v_a_171_);
v___x_179_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_178_, v___y_177_);
v_fst_180_ = lean_ctor_get(v___x_179_, 0);
v_snd_181_ = lean_ctor_get(v___x_179_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_189_ == 0)
{
v___x_183_ = v___x_179_;
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_inc(v_fst_180_);
lean_dec(v___x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_189_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___y_176_);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_fst_180_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___y_176_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; 
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_snd_181_);
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2___boxed(lean_object* v_f_194_, lean_object* v_a_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v___y_21285__boxed_199_; lean_object* v_res_200_; 
v___y_21285__boxed_199_ = lean_unbox(v___y_197_);
v_res_200_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_f_194_, v_a_195_, v___y_196_, v___y_21285__boxed_199_, v___y_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v_key_204_; lean_object* v_value_205_; lean_object* v_tail_206_; uint8_t v___y_208_; lean_object* v_fst_211_; lean_object* v_snd_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; uint8_t v___x_215_; 
v_key_204_ = lean_ctor_get(v_x_202_, 0);
v_value_205_ = lean_ctor_get(v_x_202_, 1);
v_tail_206_ = lean_ctor_get(v_x_202_, 2);
v_fst_211_ = lean_ctor_get(v_key_204_, 0);
v_snd_212_ = lean_ctor_get(v_key_204_, 1);
v_fst_213_ = lean_ctor_get(v_a_201_, 0);
v_snd_214_ = lean_ctor_get(v_a_201_, 1);
v___x_215_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_211_, v_fst_213_);
if (v___x_215_ == 0)
{
v___y_208_ = v___x_215_;
goto v___jp_207_;
}
else
{
uint8_t v___x_216_; 
v___x_216_ = lean_nat_dec_eq(v_snd_212_, v_snd_214_);
v___y_208_ = v___x_216_;
goto v___jp_207_;
}
v___jp_207_:
{
if (v___y_208_ == 0)
{
v_x_202_ = v_tail_206_;
goto _start;
}
else
{
lean_object* v___x_210_; 
lean_inc(v_value_205_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v_value_205_);
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_a_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_217_, v_x_218_);
lean_dec(v_x_218_);
lean_dec_ref(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_m_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_buckets_222_; lean_object* v_fst_223_; lean_object* v_snd_224_; lean_object* v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v_fold_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_buckets_222_ = lean_ctor_get(v_m_220_, 1);
v_fst_223_ = lean_ctor_get(v_a_221_, 0);
v_snd_224_ = lean_ctor_get(v_a_221_, 1);
v___x_225_ = lean_array_get_size(v_buckets_222_);
v___x_226_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_223_);
v___x_227_ = lean_uint64_of_nat(v_snd_224_);
v___x_228_ = lean_uint64_mix_hash(v___x_226_, v___x_227_);
v___x_229_ = 32ULL;
v___x_230_ = lean_uint64_shift_right(v___x_228_, v___x_229_);
v_fold_231_ = lean_uint64_xor(v___x_228_, v___x_230_);
v___x_232_ = 16ULL;
v___x_233_ = lean_uint64_shift_right(v_fold_231_, v___x_232_);
v___x_234_ = lean_uint64_xor(v_fold_231_, v___x_233_);
v___x_235_ = lean_uint64_to_usize(v___x_234_);
v___x_236_ = lean_usize_of_nat(v___x_225_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_sub(v___x_236_, v___x_237_);
v___x_239_ = lean_usize_land(v___x_235_, v___x_238_);
v___x_240_ = lean_array_uget_borrowed(v_buckets_222_, v___x_239_);
v___x_241_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_221_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_m_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_242_, v_a_243_);
lean_dec_ref(v_a_243_);
lean_dec_ref(v_m_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(lean_object* v_x_245_, lean_object* v_t_246_, lean_object* v_v_247_, lean_object* v_b_248_, uint8_t v_nondep_249_, lean_object* v___y_250_, uint8_t v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___y_254_; lean_object* v___y_255_; 
if (v___y_251_ == 0)
{
v___y_254_ = v___y_250_;
v___y_255_ = v___y_252_;
goto v___jp_253_;
}
else
{
lean_object* v___x_268_; lean_object* v_snd_269_; lean_object* v___x_270_; lean_object* v_snd_271_; lean_object* v___x_272_; lean_object* v_snd_273_; 
lean_inc_ref(v_t_246_);
v___x_268_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_246_, v___y_251_, v___y_252_);
v_snd_269_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v___x_268_);
lean_inc_ref(v_v_247_);
v___x_270_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_247_, v___y_251_, v_snd_269_);
v_snd_271_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_snd_271_);
lean_dec_ref(v___x_270_);
lean_inc_ref(v_b_248_);
v___x_272_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_248_, v___y_251_, v_snd_271_);
v_snd_273_ = lean_ctor_get(v___x_272_, 1);
lean_inc(v_snd_273_);
lean_dec_ref(v___x_272_);
v___y_254_ = v___y_250_;
v___y_255_ = v_snd_273_;
goto v___jp_253_;
}
v___jp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v___x_256_ = l_Lean_Expr_letE___override(v_x_245_, v_t_246_, v_v_247_, v_b_248_, v_nondep_249_);
v___x_257_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_256_, v___y_255_);
v_fst_258_ = lean_ctor_get(v___x_257_, 0);
v_snd_259_ = lean_ctor_get(v___x_257_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_267_ == 0)
{
v___x_261_ = v___x_257_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_snd_259_);
lean_inc(v_fst_258_);
lean_dec(v___x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___y_254_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_fst_258_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___y_254_);
v___x_264_ = v_reuseFailAlloc_266_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; 
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_snd_259_);
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5___boxed(lean_object* v_x_274_, lean_object* v_t_275_, lean_object* v_v_276_, lean_object* v_b_277_, lean_object* v_nondep_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
uint8_t v_nondep_boxed_282_; uint8_t v___y_21403__boxed_283_; lean_object* v_res_284_; 
v_nondep_boxed_282_ = lean_unbox(v_nondep_278_);
v___y_21403__boxed_283_ = lean_unbox(v___y_280_);
v_res_284_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_x_274_, v_t_275_, v_v_276_, v_b_277_, v_nondep_boxed_282_, v___y_279_, v___y_21403__boxed_283_, v___y_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(lean_object* v_d_285_, lean_object* v_e_286_, lean_object* v___y_287_, uint8_t v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___y_291_; lean_object* v___y_292_; 
if (v___y_288_ == 0)
{
v___y_291_ = v___y_287_;
v___y_292_ = v___y_289_;
goto v___jp_290_;
}
else
{
lean_object* v___x_305_; lean_object* v_snd_306_; 
lean_inc_ref(v_e_286_);
v___x_305_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_286_, v___y_288_, v___y_289_);
v_snd_306_ = lean_ctor_get(v___x_305_, 1);
lean_inc(v_snd_306_);
lean_dec_ref(v___x_305_);
v___y_291_ = v___y_287_;
v___y_292_ = v_snd_306_;
goto v___jp_290_;
}
v___jp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_fst_295_; lean_object* v_snd_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_304_; 
v___x_293_ = l_Lean_Expr_mdata___override(v_d_285_, v_e_286_);
v___x_294_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_293_, v___y_292_);
v_fst_295_ = lean_ctor_get(v___x_294_, 0);
v_snd_296_ = lean_ctor_get(v___x_294_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_304_ == 0)
{
v___x_298_ = v___x_294_;
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snd_296_);
lean_inc(v_fst_295_);
lean_dec(v___x_294_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v___y_291_);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_fst_295_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___y_291_);
v___x_301_ = v_reuseFailAlloc_303_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; 
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v_snd_296_);
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6___boxed(lean_object* v_d_307_, lean_object* v_e_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___y_21457__boxed_312_; lean_object* v_res_313_; 
v___y_21457__boxed_312_ = lean_unbox(v___y_310_);
v_res_313_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_d_307_, v_e_308_, v___y_309_, v___y_21457__boxed_312_, v___y_311_);
return v_res_313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__2));
v___x_318_ = lean_unsigned_to_nat(67u);
v___x_319_ = lean_unsigned_to_nat(35u);
v___x_320_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__1));
v___x_321_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__0));
v___x_322_ = l_mkPanicMessageWithDecl(v___x_321_, v___x_320_, v___x_319_, v___x_318_, v___x_317_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(lean_object* v_s_323_, lean_object* v_d_324_, lean_object* v_e_325_, lean_object* v_offset_326_, lean_object* v_a_327_, uint8_t v_a_328_, lean_object* v_a_329_){
_start:
{
switch(lean_obj_tag(v_e_325_))
{
case 5:
{
lean_object* v_fn_330_; lean_object* v_arg_331_; lean_object* v___x_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_360_; 
v_fn_330_ = lean_ctor_get(v_e_325_, 0);
v_arg_331_ = lean_ctor_get(v_e_325_, 1);
lean_inc(v_offset_326_);
lean_inc_ref(v_fn_330_);
v___x_332_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_fn_330_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v___x_332_, 1);
lean_inc(v_snd_334_);
lean_dec_ref(v___x_332_);
v_fst_335_ = lean_ctor_get(v_fst_333_, 0);
lean_inc(v_fst_335_);
v_snd_336_ = lean_ctor_get(v_fst_333_, 1);
lean_inc(v_snd_336_);
lean_dec(v_fst_333_);
lean_inc_ref(v_arg_331_);
v___x_337_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_arg_331_, v_offset_326_, v_snd_336_, v_a_328_, v_snd_334_);
v_fst_338_ = lean_ctor_get(v___x_337_, 0);
v_snd_339_ = lean_ctor_get(v___x_337_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_360_ == 0)
{
v___x_341_ = v___x_337_;
v_isShared_342_ = v_isSharedCheck_360_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snd_339_);
lean_inc(v_fst_338_);
lean_dec(v___x_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_360_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_fst_343_; lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_359_; 
v_fst_343_ = lean_ctor_get(v_fst_338_, 0);
v_snd_344_ = lean_ctor_get(v_fst_338_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_fst_338_);
if (v_isSharedCheck_359_ == 0)
{
v___x_346_ = v_fst_338_;
v_isShared_347_ = v_isSharedCheck_359_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_inc(v_fst_343_);
lean_dec(v_fst_338_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_359_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
uint8_t v___y_349_; uint8_t v___x_357_; 
v___x_357_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_330_, v_fst_335_);
if (v___x_357_ == 0)
{
v___y_349_ = v___x_357_;
goto v___jp_348_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_331_, v_fst_343_);
v___y_349_ = v___x_358_;
goto v___jp_348_;
}
v___jp_348_:
{
if (v___y_349_ == 0)
{
lean_object* v___x_350_; 
lean_del_object(v___x_346_);
lean_del_object(v___x_341_);
lean_dec_ref(v_e_325_);
v___x_350_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_335_, v_fst_343_, v_snd_344_, v_a_328_, v_snd_339_);
return v___x_350_;
}
else
{
lean_object* v___x_352_; 
lean_dec(v_fst_343_);
lean_dec(v_fst_335_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v_e_325_);
v___x_352_ = v___x_346_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_snd_344_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_352_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_snd_339_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_361_; lean_object* v_binderType_362_; lean_object* v_body_363_; uint8_t v_binderInfo_364_; lean_object* v___x_365_; lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_fst_373_; lean_object* v_snd_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_395_; 
v_binderName_361_ = lean_ctor_get(v_e_325_, 0);
v_binderType_362_ = lean_ctor_get(v_e_325_, 1);
v_body_363_ = lean_ctor_get(v_e_325_, 2);
v_binderInfo_364_ = lean_ctor_get_uint8(v_e_325_, sizeof(void*)*3 + 8);
lean_inc(v_offset_326_);
lean_inc_ref(v_binderType_362_);
v___x_365_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_binderType_362_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_fst_366_);
v_snd_367_ = lean_ctor_get(v___x_365_, 1);
lean_inc(v_snd_367_);
lean_dec_ref(v___x_365_);
v_fst_368_ = lean_ctor_get(v_fst_366_, 0);
lean_inc(v_fst_368_);
v_snd_369_ = lean_ctor_get(v_fst_366_, 1);
lean_inc(v_snd_369_);
lean_dec(v_fst_366_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_offset_326_, v___x_370_);
lean_dec(v_offset_326_);
lean_inc_ref(v_body_363_);
v___x_372_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_body_363_, v___x_371_, v_snd_369_, v_a_328_, v_snd_367_);
v_fst_373_ = lean_ctor_get(v___x_372_, 0);
v_snd_374_ = lean_ctor_get(v___x_372_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_395_ == 0)
{
v___x_376_ = v___x_372_;
v_isShared_377_ = v_isSharedCheck_395_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_snd_374_);
lean_inc(v_fst_373_);
lean_dec(v___x_372_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_395_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_394_; 
v_fst_378_ = lean_ctor_get(v_fst_373_, 0);
v_snd_379_ = lean_ctor_get(v_fst_373_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_fst_373_);
if (v_isSharedCheck_394_ == 0)
{
v___x_381_ = v_fst_373_;
v_isShared_382_ = v_isSharedCheck_394_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snd_379_);
lean_inc(v_fst_378_);
lean_dec(v_fst_373_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_394_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint8_t v___y_384_; uint8_t v___x_392_; 
v___x_392_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_362_, v_fst_368_);
if (v___x_392_ == 0)
{
v___y_384_ = v___x_392_;
goto v___jp_383_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_363_, v_fst_378_);
v___y_384_ = v___x_393_;
goto v___jp_383_;
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
lean_object* v___x_385_; 
lean_inc(v_binderName_361_);
lean_del_object(v___x_381_);
lean_del_object(v___x_376_);
lean_dec_ref(v_e_325_);
v___x_385_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_361_, v_binderInfo_364_, v_fst_368_, v_fst_378_, v_snd_379_, v_a_328_, v_snd_374_);
return v___x_385_;
}
else
{
lean_object* v___x_387_; 
lean_dec(v_fst_378_);
lean_dec(v_fst_368_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v_e_325_);
v___x_387_ = v___x_381_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_snd_379_);
v___x_387_ = v_reuseFailAlloc_391_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_387_);
v___x_389_ = v___x_376_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_snd_374_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_396_; lean_object* v_binderType_397_; lean_object* v_body_398_; uint8_t v_binderInfo_399_; lean_object* v___x_400_; lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v_fst_403_; lean_object* v_snd_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_430_; 
v_binderName_396_ = lean_ctor_get(v_e_325_, 0);
v_binderType_397_ = lean_ctor_get(v_e_325_, 1);
v_body_398_ = lean_ctor_get(v_e_325_, 2);
v_binderInfo_399_ = lean_ctor_get_uint8(v_e_325_, sizeof(void*)*3 + 8);
lean_inc(v_offset_326_);
lean_inc_ref(v_binderType_397_);
v___x_400_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_binderType_397_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_fst_401_);
v_snd_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc(v_snd_402_);
lean_dec_ref(v___x_400_);
v_fst_403_ = lean_ctor_get(v_fst_401_, 0);
lean_inc(v_fst_403_);
v_snd_404_ = lean_ctor_get(v_fst_401_, 1);
lean_inc(v_snd_404_);
lean_dec(v_fst_401_);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_nat_add(v_offset_326_, v___x_405_);
lean_dec(v_offset_326_);
lean_inc_ref(v_body_398_);
v___x_407_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_body_398_, v___x_406_, v_snd_404_, v_a_328_, v_snd_402_);
v_fst_408_ = lean_ctor_get(v___x_407_, 0);
v_snd_409_ = lean_ctor_get(v___x_407_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_430_ == 0)
{
v___x_411_ = v___x_407_;
v_isShared_412_ = v_isSharedCheck_430_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_snd_409_);
lean_inc(v_fst_408_);
lean_dec(v___x_407_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_430_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_429_; 
v_fst_413_ = lean_ctor_get(v_fst_408_, 0);
v_snd_414_ = lean_ctor_get(v_fst_408_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v_fst_408_);
if (v_isSharedCheck_429_ == 0)
{
v___x_416_ = v_fst_408_;
v_isShared_417_ = v_isSharedCheck_429_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snd_414_);
lean_inc(v_fst_413_);
lean_dec(v_fst_408_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_429_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
uint8_t v___y_419_; uint8_t v___x_427_; 
v___x_427_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_397_, v_fst_403_);
if (v___x_427_ == 0)
{
v___y_419_ = v___x_427_;
goto v___jp_418_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_398_, v_fst_413_);
v___y_419_ = v___x_428_;
goto v___jp_418_;
}
v___jp_418_:
{
if (v___y_419_ == 0)
{
lean_object* v___x_420_; 
lean_inc(v_binderName_396_);
lean_del_object(v___x_416_);
lean_del_object(v___x_411_);
lean_dec_ref(v_e_325_);
v___x_420_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_396_, v_binderInfo_399_, v_fst_403_, v_fst_413_, v_snd_414_, v_a_328_, v_snd_409_);
return v___x_420_;
}
else
{
lean_object* v___x_422_; 
lean_dec(v_fst_413_);
lean_dec(v_fst_403_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_e_325_);
v___x_422_ = v___x_416_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_snd_414_);
v___x_422_ = v_reuseFailAlloc_426_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_424_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_422_);
v___x_424_ = v___x_411_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_snd_409_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_431_; lean_object* v_type_432_; lean_object* v_value_433_; lean_object* v_body_434_; uint8_t v_nondep_435_; lean_object* v___x_436_; lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v_fst_439_; lean_object* v_snd_440_; lean_object* v___x_441_; lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_473_; 
v_declName_431_ = lean_ctor_get(v_e_325_, 0);
v_type_432_ = lean_ctor_get(v_e_325_, 1);
v_value_433_ = lean_ctor_get(v_e_325_, 2);
v_body_434_ = lean_ctor_get(v_e_325_, 3);
v_nondep_435_ = lean_ctor_get_uint8(v_e_325_, sizeof(void*)*4 + 8);
lean_inc(v_offset_326_);
lean_inc_ref(v_type_432_);
v___x_436_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_type_432_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_fst_437_);
v_snd_438_ = lean_ctor_get(v___x_436_, 1);
lean_inc(v_snd_438_);
lean_dec_ref(v___x_436_);
v_fst_439_ = lean_ctor_get(v_fst_437_, 0);
lean_inc(v_fst_439_);
v_snd_440_ = lean_ctor_get(v_fst_437_, 1);
lean_inc(v_snd_440_);
lean_dec(v_fst_437_);
lean_inc(v_offset_326_);
lean_inc_ref(v_value_433_);
v___x_441_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_value_433_, v_offset_326_, v_snd_440_, v_a_328_, v_snd_438_);
v_fst_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_fst_442_);
v_snd_443_ = lean_ctor_get(v___x_441_, 1);
lean_inc(v_snd_443_);
lean_dec_ref(v___x_441_);
v_fst_444_ = lean_ctor_get(v_fst_442_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v_fst_442_, 1);
lean_inc(v_snd_445_);
lean_dec(v_fst_442_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_offset_326_, v___x_446_);
lean_dec(v_offset_326_);
lean_inc_ref(v_body_434_);
v___x_448_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_body_434_, v___x_447_, v_snd_445_, v_a_328_, v_snd_443_);
v_fst_449_ = lean_ctor_get(v___x_448_, 0);
v_snd_450_ = lean_ctor_get(v___x_448_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_473_ == 0)
{
v___x_452_ = v___x_448_;
v_isShared_453_ = v_isSharedCheck_473_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snd_450_);
lean_inc(v_fst_449_);
lean_dec(v___x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_473_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_fst_454_; lean_object* v_snd_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_472_; 
v_fst_454_ = lean_ctor_get(v_fst_449_, 0);
v_snd_455_ = lean_ctor_get(v_fst_449_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_fst_449_);
if (v_isSharedCheck_472_ == 0)
{
v___x_457_ = v_fst_449_;
v_isShared_458_ = v_isSharedCheck_472_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_snd_455_);
lean_inc(v_fst_454_);
lean_dec(v_fst_449_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_472_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
uint8_t v___y_460_; uint8_t v___x_470_; 
v___x_470_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_432_, v_fst_439_);
if (v___x_470_ == 0)
{
v___y_460_ = v___x_470_;
goto v___jp_459_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_433_, v_fst_444_);
v___y_460_ = v___x_471_;
goto v___jp_459_;
}
v___jp_459_:
{
if (v___y_460_ == 0)
{
lean_object* v___x_461_; 
lean_inc(v_declName_431_);
lean_del_object(v___x_457_);
lean_del_object(v___x_452_);
lean_dec_ref(v_e_325_);
v___x_461_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_431_, v_fst_439_, v_fst_444_, v_fst_454_, v_nondep_435_, v_snd_455_, v_a_328_, v_snd_450_);
return v___x_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_434_, v_fst_454_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_inc(v_declName_431_);
lean_del_object(v___x_457_);
lean_del_object(v___x_452_);
lean_dec_ref(v_e_325_);
v___x_463_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_431_, v_fst_439_, v_fst_444_, v_fst_454_, v_nondep_435_, v_snd_455_, v_a_328_, v_snd_450_);
return v___x_463_;
}
else
{
lean_object* v___x_465_; 
lean_dec(v_fst_454_);
lean_dec(v_fst_444_);
lean_dec(v_fst_439_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v_e_325_);
v___x_465_ = v___x_457_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_455_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_465_);
v___x_467_ = v___x_452_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_snd_450_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
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
lean_object* v_data_474_; lean_object* v_expr_475_; lean_object* v___x_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_496_; 
v_data_474_ = lean_ctor_get(v_e_325_, 0);
v_expr_475_ = lean_ctor_get(v_e_325_, 1);
lean_inc_ref(v_expr_475_);
v___x_476_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_expr_475_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_477_ = lean_ctor_get(v___x_476_, 0);
v_snd_478_ = lean_ctor_get(v___x_476_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_496_ == 0)
{
v___x_480_ = v___x_476_;
v_isShared_481_ = v_isSharedCheck_496_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snd_478_);
lean_inc(v_fst_477_);
lean_dec(v___x_476_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_496_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_fst_482_; lean_object* v_snd_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_495_; 
v_fst_482_ = lean_ctor_get(v_fst_477_, 0);
v_snd_483_ = lean_ctor_get(v_fst_477_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_fst_477_);
if (v_isSharedCheck_495_ == 0)
{
v___x_485_ = v_fst_477_;
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_snd_483_);
lean_inc(v_fst_482_);
lean_dec(v_fst_477_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v___x_487_; 
v___x_487_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_475_, v_fst_482_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_inc(v_data_474_);
lean_del_object(v___x_485_);
lean_del_object(v___x_480_);
lean_dec_ref(v_e_325_);
v___x_488_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_474_, v_fst_482_, v_snd_483_, v_a_328_, v_snd_478_);
return v___x_488_;
}
else
{
lean_object* v___x_490_; 
lean_dec(v_fst_482_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v_e_325_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_snd_483_);
v___x_490_ = v_reuseFailAlloc_494_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_490_);
v___x_492_ = v___x_480_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_snd_478_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_497_; lean_object* v_idx_498_; lean_object* v_struct_499_; lean_object* v___x_500_; lean_object* v_fst_501_; lean_object* v_snd_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_520_; 
v_typeName_497_ = lean_ctor_get(v_e_325_, 0);
v_idx_498_ = lean_ctor_get(v_e_325_, 1);
v_struct_499_ = lean_ctor_get(v_e_325_, 2);
lean_inc_ref(v_struct_499_);
v___x_500_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_323_, v_d_324_, v_struct_499_, v_offset_326_, v_a_327_, v_a_328_, v_a_329_);
v_fst_501_ = lean_ctor_get(v___x_500_, 0);
v_snd_502_ = lean_ctor_get(v___x_500_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_520_ == 0)
{
v___x_504_ = v___x_500_;
v_isShared_505_ = v_isSharedCheck_520_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snd_502_);
lean_inc(v_fst_501_);
lean_dec(v___x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_520_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_519_; 
v_fst_506_ = lean_ctor_get(v_fst_501_, 0);
v_snd_507_ = lean_ctor_get(v_fst_501_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_fst_501_);
if (v_isSharedCheck_519_ == 0)
{
v___x_509_ = v_fst_501_;
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_inc(v_fst_506_);
lean_dec(v_fst_501_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_499_, v_fst_506_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
lean_inc(v_idx_498_);
lean_inc(v_typeName_497_);
lean_del_object(v___x_509_);
lean_del_object(v___x_504_);
lean_dec_ref(v_e_325_);
v___x_512_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_497_, v_idx_498_, v_fst_506_, v_snd_507_, v_a_328_, v_snd_502_);
return v___x_512_;
}
else
{
lean_object* v___x_514_; 
lean_dec(v_fst_506_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v_e_325_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_e_325_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_snd_507_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_514_);
v___x_516_ = v___x_504_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_snd_502_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_offset_326_);
lean_dec_ref(v_e_325_);
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_522_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_521_, v_a_327_, v_a_328_, v_a_329_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(lean_object* v_s_523_, lean_object* v_d_524_, lean_object* v_e_525_, lean_object* v_offset_526_, lean_object* v_a_527_, uint8_t v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_key_530_; lean_object* v_snd_532_; lean_object* v___x_545_; 
lean_inc(v_offset_526_);
lean_inc_ref(v_e_525_);
v_key_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_530_, 0, v_e_525_);
lean_ctor_set(v_key_530_, 1, v_offset_526_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_527_, v_key_530_);
if (lean_obj_tag(v___x_545_) == 1)
{
lean_object* v_val_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec_ref(v_key_530_);
lean_dec(v_offset_526_);
lean_dec_ref(v_e_525_);
v_val_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_val_546_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_val_546_);
lean_ctor_set(v___x_547_, 1, v_a_527_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_a_529_);
return v___x_548_;
}
else
{
lean_object* v_s_u2081_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
lean_dec(v___x_545_);
v_s_u2081_549_ = lean_nat_add(v_s_523_, v_offset_526_);
v___x_550_ = l_Lean_Expr_looseBVarRange(v_e_525_);
v___x_551_ = lean_nat_dec_le(v___x_550_, v_s_u2081_549_);
lean_dec(v___x_550_);
if (v___x_551_ == 0)
{
if (lean_obj_tag(v_e_525_) == 0)
{
lean_object* v_deBruijnIndex_552_; uint8_t v___x_553_; 
v_deBruijnIndex_552_ = lean_ctor_get(v_e_525_, 0);
v___x_553_ = lean_nat_dec_le(v_s_u2081_549_, v_deBruijnIndex_552_);
lean_dec(v_s_u2081_549_);
if (v___x_553_ == 0)
{
v_snd_532_ = v_a_529_;
goto v___jp_531_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_558_; 
lean_inc(v_deBruijnIndex_552_);
lean_dec_ref(v_e_525_);
lean_dec(v_offset_526_);
v___x_554_ = lean_nat_sub(v_deBruijnIndex_552_, v_d_524_);
lean_dec(v_deBruijnIndex_552_);
v___x_555_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_554_, v_a_529_);
v_fst_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_fst_556_);
v_snd_557_ = lean_ctor_get(v___x_555_, 1);
lean_inc(v_snd_557_);
lean_dec_ref(v___x_555_);
v___x_558_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_fst_556_, v_a_527_, v_a_528_, v_snd_557_);
return v___x_558_;
}
}
else
{
lean_dec(v_s_u2081_549_);
v_snd_532_ = v_a_529_;
goto v___jp_531_;
}
}
else
{
lean_object* v___x_559_; 
lean_dec(v_s_u2081_549_);
lean_dec(v_offset_526_);
v___x_559_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_a_529_);
return v___x_559_;
}
}
v___jp_531_:
{
switch(lean_obj_tag(v_e_525_))
{
case 9:
{
lean_object* v___x_533_; 
lean_dec(v_offset_526_);
v___x_533_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_533_;
}
case 2:
{
lean_object* v___x_534_; 
lean_dec(v_offset_526_);
v___x_534_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_534_;
}
case 0:
{
lean_object* v___x_535_; 
lean_dec(v_offset_526_);
v___x_535_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_535_;
}
case 1:
{
lean_object* v___x_536_; 
lean_dec(v_offset_526_);
v___x_536_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_536_;
}
case 4:
{
lean_object* v___x_537_; 
lean_dec(v_offset_526_);
v___x_537_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_537_;
}
case 3:
{
lean_object* v___x_538_; 
lean_dec(v_offset_526_);
v___x_538_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_e_525_, v_a_527_, v_a_528_, v_snd_532_);
return v___x_538_;
}
default: 
{
lean_object* v___x_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v_fst_542_; lean_object* v_snd_543_; lean_object* v___x_544_; 
v___x_539_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_523_, v_d_524_, v_e_525_, v_offset_526_, v_a_527_, v_a_528_, v_snd_532_);
v_fst_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_fst_540_);
v_snd_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_snd_541_);
lean_dec_ref(v___x_539_);
v_fst_542_ = lean_ctor_get(v_fst_540_, 0);
lean_inc(v_fst_542_);
v_snd_543_ = lean_ctor_get(v_fst_540_, 1);
lean_inc(v_snd_543_);
lean_dec(v_fst_540_);
v___x_544_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_530_, v_fst_542_, v_snd_543_, v_a_528_, v_snd_541_);
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1___boxed(lean_object* v_s_560_, lean_object* v_d_561_, lean_object* v_e_562_, lean_object* v_offset_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
uint8_t v_a_boxed_567_; lean_object* v_res_568_; 
v_a_boxed_567_ = lean_unbox(v_a_565_);
v_res_568_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1(v_s_560_, v_d_561_, v_e_562_, v_offset_563_, v_a_564_, v_a_boxed_567_, v_a_566_);
lean_dec(v_d_561_);
lean_dec(v_s_560_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___boxed(lean_object* v_s_569_, lean_object* v_d_570_, lean_object* v_e_571_, lean_object* v_offset_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
uint8_t v_a_boxed_576_; lean_object* v_res_577_; 
v_a_boxed_576_ = lean_unbox(v_a_574_);
v_res_577_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_569_, v_d_570_, v_e_571_, v_offset_572_, v_a_573_, v_a_boxed_576_, v_a_575_);
lean_dec(v_d_570_);
lean_dec(v_s_569_);
return v_res_577_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
v___x_579_ = lean_unsigned_to_nat(16u);
v___x_580_ = lean_mk_array(v___x_579_, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__0);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27(lean_object* v_e_584_, lean_object* v_s_585_, lean_object* v_d_586_, uint8_t v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = l_Lean_Expr_looseBVarRange(v_e_584_);
v___x_590_ = lean_nat_dec_le(v___x_589_, v_s_585_);
lean_dec(v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v_snd_593_; 
v___x_591_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_584_) == 0)
{
lean_object* v_deBruijnIndex_613_; uint8_t v___x_614_; 
v_deBruijnIndex_613_ = lean_ctor_get(v_e_584_, 0);
v___x_614_ = lean_nat_dec_le(v_s_585_, v_deBruijnIndex_613_);
if (v___x_614_ == 0)
{
v_snd_593_ = v_a_588_;
goto v___jp_592_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_inc(v_deBruijnIndex_613_);
lean_dec_ref(v_e_584_);
v___x_615_ = lean_nat_sub(v_deBruijnIndex_613_, v_d_586_);
lean_dec(v_deBruijnIndex_613_);
v___x_616_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_615_, v_a_588_);
return v___x_616_;
}
}
else
{
v_snd_593_ = v_a_588_;
goto v___jp_592_;
}
v___jp_592_:
{
switch(lean_obj_tag(v_e_584_))
{
case 9:
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_e_584_);
lean_ctor_set(v___x_594_, 1, v_snd_593_);
return v___x_594_;
}
case 2:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_e_584_);
lean_ctor_set(v___x_595_, 1, v_snd_593_);
return v___x_595_;
}
case 0:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_e_584_);
lean_ctor_set(v___x_596_, 1, v_snd_593_);
return v___x_596_;
}
case 1:
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_e_584_);
lean_ctor_set(v___x_597_, 1, v_snd_593_);
return v___x_597_;
}
case 4:
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_e_584_);
lean_ctor_set(v___x_598_, 1, v_snd_593_);
return v___x_598_;
}
case 3:
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_e_584_);
lean_ctor_set(v___x_599_, 1, v_snd_593_);
return v___x_599_;
}
default: 
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_fst_602_; lean_object* v_snd_603_; lean_object* v_fst_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v___x_600_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_601_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1(v_s_585_, v_d_586_, v_e_584_, v___x_591_, v___x_600_, v_a_587_, v_snd_593_);
v_fst_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_fst_602_);
v_snd_603_ = lean_ctor_get(v___x_601_, 1);
lean_inc(v_snd_603_);
lean_dec_ref(v___x_601_);
v_fst_604_ = lean_ctor_get(v_fst_602_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_fst_602_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_fst_602_, 1);
lean_dec(v_unused_612_);
v___x_606_ = v_fst_602_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_fst_604_);
lean_dec(v_fst_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_snd_603_);
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_fst_604_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_snd_603_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v_e_584_);
lean_ctor_set(v___x_617_, 1, v_a_588_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS_x27___boxed(lean_object* v_e_618_, lean_object* v_s_619_, lean_object* v_d_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
uint8_t v_a_boxed_623_; lean_object* v_res_624_; 
v_a_boxed_623_ = lean_unbox(v_a_621_);
v_res_624_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_618_, v_s_619_, v_d_620_, v_a_boxed_623_, v_a_622_);
lean_dec(v_d_620_);
lean_dec(v_s_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_625_, lean_object* v_m_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_m_626_, v_a_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_629_, lean_object* v_m_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2(v_00_u03b2_629_, v_m_630_, v_a_631_);
lean_dec_ref(v_a_631_);
lean_dec_ref(v_m_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(lean_object* v_00_u03b2_633_, lean_object* v_a_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___redArg(v_a_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b2_637_, lean_object* v_a_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2_spec__10(v_00_u03b2_637_, v_a_638_, v_x_639_);
lean_dec(v_x_639_);
lean_dec_ref(v_a_638_);
return v_res_640_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_641_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_object* v_00_u03b2_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0___closed__1);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_lowerLooseBVarsS_spec__0(lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(lean_object* v_e_647_, lean_object* v_s_648_, lean_object* v_d_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_652_; lean_object* v_share_653_; lean_object* v_maxFVar_654_; lean_object* v_proofInstInfo_655_; lean_object* v_inferType_656_; lean_object* v_getLevel_657_; lean_object* v_congrInfo_658_; lean_object* v_defEqI_659_; lean_object* v_extensions_660_; lean_object* v_issues_661_; uint8_t v_debug_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_696_; 
v___x_652_ = lean_st_ref_take(v_a_650_);
v_share_653_ = lean_ctor_get(v___x_652_, 0);
v_maxFVar_654_ = lean_ctor_get(v___x_652_, 1);
v_proofInstInfo_655_ = lean_ctor_get(v___x_652_, 2);
v_inferType_656_ = lean_ctor_get(v___x_652_, 3);
v_getLevel_657_ = lean_ctor_get(v___x_652_, 4);
v_congrInfo_658_ = lean_ctor_get(v___x_652_, 5);
v_defEqI_659_ = lean_ctor_get(v___x_652_, 6);
v_extensions_660_ = lean_ctor_get(v___x_652_, 7);
v_issues_661_ = lean_ctor_get(v___x_652_, 8);
v_debug_662_ = lean_ctor_get_uint8(v___x_652_, sizeof(void*)*9);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_696_ == 0)
{
v___x_664_ = v___x_652_;
v_isShared_665_ = v_isSharedCheck_696_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_issues_661_);
lean_inc(v_extensions_660_);
lean_inc(v_defEqI_659_);
lean_inc(v_congrInfo_658_);
lean_inc(v_getLevel_657_);
lean_inc(v_inferType_656_);
lean_inc(v_proofInstInfo_655_);
lean_inc(v_maxFVar_654_);
lean_inc(v_share_653_);
lean_dec(v___x_652_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_696_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_maxFVar_654_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_proofInstInfo_655_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_inferType_656_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_getLevel_657_);
lean_ctor_set(v_reuseFailAlloc_695_, 5, v_congrInfo_658_);
lean_ctor_set(v_reuseFailAlloc_695_, 6, v_defEqI_659_);
lean_ctor_set(v_reuseFailAlloc_695_, 7, v_extensions_660_);
lean_ctor_set(v_reuseFailAlloc_695_, 8, v_issues_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*9, v_debug_662_);
v___x_668_ = v_reuseFailAlloc_695_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v_debug_671_; lean_object* v___x_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v___x_675_; lean_object* v_maxFVar_676_; lean_object* v_proofInstInfo_677_; lean_object* v_inferType_678_; lean_object* v_getLevel_679_; lean_object* v_congrInfo_680_; lean_object* v_defEqI_681_; lean_object* v_extensions_682_; lean_object* v_issues_683_; uint8_t v_debug_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
v___x_669_ = lean_st_ref_set(v_a_650_, v___x_668_);
v___x_670_ = lean_st_ref_get(v_a_650_);
v_debug_671_ = lean_ctor_get_uint8(v___x_670_, sizeof(void*)*9);
lean_dec(v___x_670_);
v___x_672_ = l_Lean_Meta_Sym_lowerLooseBVarsS_x27(v_e_647_, v_s_648_, v_d_649_, v_debug_671_, v_share_653_);
v_fst_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_fst_673_);
v_snd_674_ = lean_ctor_get(v___x_672_, 1);
lean_inc(v_snd_674_);
lean_dec_ref(v___x_672_);
v___x_675_ = lean_st_ref_take(v_a_650_);
v_maxFVar_676_ = lean_ctor_get(v___x_675_, 1);
v_proofInstInfo_677_ = lean_ctor_get(v___x_675_, 2);
v_inferType_678_ = lean_ctor_get(v___x_675_, 3);
v_getLevel_679_ = lean_ctor_get(v___x_675_, 4);
v_congrInfo_680_ = lean_ctor_get(v___x_675_, 5);
v_defEqI_681_ = lean_ctor_get(v___x_675_, 6);
v_extensions_682_ = lean_ctor_get(v___x_675_, 7);
v_issues_683_ = lean_ctor_get(v___x_675_, 8);
v_debug_684_ = lean_ctor_get_uint8(v___x_675_, sizeof(void*)*9);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v___x_675_, 0);
lean_dec(v_unused_694_);
v___x_686_ = v___x_675_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_issues_683_);
lean_inc(v_extensions_682_);
lean_inc(v_defEqI_681_);
lean_inc(v_congrInfo_680_);
lean_inc(v_getLevel_679_);
lean_inc(v_inferType_678_);
lean_inc(v_proofInstInfo_677_);
lean_inc(v_maxFVar_676_);
lean_dec(v___x_675_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_snd_674_);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_snd_674_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_maxFVar_676_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_proofInstInfo_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_inferType_678_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_getLevel_679_);
lean_ctor_set(v_reuseFailAlloc_692_, 5, v_congrInfo_680_);
lean_ctor_set(v_reuseFailAlloc_692_, 6, v_defEqI_681_);
lean_ctor_set(v_reuseFailAlloc_692_, 7, v_extensions_682_);
lean_ctor_set(v_reuseFailAlloc_692_, 8, v_issues_683_);
lean_ctor_set_uint8(v_reuseFailAlloc_692_, sizeof(void*)*9, v_debug_684_);
v___x_689_ = v_reuseFailAlloc_692_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_st_ref_set(v_a_650_, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_fst_673_);
return v___x_691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___boxed(lean_object* v_e_697_, lean_object* v_s_698_, lean_object* v_d_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(v_e_697_, v_s_698_, v_d_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec(v_d_699_);
lean_dec(v_s_698_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS(lean_object* v_e_703_, lean_object* v_s_704_, lean_object* v_d_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Meta_Sym_lowerLooseBVarsS___redArg(v_e_703_, v_s_704_, v_d_705_, v_a_707_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_lowerLooseBVarsS___boxed(lean_object* v_e_714_, lean_object* v_s_715_, lean_object* v_d_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Sym_lowerLooseBVarsS(v_e_714_, v_s_715_, v_d_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_d_716_);
lean_dec(v_s_715_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(lean_object* v_s_725_, lean_object* v_d_726_, lean_object* v_e_727_, lean_object* v_offset_728_, lean_object* v_a_729_, uint8_t v_a_730_, lean_object* v_a_731_){
_start:
{
switch(lean_obj_tag(v_e_727_))
{
case 5:
{
lean_object* v_fn_732_; lean_object* v_arg_733_; lean_object* v___x_734_; lean_object* v_fst_735_; lean_object* v_snd_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_739_; lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_762_; 
v_fn_732_ = lean_ctor_get(v_e_727_, 0);
v_arg_733_ = lean_ctor_get(v_e_727_, 1);
lean_inc(v_offset_728_);
lean_inc_ref(v_fn_732_);
v___x_734_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_fn_732_, v_offset_728_, v_a_729_, v_a_730_, v_a_731_);
v_fst_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_fst_735_);
v_snd_736_ = lean_ctor_get(v___x_734_, 1);
lean_inc(v_snd_736_);
lean_dec_ref(v___x_734_);
v_fst_737_ = lean_ctor_get(v_fst_735_, 0);
lean_inc(v_fst_737_);
v_snd_738_ = lean_ctor_get(v_fst_735_, 1);
lean_inc(v_snd_738_);
lean_dec(v_fst_735_);
lean_inc_ref(v_arg_733_);
v___x_739_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_arg_733_, v_offset_728_, v_snd_738_, v_a_730_, v_snd_736_);
v_fst_740_ = lean_ctor_get(v___x_739_, 0);
v_snd_741_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_762_ == 0)
{
v___x_743_ = v___x_739_;
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_snd_741_);
lean_inc(v_fst_740_);
lean_dec(v___x_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_fst_745_; lean_object* v_snd_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_761_; 
v_fst_745_ = lean_ctor_get(v_fst_740_, 0);
v_snd_746_ = lean_ctor_get(v_fst_740_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_fst_740_);
if (v_isSharedCheck_761_ == 0)
{
v___x_748_ = v_fst_740_;
v_isShared_749_ = v_isSharedCheck_761_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_snd_746_);
lean_inc(v_fst_745_);
lean_dec(v_fst_740_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_761_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
uint8_t v___y_751_; uint8_t v___x_759_; 
v___x_759_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_732_, v_fst_737_);
if (v___x_759_ == 0)
{
v___y_751_ = v___x_759_;
goto v___jp_750_;
}
else
{
uint8_t v___x_760_; 
v___x_760_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_733_, v_fst_745_);
v___y_751_ = v___x_760_;
goto v___jp_750_;
}
v___jp_750_:
{
if (v___y_751_ == 0)
{
lean_object* v___x_752_; 
lean_del_object(v___x_748_);
lean_del_object(v___x_743_);
lean_dec_ref(v_e_727_);
v___x_752_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__2(v_fst_737_, v_fst_745_, v_snd_746_, v_a_730_, v_snd_741_);
return v___x_752_;
}
else
{
lean_object* v___x_754_; 
lean_dec(v_fst_745_);
lean_dec(v_fst_737_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v_e_727_);
v___x_754_ = v___x_748_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_e_727_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_snd_746_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_754_);
v___x_756_ = v___x_743_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_snd_741_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_763_; lean_object* v_binderType_764_; lean_object* v_body_765_; uint8_t v_binderInfo_766_; lean_object* v___x_767_; lean_object* v_fst_768_; lean_object* v_snd_769_; lean_object* v_fst_770_; lean_object* v_snd_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_797_; 
v_binderName_763_ = lean_ctor_get(v_e_727_, 0);
v_binderType_764_ = lean_ctor_get(v_e_727_, 1);
v_body_765_ = lean_ctor_get(v_e_727_, 2);
v_binderInfo_766_ = lean_ctor_get_uint8(v_e_727_, sizeof(void*)*3 + 8);
lean_inc(v_offset_728_);
lean_inc_ref(v_binderType_764_);
v___x_767_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_binderType_764_, v_offset_728_, v_a_729_, v_a_730_, v_a_731_);
v_fst_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_fst_768_);
v_snd_769_ = lean_ctor_get(v___x_767_, 1);
lean_inc(v_snd_769_);
lean_dec_ref(v___x_767_);
v_fst_770_ = lean_ctor_get(v_fst_768_, 0);
lean_inc(v_fst_770_);
v_snd_771_ = lean_ctor_get(v_fst_768_, 1);
lean_inc(v_snd_771_);
lean_dec(v_fst_768_);
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_add(v_offset_728_, v___x_772_);
lean_dec(v_offset_728_);
lean_inc_ref(v_body_765_);
v___x_774_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_body_765_, v___x_773_, v_snd_771_, v_a_730_, v_snd_769_);
v_fst_775_ = lean_ctor_get(v___x_774_, 0);
v_snd_776_ = lean_ctor_get(v___x_774_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_797_ == 0)
{
v___x_778_ = v___x_774_;
v_isShared_779_ = v_isSharedCheck_797_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_776_);
lean_inc(v_fst_775_);
lean_dec(v___x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_797_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_796_; 
v_fst_780_ = lean_ctor_get(v_fst_775_, 0);
v_snd_781_ = lean_ctor_get(v_fst_775_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_fst_775_);
if (v_isSharedCheck_796_ == 0)
{
v___x_783_ = v_fst_775_;
v_isShared_784_ = v_isSharedCheck_796_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snd_781_);
lean_inc(v_fst_780_);
lean_dec(v_fst_775_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_796_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
uint8_t v___y_786_; uint8_t v___x_794_; 
v___x_794_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_764_, v_fst_770_);
if (v___x_794_ == 0)
{
v___y_786_ = v___x_794_;
goto v___jp_785_;
}
else
{
uint8_t v___x_795_; 
v___x_795_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_765_, v_fst_780_);
v___y_786_ = v___x_795_;
goto v___jp_785_;
}
v___jp_785_:
{
if (v___y_786_ == 0)
{
lean_object* v___x_787_; 
lean_inc(v_binderName_763_);
lean_del_object(v___x_783_);
lean_del_object(v___x_778_);
lean_dec_ref(v_e_727_);
v___x_787_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__3(v_binderName_763_, v_binderInfo_766_, v_fst_770_, v_fst_780_, v_snd_781_, v_a_730_, v_snd_776_);
return v___x_787_;
}
else
{
lean_object* v___x_789_; 
lean_dec(v_fst_780_);
lean_dec(v_fst_770_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_e_727_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_e_727_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_snd_781_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_789_);
v___x_791_ = v___x_778_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_snd_776_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_798_; lean_object* v_binderType_799_; lean_object* v_body_800_; uint8_t v_binderInfo_801_; lean_object* v___x_802_; lean_object* v_fst_803_; lean_object* v_snd_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_fst_810_; lean_object* v_snd_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_832_; 
v_binderName_798_ = lean_ctor_get(v_e_727_, 0);
v_binderType_799_ = lean_ctor_get(v_e_727_, 1);
v_body_800_ = lean_ctor_get(v_e_727_, 2);
v_binderInfo_801_ = lean_ctor_get_uint8(v_e_727_, sizeof(void*)*3 + 8);
lean_inc(v_offset_728_);
lean_inc_ref(v_binderType_799_);
v___x_802_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_binderType_799_, v_offset_728_, v_a_729_, v_a_730_, v_a_731_);
v_fst_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_fst_803_);
v_snd_804_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_snd_804_);
lean_dec_ref(v___x_802_);
v_fst_805_ = lean_ctor_get(v_fst_803_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v_fst_803_, 1);
lean_inc(v_snd_806_);
lean_dec(v_fst_803_);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_add(v_offset_728_, v___x_807_);
lean_dec(v_offset_728_);
lean_inc_ref(v_body_800_);
v___x_809_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_body_800_, v___x_808_, v_snd_806_, v_a_730_, v_snd_804_);
v_fst_810_ = lean_ctor_get(v___x_809_, 0);
v_snd_811_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_832_ == 0)
{
v___x_813_ = v___x_809_;
v_isShared_814_ = v_isSharedCheck_832_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_snd_811_);
lean_inc(v_fst_810_);
lean_dec(v___x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_832_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_fst_815_; lean_object* v_snd_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_831_; 
v_fst_815_ = lean_ctor_get(v_fst_810_, 0);
v_snd_816_ = lean_ctor_get(v_fst_810_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_fst_810_);
if (v_isSharedCheck_831_ == 0)
{
v___x_818_ = v_fst_810_;
v_isShared_819_ = v_isSharedCheck_831_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_snd_816_);
lean_inc(v_fst_815_);
lean_dec(v_fst_810_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_831_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
uint8_t v___y_821_; uint8_t v___x_829_; 
v___x_829_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_799_, v_fst_805_);
if (v___x_829_ == 0)
{
v___y_821_ = v___x_829_;
goto v___jp_820_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_800_, v_fst_815_);
v___y_821_ = v___x_830_;
goto v___jp_820_;
}
v___jp_820_:
{
if (v___y_821_ == 0)
{
lean_object* v___x_822_; 
lean_inc(v_binderName_798_);
lean_del_object(v___x_818_);
lean_del_object(v___x_813_);
lean_dec_ref(v_e_727_);
v___x_822_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__4(v_binderName_798_, v_binderInfo_801_, v_fst_805_, v_fst_815_, v_snd_816_, v_a_730_, v_snd_811_);
return v___x_822_;
}
else
{
lean_object* v___x_824_; 
lean_dec(v_fst_815_);
lean_dec(v_fst_805_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v_e_727_);
v___x_824_ = v___x_818_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_e_727_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_snd_816_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_826_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_824_);
v___x_826_ = v___x_813_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_snd_811_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_833_; lean_object* v_type_834_; lean_object* v_value_835_; lean_object* v_body_836_; uint8_t v_nondep_837_; lean_object* v___x_838_; lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v_fst_841_; lean_object* v_snd_842_; lean_object* v___x_843_; lean_object* v_fst_844_; lean_object* v_snd_845_; lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_fst_851_; lean_object* v_snd_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_875_; 
v_declName_833_ = lean_ctor_get(v_e_727_, 0);
v_type_834_ = lean_ctor_get(v_e_727_, 1);
v_value_835_ = lean_ctor_get(v_e_727_, 2);
v_body_836_ = lean_ctor_get(v_e_727_, 3);
v_nondep_837_ = lean_ctor_get_uint8(v_e_727_, sizeof(void*)*4 + 8);
lean_inc(v_offset_728_);
lean_inc_ref(v_type_834_);
v___x_838_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_type_834_, v_offset_728_, v_a_729_, v_a_730_, v_a_731_);
v_fst_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_fst_839_);
v_snd_840_ = lean_ctor_get(v___x_838_, 1);
lean_inc(v_snd_840_);
lean_dec_ref(v___x_838_);
v_fst_841_ = lean_ctor_get(v_fst_839_, 0);
lean_inc(v_fst_841_);
v_snd_842_ = lean_ctor_get(v_fst_839_, 1);
lean_inc(v_snd_842_);
lean_dec(v_fst_839_);
lean_inc(v_offset_728_);
lean_inc_ref(v_value_835_);
v___x_843_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_value_835_, v_offset_728_, v_snd_842_, v_a_730_, v_snd_840_);
v_fst_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_fst_844_);
v_snd_845_ = lean_ctor_get(v___x_843_, 1);
lean_inc(v_snd_845_);
lean_dec_ref(v___x_843_);
v_fst_846_ = lean_ctor_get(v_fst_844_, 0);
lean_inc(v_fst_846_);
v_snd_847_ = lean_ctor_get(v_fst_844_, 1);
lean_inc(v_snd_847_);
lean_dec(v_fst_844_);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_add(v_offset_728_, v___x_848_);
lean_dec(v_offset_728_);
lean_inc_ref(v_body_836_);
v___x_850_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_body_836_, v___x_849_, v_snd_847_, v_a_730_, v_snd_845_);
v_fst_851_ = lean_ctor_get(v___x_850_, 0);
v_snd_852_ = lean_ctor_get(v___x_850_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_875_ == 0)
{
v___x_854_ = v___x_850_;
v_isShared_855_ = v_isSharedCheck_875_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snd_852_);
lean_inc(v_fst_851_);
lean_dec(v___x_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_875_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_fst_856_; lean_object* v_snd_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_874_; 
v_fst_856_ = lean_ctor_get(v_fst_851_, 0);
v_snd_857_ = lean_ctor_get(v_fst_851_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_fst_851_);
if (v_isSharedCheck_874_ == 0)
{
v___x_859_ = v_fst_851_;
v_isShared_860_ = v_isSharedCheck_874_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_snd_857_);
lean_inc(v_fst_856_);
lean_dec(v_fst_851_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_874_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
uint8_t v___y_862_; uint8_t v___x_872_; 
v___x_872_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_834_, v_fst_841_);
if (v___x_872_ == 0)
{
v___y_862_ = v___x_872_;
goto v___jp_861_;
}
else
{
uint8_t v___x_873_; 
v___x_873_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_835_, v_fst_846_);
v___y_862_ = v___x_873_;
goto v___jp_861_;
}
v___jp_861_:
{
if (v___y_862_ == 0)
{
lean_object* v___x_863_; 
lean_inc(v_declName_833_);
lean_del_object(v___x_859_);
lean_del_object(v___x_854_);
lean_dec_ref(v_e_727_);
v___x_863_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_833_, v_fst_841_, v_fst_846_, v_fst_856_, v_nondep_837_, v_snd_857_, v_a_730_, v_snd_852_);
return v___x_863_;
}
else
{
uint8_t v___x_864_; 
v___x_864_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_836_, v_fst_856_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_inc(v_declName_833_);
lean_del_object(v___x_859_);
lean_del_object(v___x_854_);
lean_dec_ref(v_e_727_);
v___x_865_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__5(v_declName_833_, v_fst_841_, v_fst_846_, v_fst_856_, v_nondep_837_, v_snd_857_, v_a_730_, v_snd_852_);
return v___x_865_;
}
else
{
lean_object* v___x_867_; 
lean_dec(v_fst_856_);
lean_dec(v_fst_846_);
lean_dec(v_fst_841_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v_e_727_);
v___x_867_ = v___x_859_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_e_727_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_snd_857_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_867_);
v___x_869_ = v___x_854_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_snd_852_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
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
lean_object* v_data_876_; lean_object* v_expr_877_; lean_object* v___x_878_; lean_object* v_fst_879_; lean_object* v_snd_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_898_; 
v_data_876_ = lean_ctor_get(v_e_727_, 0);
v_expr_877_ = lean_ctor_get(v_e_727_, 1);
lean_inc_ref(v_expr_877_);
v___x_878_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_expr_877_, v_offset_728_, v_a_729_, v_a_730_, v_a_731_);
v_fst_879_ = lean_ctor_get(v___x_878_, 0);
v_snd_880_ = lean_ctor_get(v___x_878_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_898_ == 0)
{
v___x_882_ = v___x_878_;
v_isShared_883_ = v_isSharedCheck_898_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_snd_880_);
lean_inc(v_fst_879_);
lean_dec(v___x_878_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_898_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_fst_884_; lean_object* v_snd_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_897_; 
v_fst_884_ = lean_ctor_get(v_fst_879_, 0);
v_snd_885_ = lean_ctor_get(v_fst_879_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_fst_879_);
if (v_isSharedCheck_897_ == 0)
{
v___x_887_ = v_fst_879_;
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_snd_885_);
lean_inc(v_fst_884_);
lean_dec(v_fst_879_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_897_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
uint8_t v___x_889_; 
v___x_889_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_877_, v_fst_884_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_inc(v_data_876_);
lean_del_object(v___x_887_);
lean_del_object(v___x_882_);
lean_dec_ref(v_e_727_);
v___x_890_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__6(v_data_876_, v_fst_884_, v_snd_885_, v_a_730_, v_snd_880_);
return v___x_890_;
}
else
{
lean_object* v___x_892_; 
lean_dec(v_fst_884_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_e_727_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_e_727_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_snd_885_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_892_);
v___x_894_ = v___x_882_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_snd_880_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_899_; lean_object* v_idx_900_; lean_object* v_struct_901_; lean_object* v___x_902_; lean_object* v_fst_903_; lean_object* v_snd_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_922_; 
v_typeName_899_ = lean_ctor_get(v_e_727_, 0);
v_idx_900_ = lean_ctor_get(v_e_727_, 1);
v_struct_901_ = lean_ctor_get(v_e_727_, 2);
lean_inc_ref(v_struct_901_);
v___x_902_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_725_, v_d_726_, v_struct_901_, v_offset_728_, v_a_729_, v_a_730_, v_a_731_);
v_fst_903_ = lean_ctor_get(v___x_902_, 0);
v_snd_904_ = lean_ctor_get(v___x_902_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_922_ == 0)
{
v___x_906_ = v___x_902_;
v_isShared_907_ = v_isSharedCheck_922_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_snd_904_);
lean_inc(v_fst_903_);
lean_dec(v___x_902_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_922_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v_fst_908_ = lean_ctor_get(v_fst_903_, 0);
v_snd_909_ = lean_ctor_get(v_fst_903_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_fst_903_);
if (v_isSharedCheck_921_ == 0)
{
v___x_911_ = v_fst_903_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snd_909_);
lean_inc(v_fst_908_);
lean_dec(v_fst_903_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
uint8_t v___x_913_; 
v___x_913_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_901_, v_fst_908_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_inc(v_idx_900_);
lean_inc(v_typeName_899_);
lean_del_object(v___x_911_);
lean_del_object(v___x_906_);
lean_dec_ref(v_e_727_);
v___x_914_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__7(v_typeName_899_, v_idx_900_, v_fst_908_, v_snd_909_, v_a_730_, v_snd_904_);
return v___x_914_;
}
else
{
lean_object* v___x_916_; 
lean_dec(v_fst_908_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_e_727_);
v___x_916_ = v___x_911_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_e_727_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_snd_909_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_916_);
v___x_918_ = v___x_906_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_snd_904_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_offset_728_);
lean_dec_ref(v_e_727_);
v___x_923_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1___closed__3);
v___x_924_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__8(v___x_923_, v_a_729_, v_a_730_, v_a_731_);
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(lean_object* v_s_925_, lean_object* v_d_926_, lean_object* v_e_927_, lean_object* v_offset_928_, lean_object* v_a_929_, uint8_t v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_key_932_; lean_object* v_snd_934_; lean_object* v___x_947_; 
lean_inc(v_offset_928_);
lean_inc_ref(v_e_927_);
v_key_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_932_, 0, v_e_927_);
lean_ctor_set(v_key_932_, 1, v_offset_928_);
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__1_spec__1_spec__2___redArg(v_a_929_, v_key_932_);
if (lean_obj_tag(v___x_947_) == 1)
{
lean_object* v_val_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec_ref(v_key_932_);
lean_dec(v_offset_928_);
lean_dec_ref(v_e_927_);
v_val_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_val_948_);
lean_dec_ref(v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_val_948_);
lean_ctor_set(v___x_949_, 1, v_a_929_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v_a_931_);
return v___x_950_;
}
else
{
lean_object* v_s_u2081_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
lean_dec(v___x_947_);
v_s_u2081_951_ = lean_nat_add(v_s_925_, v_offset_928_);
v___x_952_ = l_Lean_Expr_looseBVarRange(v_e_927_);
v___x_953_ = lean_nat_dec_le(v___x_952_, v_s_u2081_951_);
lean_dec(v___x_952_);
if (v___x_953_ == 0)
{
if (lean_obj_tag(v_e_927_) == 0)
{
lean_object* v_deBruijnIndex_954_; uint8_t v___x_955_; 
v_deBruijnIndex_954_ = lean_ctor_get(v_e_927_, 0);
v___x_955_ = lean_nat_dec_le(v_s_u2081_951_, v_deBruijnIndex_954_);
lean_dec(v_s_u2081_951_);
if (v___x_955_ == 0)
{
v_snd_934_ = v_a_931_;
goto v___jp_933_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_960_; 
lean_inc(v_deBruijnIndex_954_);
lean_dec_ref(v_e_927_);
lean_dec(v_offset_928_);
v___x_956_ = lean_nat_add(v_deBruijnIndex_954_, v_d_926_);
lean_dec(v_deBruijnIndex_954_);
v___x_957_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_956_, v_a_931_);
v_fst_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_fst_958_);
v_snd_959_ = lean_ctor_get(v___x_957_, 1);
lean_inc(v_snd_959_);
lean_dec_ref(v___x_957_);
v___x_960_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_fst_958_, v_a_929_, v_a_930_, v_snd_959_);
return v___x_960_;
}
}
else
{
lean_dec(v_s_u2081_951_);
v_snd_934_ = v_a_931_;
goto v___jp_933_;
}
}
else
{
lean_object* v___x_961_; 
lean_dec(v_s_u2081_951_);
lean_dec(v_offset_928_);
v___x_961_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_e_927_, v_a_929_, v_a_930_, v_a_931_);
return v___x_961_;
}
}
v___jp_933_:
{
switch(lean_obj_tag(v_e_927_))
{
case 9:
{
lean_object* v___x_935_; 
lean_dec(v_offset_928_);
v___x_935_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_e_927_, v_a_929_, v_a_930_, v_snd_934_);
return v___x_935_;
}
case 2:
{
lean_object* v___x_936_; 
lean_dec(v_offset_928_);
v___x_936_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_e_927_, v_a_929_, v_a_930_, v_snd_934_);
return v___x_936_;
}
case 0:
{
lean_object* v___x_937_; 
lean_dec(v_offset_928_);
v___x_937_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_e_927_, v_a_929_, v_a_930_, v_snd_934_);
return v___x_937_;
}
case 1:
{
lean_object* v___x_938_; 
lean_dec(v_offset_928_);
v___x_938_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_e_927_, v_a_929_, v_a_930_, v_snd_934_);
return v___x_938_;
}
case 4:
{
lean_object* v___x_939_; 
lean_dec(v_offset_928_);
v___x_939_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_e_927_, v_a_929_, v_a_930_, v_snd_934_);
return v___x_939_;
}
case 3:
{
lean_object* v___x_940_; 
lean_dec(v_offset_928_);
v___x_940_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_e_927_, v_a_929_, v_a_930_, v_snd_934_);
return v___x_940_;
}
default: 
{
lean_object* v___x_941_; lean_object* v_fst_942_; lean_object* v_snd_943_; lean_object* v_fst_944_; lean_object* v_snd_945_; lean_object* v___x_946_; 
v___x_941_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_925_, v_d_926_, v_e_927_, v_offset_928_, v_a_929_, v_a_930_, v_snd_934_);
v_fst_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_fst_942_);
v_snd_943_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_snd_943_);
lean_dec_ref(v___x_941_);
v_fst_944_ = lean_ctor_get(v_fst_942_, 0);
lean_inc(v_fst_944_);
v_snd_945_ = lean_ctor_get(v_fst_942_, 1);
lean_inc(v_snd_945_);
lean_dec(v_fst_942_);
v___x_946_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_932_, v_fst_944_, v_snd_945_, v_a_930_, v_snd_943_);
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0___boxed(lean_object* v_s_962_, lean_object* v_d_963_, lean_object* v_e_964_, lean_object* v_offset_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
uint8_t v_a_boxed_969_; lean_object* v_res_970_; 
v_a_boxed_969_ = lean_unbox(v_a_967_);
v_res_970_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0_spec__0(v_s_962_, v_d_963_, v_e_964_, v_offset_965_, v_a_966_, v_a_boxed_969_, v_a_968_);
lean_dec(v_d_963_);
lean_dec(v_s_962_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0___boxed(lean_object* v_s_971_, lean_object* v_d_972_, lean_object* v_e_973_, lean_object* v_offset_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
uint8_t v_a_boxed_978_; lean_object* v_res_979_; 
v_a_boxed_978_ = lean_unbox(v_a_976_);
v_res_979_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_971_, v_d_972_, v_e_973_, v_offset_974_, v_a_975_, v_a_boxed_978_, v_a_977_);
lean_dec(v_d_972_);
lean_dec(v_s_971_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27(lean_object* v_e_980_, lean_object* v_s_981_, lean_object* v_d_982_, uint8_t v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = l_Lean_Expr_looseBVarRange(v_e_980_);
v___x_986_ = lean_nat_dec_le(v___x_985_, v_s_981_);
lean_dec(v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v_snd_989_; 
v___x_987_ = lean_unsigned_to_nat(0u);
if (lean_obj_tag(v_e_980_) == 0)
{
lean_object* v_deBruijnIndex_1009_; uint8_t v___x_1010_; 
v_deBruijnIndex_1009_ = lean_ctor_get(v_e_980_, 0);
v___x_1010_ = lean_nat_dec_le(v_s_981_, v_deBruijnIndex_1009_);
if (v___x_1010_ == 0)
{
v_snd_989_ = v_a_984_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_inc(v_deBruijnIndex_1009_);
lean_dec_ref(v_e_980_);
v___x_1011_ = lean_nat_add(v_deBruijnIndex_1009_, v_d_982_);
lean_dec(v_deBruijnIndex_1009_);
v___x_1012_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_lowerLooseBVarsS_x27_spec__0___redArg(v___x_1011_, v_a_984_);
return v___x_1012_;
}
}
else
{
v_snd_989_ = v_a_984_;
goto v___jp_988_;
}
v___jp_988_:
{
switch(lean_obj_tag(v_e_980_))
{
case 9:
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v_e_980_);
lean_ctor_set(v___x_990_, 1, v_snd_989_);
return v___x_990_;
}
case 2:
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_e_980_);
lean_ctor_set(v___x_991_, 1, v_snd_989_);
return v___x_991_;
}
case 0:
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_e_980_);
lean_ctor_set(v___x_992_, 1, v_snd_989_);
return v___x_992_;
}
case 1:
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v_e_980_);
lean_ctor_set(v___x_993_, 1, v_snd_989_);
return v___x_993_;
}
case 4:
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v_e_980_);
lean_ctor_set(v___x_994_, 1, v_snd_989_);
return v___x_994_;
}
case 3:
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v_e_980_);
lean_ctor_set(v___x_995_, 1, v_snd_989_);
return v___x_995_;
}
default: 
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v_fst_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v___x_996_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1, &l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS_x27___closed__1);
v___x_997_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_liftLooseBVarsS_x27_spec__0(v_s_981_, v_d_982_, v_e_980_, v___x_987_, v___x_996_, v_a_983_, v_snd_989_);
v_fst_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_fst_998_);
v_snd_999_ = lean_ctor_get(v___x_997_, 1);
lean_inc(v_snd_999_);
lean_dec_ref(v___x_997_);
v_fst_1000_ = lean_ctor_get(v_fst_998_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_fst_998_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; 
v_unused_1008_ = lean_ctor_get(v_fst_998_, 1);
lean_dec(v_unused_1008_);
v___x_1002_ = v_fst_998_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_fst_1000_);
lean_dec(v_fst_998_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 1, v_snd_999_);
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_fst_1000_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_snd_999_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_e_980_);
lean_ctor_set(v___x_1013_, 1, v_a_984_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS_x27___boxed(lean_object* v_e_1014_, lean_object* v_s_1015_, lean_object* v_d_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_a_boxed_1019_; lean_object* v_res_1020_; 
v_a_boxed_1019_ = lean_unbox(v_a_1017_);
v_res_1020_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1014_, v_s_1015_, v_d_1016_, v_a_boxed_1019_, v_a_1018_);
lean_dec(v_d_1016_);
lean_dec(v_s_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___redArg(lean_object* v_e_1021_, lean_object* v_s_1022_, lean_object* v_d_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v_share_1027_; lean_object* v_maxFVar_1028_; lean_object* v_proofInstInfo_1029_; lean_object* v_inferType_1030_; lean_object* v_getLevel_1031_; lean_object* v_congrInfo_1032_; lean_object* v_defEqI_1033_; lean_object* v_extensions_1034_; lean_object* v_issues_1035_; uint8_t v_debug_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1070_; 
v___x_1026_ = lean_st_ref_take(v_a_1024_);
v_share_1027_ = lean_ctor_get(v___x_1026_, 0);
v_maxFVar_1028_ = lean_ctor_get(v___x_1026_, 1);
v_proofInstInfo_1029_ = lean_ctor_get(v___x_1026_, 2);
v_inferType_1030_ = lean_ctor_get(v___x_1026_, 3);
v_getLevel_1031_ = lean_ctor_get(v___x_1026_, 4);
v_congrInfo_1032_ = lean_ctor_get(v___x_1026_, 5);
v_defEqI_1033_ = lean_ctor_get(v___x_1026_, 6);
v_extensions_1034_ = lean_ctor_get(v___x_1026_, 7);
v_issues_1035_ = lean_ctor_get(v___x_1026_, 8);
v_debug_1036_ = lean_ctor_get_uint8(v___x_1026_, sizeof(void*)*9);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1038_ = v___x_1026_;
v_isShared_1039_ = v_isSharedCheck_1070_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_issues_1035_);
lean_inc(v_extensions_1034_);
lean_inc(v_defEqI_1033_);
lean_inc(v_congrInfo_1032_);
lean_inc(v_getLevel_1031_);
lean_inc(v_inferType_1030_);
lean_inc(v_proofInstInfo_1029_);
lean_inc(v_maxFVar_1028_);
lean_inc(v_share_1027_);
lean_dec(v___x_1026_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1070_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = lean_obj_once(&l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0, &l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0_once, _init_l_Lean_Meta_Sym_lowerLooseBVarsS___redArg___closed__0);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_maxFVar_1028_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_proofInstInfo_1029_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_inferType_1030_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v_getLevel_1031_);
lean_ctor_set(v_reuseFailAlloc_1069_, 5, v_congrInfo_1032_);
lean_ctor_set(v_reuseFailAlloc_1069_, 6, v_defEqI_1033_);
lean_ctor_set(v_reuseFailAlloc_1069_, 7, v_extensions_1034_);
lean_ctor_set(v_reuseFailAlloc_1069_, 8, v_issues_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*9, v_debug_1036_);
v___x_1042_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v_debug_1045_; lean_object* v___x_1046_; lean_object* v_fst_1047_; lean_object* v_snd_1048_; lean_object* v___x_1049_; lean_object* v_maxFVar_1050_; lean_object* v_proofInstInfo_1051_; lean_object* v_inferType_1052_; lean_object* v_getLevel_1053_; lean_object* v_congrInfo_1054_; lean_object* v_defEqI_1055_; lean_object* v_extensions_1056_; lean_object* v_issues_1057_; uint8_t v_debug_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1067_; 
v___x_1043_ = lean_st_ref_set(v_a_1024_, v___x_1042_);
v___x_1044_ = lean_st_ref_get(v_a_1024_);
v_debug_1045_ = lean_ctor_get_uint8(v___x_1044_, sizeof(void*)*9);
lean_dec(v___x_1044_);
v___x_1046_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(v_e_1021_, v_s_1022_, v_d_1023_, v_debug_1045_, v_share_1027_);
v_fst_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_fst_1047_);
v_snd_1048_ = lean_ctor_get(v___x_1046_, 1);
lean_inc(v_snd_1048_);
lean_dec_ref(v___x_1046_);
v___x_1049_ = lean_st_ref_take(v_a_1024_);
v_maxFVar_1050_ = lean_ctor_get(v___x_1049_, 1);
v_proofInstInfo_1051_ = lean_ctor_get(v___x_1049_, 2);
v_inferType_1052_ = lean_ctor_get(v___x_1049_, 3);
v_getLevel_1053_ = lean_ctor_get(v___x_1049_, 4);
v_congrInfo_1054_ = lean_ctor_get(v___x_1049_, 5);
v_defEqI_1055_ = lean_ctor_get(v___x_1049_, 6);
v_extensions_1056_ = lean_ctor_get(v___x_1049_, 7);
v_issues_1057_ = lean_ctor_get(v___x_1049_, 8);
v_debug_1058_ = lean_ctor_get_uint8(v___x_1049_, sizeof(void*)*9);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v___x_1049_, 0);
lean_dec(v_unused_1068_);
v___x_1060_ = v___x_1049_;
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_issues_1057_);
lean_inc(v_extensions_1056_);
lean_inc(v_defEqI_1055_);
lean_inc(v_congrInfo_1054_);
lean_inc(v_getLevel_1053_);
lean_inc(v_inferType_1052_);
lean_inc(v_proofInstInfo_1051_);
lean_inc(v_maxFVar_1050_);
lean_dec(v___x_1049_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1067_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v_snd_1048_);
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_snd_1048_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_maxFVar_1050_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_proofInstInfo_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_inferType_1052_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_getLevel_1053_);
lean_ctor_set(v_reuseFailAlloc_1066_, 5, v_congrInfo_1054_);
lean_ctor_set(v_reuseFailAlloc_1066_, 6, v_defEqI_1055_);
lean_ctor_set(v_reuseFailAlloc_1066_, 7, v_extensions_1056_);
lean_ctor_set(v_reuseFailAlloc_1066_, 8, v_issues_1057_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*9, v_debug_1058_);
v___x_1063_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_st_ref_set(v_a_1024_, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_fst_1047_);
return v___x_1065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___redArg___boxed(lean_object* v_e_1071_, lean_object* v_s_1072_, lean_object* v_d_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Meta_Sym_liftLooseBVarsS___redArg(v_e_1071_, v_s_1072_, v_d_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec(v_d_1073_);
lean_dec(v_s_1072_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS(lean_object* v_e_1077_, lean_object* v_s_1078_, lean_object* v_d_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Meta_Sym_liftLooseBVarsS___redArg(v_e_1077_, v_s_1078_, v_d_1079_, v_a_1081_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_liftLooseBVarsS___boxed(lean_object* v_e_1088_, lean_object* v_s_1089_, lean_object* v_d_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Meta_Sym_liftLooseBVarsS(v_e_1088_, v_s_1089_, v_d_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_d_1090_);
lean_dec(v_s_1089_);
return v_res_1098_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LooseBVarsS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
}
#ifdef __cplusplus
}
#endif
