// Lean compiler output
// Module: Lean.Meta.Sym.AlphaShareBuilder
// Imports: public import Lean.Meta.Sym.SymM
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_isDebugEnabled___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "__dummy__"};
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 141, 137, 132, 208, 124, 31, 129)}};
static const lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Sym.AlphaShareBuilder"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Sym.Internal.Sym.assertShared"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "assertion violation: isSameExpr prev.expr e\n\n"};
static const lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Sym_share1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_isDebugEnabled___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value),((lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value)}};
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Meta.Sym.Internal.Builder.assertShared"};
static const lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 121, .m_capacity = 121, .m_length = 116, .m_data = "assertion violation: ( __do_lift._@.Lean.Meta.Sym.AlphaShareBuilder.3401574005._hygCtx._hyg.9.0 ).set.contains ⟨e⟩\n\n"};
static const lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Builder_share1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateAppS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateAppS!"};
static const lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateAppS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateAppS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateAppS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateAppS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateAppS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateMDataS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Expr.updateMDataS!"};
static const lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateMDataS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateMDataS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mdata expected"};
static const lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateMDataS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateMDataS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateProjS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Expr.updateProjS!"};
static const lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateProjS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateProjS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateProjS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateProjS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateProjS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateForallS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateForallS!"};
static const lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateForallS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateForallS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "forall expected"};
static const lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateForallS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateForallS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateForallS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLambdaS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Expr.updateLambdaS!"};
static const lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateLambdaS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateLambdaS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "lambda expected"};
static const lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateLambdaS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLambdaS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_updateLetS_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Expr.updateLetS!"};
static const lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_updateLetS_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_updateLetS_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "let expression expected"};
static const lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_updateLetS_x21___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Expr_updateLetS_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_updateLetS_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0(lean_object* v_share1_1_, lean_object* v_inst_2_, lean_object* v_e_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_share1_1_, v_e_3_);
v___x_5_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1(lean_object* v_assertShared_6_, lean_object* v_inst_7_, lean_object* v_e_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_apply_1(v_assertShared_6_, v_e_8_);
v___x_10_ = lean_apply_2(v_inst_7_, lean_box(0), v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg(lean_object* v_inst_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v_share1_13_; lean_object* v_assertShared_14_; lean_object* v_isDebugEnabled_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_25_; 
v_share1_13_ = lean_ctor_get(v_inst_12_, 0);
v_assertShared_14_ = lean_ctor_get(v_inst_12_, 1);
v_isDebugEnabled_15_ = lean_ctor_get(v_inst_12_, 2);
v_isSharedCheck_25_ = !lean_is_exclusive(v_inst_12_);
if (v_isSharedCheck_25_ == 0)
{
v___x_17_ = v_inst_12_;
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_isDebugEnabled_15_);
lean_inc(v_assertShared_14_);
lean_inc(v_share1_13_);
lean_dec(v_inst_12_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_25_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___f_19_; lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_23_; 
lean_inc(v_inst_11_);
v___f_19_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_19_, 0, v_share1_13_);
lean_closure_set(v___f_19_, 1, v_inst_11_);
lean_inc(v_inst_11_);
v___f_20_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_20_, 0, v_assertShared_14_);
lean_closure_set(v___f_20_, 1, v_inst_11_);
v___x_21_ = lean_apply_2(v_inst_11_, lean_box(0), v_isDebugEnabled_15_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 2, v___x_21_);
lean_ctor_set(v___x_17_, 1, v___f_20_);
lean_ctor_set(v___x_17_, 0, v___f_19_);
v___x_23_ = v___x_17_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___f_19_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v___f_20_);
lean_ctor_set(v_reuseFailAlloc_24_, 2, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift(lean_object* v_m_26_, lean_object* v_n_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
lean_object* v_share1_30_; lean_object* v_assertShared_31_; lean_object* v_isDebugEnabled_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_42_; 
v_share1_30_ = lean_ctor_get(v_inst_29_, 0);
v_assertShared_31_ = lean_ctor_get(v_inst_29_, 1);
v_isDebugEnabled_32_ = lean_ctor_get(v_inst_29_, 2);
v_isSharedCheck_42_ = !lean_is_exclusive(v_inst_29_);
if (v_isSharedCheck_42_ == 0)
{
v___x_34_ = v_inst_29_;
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_isDebugEnabled_32_);
lean_inc(v_assertShared_31_);
lean_inc(v_share1_30_);
lean_dec(v_inst_29_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_42_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_inst_28_);
v___f_36_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_36_, 0, v_share1_30_);
lean_closure_set(v___f_36_, 1, v_inst_28_);
lean_inc(v_inst_28_);
v___f_37_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1), 3, 2);
lean_closure_set(v___f_37_, 0, v_assertShared_31_);
lean_closure_set(v___f_37_, 1, v_inst_28_);
v___x_38_ = lean_apply_2(v_inst_28_, lean_box(0), v_isDebugEnabled_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 2, v___x_38_);
lean_ctor_set(v___x_34_, 1, v___f_37_);
lean_ctor_set(v___x_34_, 0, v___f_36_);
v___x_40_ = v___x_34_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___f_36_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___f_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = ((lean_object*)(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1));
v___x_48_ = l_Lean_mkConst(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2, &l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2_once, _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_ks_54_; lean_object* v_vs_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_79_; 
v_ks_54_ = lean_ctor_get(v_x_50_, 0);
v_vs_55_ = lean_ctor_get(v_x_50_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_79_ == 0)
{
v___x_57_ = v_x_50_;
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_vs_55_);
lean_inc(v_ks_54_);
lean_dec(v_x_50_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_79_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_array_get_size(v_ks_54_);
v___x_60_ = lean_nat_dec_lt(v_x_51_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
lean_dec(v_x_51_);
v___x_61_ = lean_array_push(v_ks_54_, v_x_52_);
v___x_62_ = lean_array_push(v_vs_55_, v_x_53_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_62_);
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
else
{
lean_object* v_k_x27_66_; uint8_t v___x_67_; 
v_k_x27_66_ = lean_array_fget_borrowed(v_ks_54_, v_x_51_);
lean_inc(v_k_x27_66_);
lean_inc_ref(v_x_52_);
v___x_67_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_52_, v_k_x27_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_69_; 
if (v_isShared_58_ == 0)
{
v___x_69_ = v___x_57_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_ks_54_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_vs_55_);
v___x_69_ = v_reuseFailAlloc_73_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_x_51_, v___x_70_);
lean_dec(v_x_51_);
v_x_50_ = v___x_69_;
v_x_51_ = v___x_71_;
goto _start;
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = lean_array_fset(v_ks_54_, v_x_51_, v_x_52_);
v___x_75_ = lean_array_fset(v_vs_55_, v_x_51_, v_x_53_);
lean_dec(v_x_51_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 1, v___x_75_);
lean_ctor_set(v___x_57_, 0, v___x_74_);
v___x_77_ = v___x_57_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_80_, lean_object* v_k_81_, lean_object* v_v_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_80_, v___x_83_, v_k_81_, v_v_82_);
return v___x_84_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; 
v___x_85_ = ((size_t)5ULL);
v___x_86_ = ((size_t)1ULL);
v___x_87_ = lean_usize_shift_left(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; 
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0);
v___x_90_ = lean_usize_sub(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(lean_object* v_x_92_, size_t v_x_93_, size_t v_x_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v_es_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; lean_object* v_j_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_es_97_ = lean_ctor_get(v_x_92_, 0);
v___x_98_ = ((size_t)5ULL);
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
v___x_101_ = lean_usize_land(v_x_93_, v___x_100_);
v_j_102_ = lean_usize_to_nat(v___x_101_);
v___x_103_ = lean_array_get_size(v_es_97_);
v___x_104_ = lean_nat_dec_lt(v_j_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_dec(v_j_102_);
lean_dec(v_x_96_);
lean_dec_ref(v_x_95_);
return v_x_92_;
}
else
{
lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_141_; 
lean_inc_ref(v_es_97_);
v_isSharedCheck_141_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v_x_92_, 0);
lean_dec(v_unused_142_);
v___x_106_ = v_x_92_;
v_isShared_107_ = v_isSharedCheck_141_;
goto v_resetjp_105_;
}
else
{
lean_dec(v_x_92_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_141_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_v_108_; lean_object* v___x_109_; lean_object* v_xs_x27_110_; lean_object* v___y_112_; 
v_v_108_ = lean_array_fget(v_es_97_, v_j_102_);
v___x_109_ = lean_box(0);
v_xs_x27_110_ = lean_array_fset(v_es_97_, v_j_102_, v___x_109_);
switch(lean_obj_tag(v_v_108_))
{
case 0:
{
lean_object* v_key_117_; lean_object* v_val_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_key_117_ = lean_ctor_get(v_v_108_, 0);
v_val_118_ = lean_ctor_get(v_v_108_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_v_108_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v_v_108_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_val_118_);
lean_inc(v_key_117_);
lean_dec(v_v_108_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
uint8_t v___x_122_; 
lean_inc(v_key_117_);
lean_inc_ref(v_x_95_);
v___x_122_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_95_, v_key_117_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_del_object(v___x_120_);
v___x_123_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_117_, v_val_118_, v_x_95_, v_x_96_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
v___y_112_ = v___x_124_;
goto v___jp_111_;
}
else
{
lean_object* v___x_126_; 
lean_dec(v_val_118_);
lean_dec(v_key_117_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v_x_96_);
lean_ctor_set(v___x_120_, 0, v_x_95_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_x_95_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_x_96_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v___y_112_ = v___x_126_;
goto v___jp_111_;
}
}
}
}
case 1:
{
lean_object* v_node_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_139_; 
v_node_129_ = lean_ctor_get(v_v_108_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v_v_108_);
if (v_isSharedCheck_139_ == 0)
{
v___x_131_ = v_v_108_;
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_node_129_);
lean_dec(v_v_108_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_139_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
size_t v___x_133_; size_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_133_ = lean_usize_shift_right(v_x_93_, v___x_98_);
v___x_134_ = lean_usize_add(v_x_94_, v___x_99_);
v___x_135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_node_129_, v___x_133_, v___x_134_, v_x_95_, v_x_96_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_135_);
v___x_137_ = v___x_131_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
v___y_112_ = v___x_137_;
goto v___jp_111_;
}
}
}
default: 
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v_x_95_);
lean_ctor_set(v___x_140_, 1, v_x_96_);
v___y_112_ = v___x_140_;
goto v___jp_111_;
}
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_array_fset(v_xs_x27_110_, v_j_102_, v___y_112_);
lean_dec(v_j_102_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_113_);
v___x_115_ = v___x_106_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
else
{
lean_object* v_ks_143_; lean_object* v_vs_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_164_; 
v_ks_143_ = lean_ctor_get(v_x_92_, 0);
v_vs_144_ = lean_ctor_get(v_x_92_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_164_ == 0)
{
v___x_146_ = v_x_92_;
v_isShared_147_ = v_isSharedCheck_164_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_vs_144_);
lean_inc(v_ks_143_);
lean_dec(v_x_92_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_164_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_ks_143_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_vs_144_);
v___x_149_ = v_reuseFailAlloc_163_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v_newNode_150_; uint8_t v___y_152_; size_t v___x_158_; uint8_t v___x_159_; 
v_newNode_150_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v___x_149_, v_x_95_, v_x_96_);
v___x_158_ = ((size_t)7ULL);
v___x_159_ = lean_usize_dec_le(v___x_158_, v_x_94_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_150_);
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = lean_nat_dec_lt(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
v___y_152_ = v___x_162_;
goto v___jp_151_;
}
else
{
v___y_152_ = v___x_159_;
goto v___jp_151_;
}
v___jp_151_:
{
if (v___y_152_ == 0)
{
lean_object* v_ks_153_; lean_object* v_vs_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_ks_153_ = lean_ctor_get(v_newNode_150_, 0);
lean_inc_ref(v_ks_153_);
v_vs_154_ = lean_ctor_get(v_newNode_150_, 1);
lean_inc_ref(v_vs_154_);
lean_dec_ref(v_newNode_150_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2);
v___x_157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_x_94_, v_ks_153_, v_vs_154_, v___x_155_, v___x_156_);
lean_dec_ref(v_vs_154_);
lean_dec_ref(v_ks_153_);
return v___x_157_;
}
else
{
return v_newNode_150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(size_t v_depth_165_, lean_object* v_keys_166_, lean_object* v_vals_167_, lean_object* v_i_168_, lean_object* v_entries_169_){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_array_get_size(v_keys_166_);
v___x_171_ = lean_nat_dec_lt(v_i_168_, v___x_170_);
if (v___x_171_ == 0)
{
lean_dec(v_i_168_);
return v_entries_169_;
}
else
{
lean_object* v_k_172_; lean_object* v_v_173_; uint64_t v___x_174_; size_t v_h_175_; size_t v___x_176_; lean_object* v___x_177_; size_t v___x_178_; size_t v___x_179_; size_t v___x_180_; size_t v_h_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_k_172_ = lean_array_fget_borrowed(v_keys_166_, v_i_168_);
v_v_173_ = lean_array_fget_borrowed(v_vals_167_, v_i_168_);
v___x_174_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_k_172_);
v_h_175_ = lean_uint64_to_usize(v___x_174_);
v___x_176_ = ((size_t)5ULL);
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_sub(v_depth_165_, v___x_178_);
v___x_180_ = lean_usize_mul(v___x_176_, v___x_179_);
v_h_181_ = lean_usize_shift_right(v_h_175_, v___x_180_);
v___x_182_ = lean_nat_add(v_i_168_, v___x_177_);
lean_dec(v_i_168_);
lean_inc(v_v_173_);
lean_inc(v_k_172_);
v___x_183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_entries_169_, v_h_181_, v_depth_165_, v_k_172_, v_v_173_);
v_i_168_ = v___x_182_;
v_entries_169_ = v___x_183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_185_, lean_object* v_keys_186_, lean_object* v_vals_187_, lean_object* v_i_188_, lean_object* v_entries_189_){
_start:
{
size_t v_depth_boxed_190_; lean_object* v_res_191_; 
v_depth_boxed_190_ = lean_unbox_usize(v_depth_185_);
lean_dec(v_depth_185_);
v_res_191_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_190_, v_keys_186_, v_vals_187_, v_i_188_, v_entries_189_);
lean_dec_ref(v_vals_187_);
lean_dec_ref(v_keys_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
size_t v_x_2157__boxed_197_; size_t v_x_2158__boxed_198_; lean_object* v_res_199_; 
v_x_2157__boxed_197_ = lean_unbox_usize(v_x_193_);
lean_dec(v_x_193_);
v_x_2158__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_res_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_192_, v_x_2157__boxed_197_, v_x_2158__boxed_198_, v_x_195_, v_x_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint64_t v___x_203_; size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; 
v___x_203_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_201_);
v___x_204_ = lean_uint64_to_usize(v___x_203_);
v___x_205_ = ((size_t)1ULL);
v___x_206_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_200_, v___x_204_, v___x_205_, v_x_201_, v_x_202_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(lean_object* v_keys_207_, lean_object* v_i_208_, lean_object* v_k_209_, lean_object* v_k_u2080_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_array_get_size(v_keys_207_);
v___x_212_ = lean_nat_dec_lt(v_i_208_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_k_209_);
lean_dec(v_i_208_);
lean_inc_ref(v_k_u2080_210_);
return v_k_u2080_210_;
}
else
{
lean_object* v_k_x27_213_; uint8_t v___x_214_; 
v_k_x27_213_ = lean_array_fget_borrowed(v_keys_207_, v_i_208_);
lean_inc(v_k_x27_213_);
lean_inc_ref(v_k_209_);
v___x_214_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_209_, v_k_x27_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_i_208_, v___x_215_);
lean_dec(v_i_208_);
v_i_208_ = v___x_216_;
goto _start;
}
else
{
lean_dec_ref(v_k_209_);
lean_dec(v_i_208_);
lean_inc(v_k_x27_213_);
return v_k_x27_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(lean_object* v_keys_218_, lean_object* v_i_219_, lean_object* v_k_220_, lean_object* v_k_u2080_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_218_, v_i_219_, v_k_220_, v_k_u2080_221_);
lean_dec_ref(v_k_u2080_221_);
lean_dec_ref(v_keys_218_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(lean_object* v_x_223_, size_t v_x_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v_es_227_; lean_object* v___x_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v_j_232_; lean_object* v___x_233_; 
v_es_227_ = lean_ctor_get(v_x_223_, 0);
lean_inc_ref(v_es_227_);
lean_dec_ref(v_x_223_);
v___x_228_ = lean_box(2);
v___x_229_ = ((size_t)5ULL);
v___x_230_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
v___x_231_ = lean_usize_land(v_x_224_, v___x_230_);
v_j_232_ = lean_usize_to_nat(v___x_231_);
v___x_233_ = lean_array_get(v___x_228_, v_es_227_, v_j_232_);
lean_dec(v_j_232_);
lean_dec_ref(v_es_227_);
switch(lean_obj_tag(v___x_233_))
{
case 0:
{
lean_object* v_key_234_; uint8_t v___x_235_; 
v_key_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_key_234_);
lean_dec_ref(v___x_233_);
lean_inc(v_key_234_);
v___x_235_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_225_, v_key_234_);
if (v___x_235_ == 0)
{
lean_dec(v_key_234_);
lean_inc_ref(v_x_226_);
return v_x_226_;
}
else
{
return v_key_234_;
}
}
case 1:
{
lean_object* v_node_236_; size_t v___x_237_; 
v_node_236_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_node_236_);
lean_dec_ref(v___x_233_);
v___x_237_ = lean_usize_shift_right(v_x_224_, v___x_229_);
v_x_223_ = v_node_236_;
v_x_224_ = v___x_237_;
goto _start;
}
default: 
{
lean_dec_ref(v_x_225_);
lean_inc_ref(v_x_226_);
return v_x_226_;
}
}
}
else
{
lean_object* v_ks_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_ks_239_ = lean_ctor_get(v_x_223_, 0);
lean_inc_ref(v_ks_239_);
lean_dec_ref(v_x_223_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_ks_239_, v___x_240_, v_x_225_, v_x_226_);
lean_dec_ref(v_ks_239_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
size_t v_x_2351__boxed_246_; lean_object* v_res_247_; 
v_x_2351__boxed_246_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_res_247_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_242_, v_x_2351__boxed_246_, v_x_244_, v_x_245_);
lean_dec_ref(v_x_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object* v_e_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; lean_object* v_share_252_; lean_object* v___x_253_; uint64_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_251_ = lean_st_ref_get(v_a_249_);
v_share_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_ref(v_share_252_);
lean_dec(v___x_251_);
v___x_253_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_254_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_248_);
v___x_255_ = lean_uint64_to_usize(v___x_254_);
lean_inc_ref(v_e_248_);
v___x_256_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_252_, v___x_255_, v_e_248_, v___x_253_);
v___x_257_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_256_, v___x_253_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v_e_248_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; lean_object* v_share_260_; lean_object* v_maxFVar_261_; lean_object* v_proofInstInfo_262_; lean_object* v_inferType_263_; lean_object* v_getLevel_264_; lean_object* v_congrInfo_265_; lean_object* v_defEqI_266_; lean_object* v_extensions_267_; lean_object* v_issues_268_; uint8_t v_debug_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v___x_256_);
v___x_259_ = lean_st_ref_take(v_a_249_);
v_share_260_ = lean_ctor_get(v___x_259_, 0);
v_maxFVar_261_ = lean_ctor_get(v___x_259_, 1);
v_proofInstInfo_262_ = lean_ctor_get(v___x_259_, 2);
v_inferType_263_ = lean_ctor_get(v___x_259_, 3);
v_getLevel_264_ = lean_ctor_get(v___x_259_, 4);
v_congrInfo_265_ = lean_ctor_get(v___x_259_, 5);
v_defEqI_266_ = lean_ctor_get(v___x_259_, 6);
v_extensions_267_ = lean_ctor_get(v___x_259_, 7);
v_issues_268_ = lean_ctor_get(v___x_259_, 8);
v_debug_269_ = lean_ctor_get_uint8(v___x_259_, sizeof(void*)*9);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_280_ == 0)
{
v___x_271_ = v___x_259_;
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_issues_268_);
lean_inc(v_extensions_267_);
lean_inc(v_defEqI_266_);
lean_inc(v_congrInfo_265_);
lean_inc(v_getLevel_264_);
lean_inc(v_inferType_263_);
lean_inc(v_proofInstInfo_262_);
lean_inc(v_maxFVar_261_);
lean_inc(v_share_260_);
lean_dec(v___x_259_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_273_ = lean_box(0);
lean_inc_ref(v_e_248_);
v___x_274_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_260_, v_e_248_, v___x_273_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_maxFVar_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_proofInstInfo_262_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_inferType_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_getLevel_264_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_congrInfo_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v_defEqI_266_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_extensions_267_);
lean_ctor_set(v_reuseFailAlloc_279_, 8, v_issues_268_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*9, v_debug_269_);
v___x_276_ = v_reuseFailAlloc_279_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_st_ref_set(v_a_249_, v___x_276_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_e_248_);
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(lean_object* v_e_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_281_, v_a_282_);
lean_dec(v_a_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1(lean_object* v_e_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_285_, v_a_287_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___boxed(lean_object* v_e_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_Sym_Internal_Sym_share1(v_e_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(lean_object* v_00_u03b2_303_, lean_object* v_x_304_, size_t v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_304_, v_x_305_, v_x_306_, v_x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(lean_object* v_00_u03b2_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
size_t v_x_2441__boxed_314_; lean_object* v_res_315_; 
v_x_2441__boxed_314_ = lean_unbox_usize(v_x_311_);
lean_dec(v_x_311_);
v_res_315_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(v_00_u03b2_309_, v_x_310_, v_x_2441__boxed_314_, v_x_312_, v_x_313_);
lean_dec_ref(v_x_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(lean_object* v_00_u03b2_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_x_317_, v_x_318_, v_x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(lean_object* v_00_u03b2_321_, lean_object* v_keys_322_, lean_object* v_vals_323_, lean_object* v_heq_324_, lean_object* v_i_325_, lean_object* v_k_326_, lean_object* v_k_u2080_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_322_, v_i_325_, v_k_326_, v_k_u2080_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(lean_object* v_00_u03b2_329_, lean_object* v_keys_330_, lean_object* v_vals_331_, lean_object* v_heq_332_, lean_object* v_i_333_, lean_object* v_k_334_, lean_object* v_k_u2080_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_329_, v_keys_330_, v_vals_331_, v_heq_332_, v_i_333_, v_k_334_, v_k_u2080_335_);
lean_dec_ref(v_k_u2080_335_);
lean_dec_ref(v_vals_331_);
lean_dec_ref(v_keys_330_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(lean_object* v_00_u03b2_337_, lean_object* v_x_338_, size_t v_x_339_, size_t v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_338_, v_x_339_, v_x_340_, v_x_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
size_t v_x_2465__boxed_350_; size_t v_x_2466__boxed_351_; lean_object* v_res_352_; 
v_x_2465__boxed_350_ = lean_unbox_usize(v_x_346_);
lean_dec(v_x_346_);
v_x_2466__boxed_351_ = lean_unbox_usize(v_x_347_);
lean_dec(v_x_347_);
v_res_352_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_344_, v_x_345_, v_x_2465__boxed_350_, v_x_2466__boxed_351_, v_x_348_, v_x_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_353_, lean_object* v_n_354_, lean_object* v_k_355_, lean_object* v_v_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_354_, v_k_355_, v_v_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_358_, size_t v_depth_359_, lean_object* v_keys_360_, lean_object* v_vals_361_, lean_object* v_heq_362_, lean_object* v_i_363_, lean_object* v_entries_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_359_, v_keys_360_, v_vals_361_, v_i_363_, v_entries_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_366_, lean_object* v_depth_367_, lean_object* v_keys_368_, lean_object* v_vals_369_, lean_object* v_heq_370_, lean_object* v_i_371_, lean_object* v_entries_372_){
_start:
{
size_t v_depth_boxed_373_; lean_object* v_res_374_; 
v_depth_boxed_373_ = lean_unbox_usize(v_depth_367_);
lean_dec(v_depth_367_);
v_res_374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_366_, v_depth_boxed_373_, v_keys_368_, v_vals_369_, v_heq_370_, v_i_371_, v_entries_372_);
lean_dec_ref(v_vals_369_);
lean_dec_ref(v_keys_368_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_376_, v_x_377_, v_x_378_, v_x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_756__overap_391_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0, &l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0);
v___x_756__overap_391_ = lean_panic_fn_borrowed(v___x_390_, v_msg_382_);
lean_inc(v___y_388_);
lean_inc_ref(v___y_387_);
lean_inc(v___y_386_);
lean_inc_ref(v___y_385_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
v___x_392_ = lean_apply_7(v___x_756__overap_391_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, lean_box(0));
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v_msg_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_401_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_405_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2));
v___x_406_ = lean_unsigned_to_nat(2u);
v___x_407_ = lean_unsigned_to_nat(42u);
v___x_408_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1));
v___x_409_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_410_ = l_mkPanicMessageWithDecl(v___x_409_, v___x_408_, v___x_407_, v___x_406_, v___x_405_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object* v_e_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; lean_object* v_share_420_; lean_object* v___x_421_; uint64_t v___x_422_; size_t v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_419_ = lean_st_ref_get(v_a_413_);
v_share_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_share_420_);
lean_dec(v___x_419_);
v___x_421_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_422_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_411_);
v___x_423_ = lean_uint64_to_usize(v___x_422_);
lean_inc_ref(v_e_411_);
v___x_424_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_420_, v___x_423_, v_e_411_, v___x_421_);
v___x_425_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_424_, v_e_411_);
lean_dec_ref(v_e_411_);
lean_dec_ref(v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3, &l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once, _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3);
v___x_427_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(v___x_426_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(lean_object* v_e_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_e_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_438_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2(void){
_start:
{
lean_object* v___f_449_; lean_object* v___f_450_; lean_object* v___x_451_; 
v___f_449_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1));
v___f_450_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0));
v___x_451_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_450_, v___f_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(lean_object* v_k_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_455_; lean_object* v_share_456_; lean_object* v_maxFVar_457_; lean_object* v_proofInstInfo_458_; lean_object* v_inferType_459_; lean_object* v_getLevel_460_; lean_object* v_congrInfo_461_; lean_object* v_defEqI_462_; lean_object* v_extensions_463_; lean_object* v_issues_464_; uint8_t v_debug_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_500_; 
v___x_455_ = lean_st_ref_take(v_a_453_);
v_share_456_ = lean_ctor_get(v___x_455_, 0);
v_maxFVar_457_ = lean_ctor_get(v___x_455_, 1);
v_proofInstInfo_458_ = lean_ctor_get(v___x_455_, 2);
v_inferType_459_ = lean_ctor_get(v___x_455_, 3);
v_getLevel_460_ = lean_ctor_get(v___x_455_, 4);
v_congrInfo_461_ = lean_ctor_get(v___x_455_, 5);
v_defEqI_462_ = lean_ctor_get(v___x_455_, 6);
v_extensions_463_ = lean_ctor_get(v___x_455_, 7);
v_issues_464_ = lean_ctor_get(v___x_455_, 8);
v_debug_465_ = lean_ctor_get_uint8(v___x_455_, sizeof(void*)*9);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_500_ == 0)
{
v___x_467_ = v___x_455_;
v_isShared_468_ = v_isSharedCheck_500_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_issues_464_);
lean_inc(v_extensions_463_);
lean_inc(v_defEqI_462_);
lean_inc(v_congrInfo_461_);
lean_inc(v_getLevel_460_);
lean_inc(v_inferType_459_);
lean_inc(v_proofInstInfo_458_);
lean_inc(v_maxFVar_457_);
lean_inc(v_share_456_);
lean_dec(v___x_455_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_500_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_469_);
v___x_471_ = v___x_467_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_maxFVar_457_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_proofInstInfo_458_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_inferType_459_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_getLevel_460_);
lean_ctor_set(v_reuseFailAlloc_499_, 5, v_congrInfo_461_);
lean_ctor_set(v_reuseFailAlloc_499_, 6, v_defEqI_462_);
lean_ctor_set(v_reuseFailAlloc_499_, 7, v_extensions_463_);
lean_ctor_set(v_reuseFailAlloc_499_, 8, v_issues_464_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*9, v_debug_465_);
v___x_471_ = v_reuseFailAlloc_499_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v_debug_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_479_; lean_object* v_maxFVar_480_; lean_object* v_proofInstInfo_481_; lean_object* v_inferType_482_; lean_object* v_getLevel_483_; lean_object* v_congrInfo_484_; lean_object* v_defEqI_485_; lean_object* v_extensions_486_; lean_object* v_issues_487_; uint8_t v_debug_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
v___x_472_ = lean_st_ref_set(v_a_453_, v___x_471_);
v___x_473_ = lean_st_ref_get(v_a_453_);
v_debug_474_ = lean_ctor_get_uint8(v___x_473_, sizeof(void*)*9);
lean_dec(v___x_473_);
v___x_475_ = lean_box(v_debug_474_);
v___x_476_ = lean_apply_2(v_k_452_, v___x_475_, v_share_456_);
v_fst_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_fst_477_);
v_snd_478_ = lean_ctor_get(v___x_476_, 1);
lean_inc(v_snd_478_);
lean_dec_ref(v___x_476_);
v___x_479_ = lean_st_ref_take(v_a_453_);
v_maxFVar_480_ = lean_ctor_get(v___x_479_, 1);
v_proofInstInfo_481_ = lean_ctor_get(v___x_479_, 2);
v_inferType_482_ = lean_ctor_get(v___x_479_, 3);
v_getLevel_483_ = lean_ctor_get(v___x_479_, 4);
v_congrInfo_484_ = lean_ctor_get(v___x_479_, 5);
v_defEqI_485_ = lean_ctor_get(v___x_479_, 6);
v_extensions_486_ = lean_ctor_get(v___x_479_, 7);
v_issues_487_ = lean_ctor_get(v___x_479_, 8);
v_debug_488_ = lean_ctor_get_uint8(v___x_479_, sizeof(void*)*9);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_498_);
v___x_490_ = v___x_479_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_issues_487_);
lean_inc(v_extensions_486_);
lean_inc(v_defEqI_485_);
lean_inc(v_congrInfo_484_);
lean_inc(v_getLevel_483_);
lean_inc(v_inferType_482_);
lean_inc(v_proofInstInfo_481_);
lean_inc(v_maxFVar_480_);
lean_dec(v___x_479_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_snd_478_);
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_snd_478_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_maxFVar_480_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_proofInstInfo_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_inferType_482_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_getLevel_483_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_congrInfo_484_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_defEqI_485_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_extensions_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_issues_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_496_, sizeof(void*)*9, v_debug_488_);
v___x_493_ = v_reuseFailAlloc_496_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_st_ref_set(v_a_453_, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_fst_477_);
return v___x_495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(lean_object* v_k_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_501_, v_a_502_);
lean_dec(v_a_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM(lean_object* v_00_u03b1_505_, lean_object* v_k_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v___x_514_; lean_object* v_share_515_; lean_object* v_maxFVar_516_; lean_object* v_proofInstInfo_517_; lean_object* v_inferType_518_; lean_object* v_getLevel_519_; lean_object* v_congrInfo_520_; lean_object* v_defEqI_521_; lean_object* v_extensions_522_; lean_object* v_issues_523_; uint8_t v_debug_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_559_; 
v___x_514_ = lean_st_ref_take(v_a_508_);
v_share_515_ = lean_ctor_get(v___x_514_, 0);
v_maxFVar_516_ = lean_ctor_get(v___x_514_, 1);
v_proofInstInfo_517_ = lean_ctor_get(v___x_514_, 2);
v_inferType_518_ = lean_ctor_get(v___x_514_, 3);
v_getLevel_519_ = lean_ctor_get(v___x_514_, 4);
v_congrInfo_520_ = lean_ctor_get(v___x_514_, 5);
v_defEqI_521_ = lean_ctor_get(v___x_514_, 6);
v_extensions_522_ = lean_ctor_get(v___x_514_, 7);
v_issues_523_ = lean_ctor_get(v___x_514_, 8);
v_debug_524_ = lean_ctor_get_uint8(v___x_514_, sizeof(void*)*9);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_559_ == 0)
{
v___x_526_ = v___x_514_;
v_isShared_527_ = v_isSharedCheck_559_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_issues_523_);
lean_inc(v_extensions_522_);
lean_inc(v_defEqI_521_);
lean_inc(v_congrInfo_520_);
lean_inc(v_getLevel_519_);
lean_inc(v_inferType_518_);
lean_inc(v_proofInstInfo_517_);
lean_inc(v_maxFVar_516_);
lean_inc(v_share_515_);
lean_dec(v___x_514_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_559_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2, &l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once, _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_maxFVar_516_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_proofInstInfo_517_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_inferType_518_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_getLevel_519_);
lean_ctor_set(v_reuseFailAlloc_558_, 5, v_congrInfo_520_);
lean_ctor_set(v_reuseFailAlloc_558_, 6, v_defEqI_521_);
lean_ctor_set(v_reuseFailAlloc_558_, 7, v_extensions_522_);
lean_ctor_set(v_reuseFailAlloc_558_, 8, v_issues_523_);
lean_ctor_set_uint8(v_reuseFailAlloc_558_, sizeof(void*)*9, v_debug_524_);
v___x_530_ = v_reuseFailAlloc_558_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v_debug_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_538_; lean_object* v_maxFVar_539_; lean_object* v_proofInstInfo_540_; lean_object* v_inferType_541_; lean_object* v_getLevel_542_; lean_object* v_congrInfo_543_; lean_object* v_defEqI_544_; lean_object* v_extensions_545_; lean_object* v_issues_546_; uint8_t v_debug_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_556_; 
v___x_531_ = lean_st_ref_set(v_a_508_, v___x_530_);
v___x_532_ = lean_st_ref_get(v_a_508_);
v_debug_533_ = lean_ctor_get_uint8(v___x_532_, sizeof(void*)*9);
lean_dec(v___x_532_);
v___x_534_ = lean_box(v_debug_533_);
v___x_535_ = lean_apply_2(v_k_506_, v___x_534_, v_share_515_);
v_fst_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_fst_536_);
v_snd_537_ = lean_ctor_get(v___x_535_, 1);
lean_inc(v_snd_537_);
lean_dec_ref(v___x_535_);
v___x_538_ = lean_st_ref_take(v_a_508_);
v_maxFVar_539_ = lean_ctor_get(v___x_538_, 1);
v_proofInstInfo_540_ = lean_ctor_get(v___x_538_, 2);
v_inferType_541_ = lean_ctor_get(v___x_538_, 3);
v_getLevel_542_ = lean_ctor_get(v___x_538_, 4);
v_congrInfo_543_ = lean_ctor_get(v___x_538_, 5);
v_defEqI_544_ = lean_ctor_get(v___x_538_, 6);
v_extensions_545_ = lean_ctor_get(v___x_538_, 7);
v_issues_546_ = lean_ctor_get(v___x_538_, 8);
v_debug_547_ = lean_ctor_get_uint8(v___x_538_, sizeof(void*)*9);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___x_538_, 0);
lean_dec(v_unused_557_);
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_issues_546_);
lean_inc(v_extensions_545_);
lean_inc(v_defEqI_544_);
lean_inc(v_congrInfo_543_);
lean_inc(v_getLevel_542_);
lean_inc(v_inferType_541_);
lean_inc(v_proofInstInfo_540_);
lean_inc(v_maxFVar_539_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_556_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_snd_537_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_snd_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_maxFVar_539_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_proofInstInfo_540_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_inferType_541_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_getLevel_542_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v_congrInfo_543_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_defEqI_544_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v_extensions_545_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v_issues_546_);
lean_ctor_set_uint8(v_reuseFailAlloc_555_, sizeof(void*)*9, v_debug_547_);
v___x_552_ = v_reuseFailAlloc_555_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_st_ref_set(v_a_508_, v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v_fst_536_);
return v___x_554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(lean_object* v_00_u03b1_560_, lean_object* v_k_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_Sym_Internal_liftBuilderM(v_00_u03b1_560_, v_k_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object* v_e_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_572_; uint64_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_572_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
v___x_573_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_570_);
v___x_574_ = lean_uint64_to_usize(v___x_573_);
lean_inc_ref(v_e_570_);
lean_inc_ref(v_a_571_);
v___x_575_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_571_, v___x_574_, v_e_570_, v___x_572_);
v___x_576_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_575_, v___x_572_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec_ref(v_e_570_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v_a_571_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec_ref(v___x_575_);
v___x_578_ = lean_box(0);
lean_inc_ref(v_e_570_);
v___x_579_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_571_, v_e_570_, v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_e_570_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1(lean_object* v_e_581_, uint8_t v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_581_, v_a_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___boxed(lean_object* v_e_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
uint8_t v_a_boxed_588_; lean_object* v_res_589_; 
v_a_boxed_588_ = lean_unbox(v_a_586_);
v_res_589_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_585_, v_a_boxed_588_, v_a_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(lean_object* v_msg_597_, uint8_t v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___f_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___f_622_; lean_object* v___x_692__overap_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___f_600_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_601_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_602_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_603_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_604_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_605_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_606_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___f_600_);
lean_ctor_set(v___x_607_, 1, v___f_601_);
v___x_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___f_602_);
lean_ctor_set(v___x_608_, 2, v___f_603_);
lean_ctor_set(v___x_608_, 3, v___f_604_);
lean_ctor_set(v___x_608_, 4, v___f_605_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___f_606_);
lean_inc_ref(v___x_609_);
v___f_610_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_610_, 0, v___x_609_);
lean_inc_ref(v___x_609_);
v___f_611_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_611_, 0, v___x_609_);
lean_inc_ref(v___x_609_);
v___f_612_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_612_, 0, v___x_609_);
lean_inc_ref(v___x_609_);
v___f_613_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_613_, 0, v___x_609_);
lean_inc_ref(v___x_609_);
v___x_614_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_614_, 0, lean_box(0));
lean_closure_set(v___x_614_, 1, lean_box(0));
lean_closure_set(v___x_614_, 2, v___x_609_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___f_610_);
lean_inc_ref(v___x_609_);
v___x_616_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_616_, 0, lean_box(0));
lean_closure_set(v___x_616_, 1, lean_box(0));
lean_closure_set(v___x_616_, 2, v___x_609_);
v___x_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_ctor_set(v___x_617_, 2, v___f_611_);
lean_ctor_set(v___x_617_, 3, v___f_612_);
lean_ctor_set(v___x_617_, 4, v___f_613_);
v___x_618_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_618_, 0, lean_box(0));
lean_closure_set(v___x_618_, 1, lean_box(0));
lean_closure_set(v___x_618_, 2, v___x_609_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_box(0);
v___x_621_ = l_instInhabitedOfMonad___redArg(v___x_619_, v___x_620_);
v___f_622_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_622_, 0, v___x_621_);
v___x_692__overap_623_ = lean_panic_fn_borrowed(v___f_622_, v_msg_597_);
lean_dec_ref(v___f_622_);
v___x_624_ = lean_box(v___y_598_);
v___x_625_ = lean_apply_2(v___x_692__overap_623_, v___x_624_, v___y_599_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v___y_825__boxed_629_; lean_object* v_res_630_; 
v___y_825__boxed_629_ = lean_unbox(v___y_627_);
v_res_630_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v_msg_626_, v___y_825__boxed_629_, v___y_628_);
return v_res_630_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_631_, lean_object* v_i_632_, lean_object* v_k_633_){
_start:
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_array_get_size(v_keys_631_);
v___x_635_ = lean_nat_dec_lt(v_i_632_, v___x_634_);
if (v___x_635_ == 0)
{
lean_dec_ref(v_k_633_);
lean_dec(v_i_632_);
return v___x_635_;
}
else
{
lean_object* v_k_x27_636_; uint8_t v___x_637_; 
v_k_x27_636_ = lean_array_fget_borrowed(v_keys_631_, v_i_632_);
lean_inc(v_k_x27_636_);
lean_inc_ref(v_k_633_);
v___x_637_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_633_, v_k_x27_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_add(v_i_632_, v___x_638_);
lean_dec(v_i_632_);
v_i_632_ = v___x_639_;
goto _start;
}
else
{
lean_dec_ref(v_k_633_);
lean_dec(v_i_632_);
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_641_, lean_object* v_i_642_, lean_object* v_k_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_641_, v_i_642_, v_k_643_);
lean_dec_ref(v_keys_641_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(lean_object* v_x_646_, size_t v_x_647_, lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v_es_649_; lean_object* v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; lean_object* v_j_654_; lean_object* v___x_655_; 
v_es_649_ = lean_ctor_get(v_x_646_, 0);
lean_inc_ref(v_es_649_);
lean_dec_ref(v_x_646_);
v___x_650_ = lean_box(2);
v___x_651_ = ((size_t)5ULL);
v___x_652_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
v___x_653_ = lean_usize_land(v_x_647_, v___x_652_);
v_j_654_ = lean_usize_to_nat(v___x_653_);
v___x_655_ = lean_array_get(v___x_650_, v_es_649_, v_j_654_);
lean_dec(v_j_654_);
lean_dec_ref(v_es_649_);
switch(lean_obj_tag(v___x_655_))
{
case 0:
{
lean_object* v_key_656_; uint8_t v___x_657_; 
v_key_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_key_656_);
lean_dec_ref(v___x_655_);
v___x_657_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_648_, v_key_656_);
return v___x_657_;
}
case 1:
{
lean_object* v_node_658_; size_t v___x_659_; 
v_node_658_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_node_658_);
lean_dec_ref(v___x_655_);
v___x_659_ = lean_usize_shift_right(v_x_647_, v___x_651_);
v_x_646_ = v_node_658_;
v_x_647_ = v___x_659_;
goto _start;
}
default: 
{
uint8_t v___x_661_; 
lean_dec_ref(v_x_648_);
v___x_661_ = 0;
return v___x_661_;
}
}
}
else
{
lean_object* v_ks_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_ks_662_ = lean_ctor_get(v_x_646_, 0);
lean_inc_ref(v_ks_662_);
lean_dec_ref(v_x_646_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_662_, v___x_663_, v_x_648_);
lean_dec_ref(v_ks_662_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
size_t v_x_907__boxed_668_; uint8_t v_res_669_; lean_object* v_r_670_; 
v_x_907__boxed_668_ = lean_unbox_usize(v_x_666_);
lean_dec(v_x_666_);
v_res_669_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_665_, v_x_907__boxed_668_, v_x_667_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint64_t v___x_673_; size_t v___x_674_; uint8_t v___x_675_; 
v___x_673_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_672_);
v___x_674_ = lean_uint64_to_usize(v___x_673_);
v___x_675_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_671_, v___x_674_, v_x_672_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_676_, v_x_677_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_682_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1));
v___x_683_ = lean_unsigned_to_nat(2u);
v___x_684_ = lean_unsigned_to_nat(74u);
v___x_685_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0));
v___x_686_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_687_ = l_mkPanicMessageWithDecl(v___x_686_, v___x_685_, v___x_684_, v___x_683_, v___x_682_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object* v_e_688_, uint8_t v_a_689_, lean_object* v_a_690_){
_start:
{
uint8_t v___x_691_; 
lean_inc_ref(v_a_690_);
v___x_691_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_690_, v_e_688_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2, &l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once, _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2);
v___x_693_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(v___x_692_, v_a_689_, v_a_690_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_box(0);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_690_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
uint8_t v_a_boxed_699_; lean_object* v_res_700_; 
v_a_boxed_699_ = lean_unbox(v_a_697_);
v_res_700_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_696_, v_a_boxed_699_, v_a_698_);
return v_res_700_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(lean_object* v_00_u03b2_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_702_, v_x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(lean_object* v_00_u03b2_705_, lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_705_, v_x_706_, v_x_707_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(lean_object* v_00_u03b2_710_, lean_object* v_x_711_, size_t v_x_712_, lean_object* v_x_713_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_711_, v_x_712_, v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
size_t v_x_1008__boxed_719_; uint8_t v_res_720_; lean_object* v_r_721_; 
v_x_1008__boxed_719_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_res_720_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_715_, v_x_716_, v_x_1008__boxed_719_, v_x_718_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_722_, lean_object* v_keys_723_, lean_object* v_vals_724_, lean_object* v_heq_725_, lean_object* v_i_726_, lean_object* v_k_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_723_, v_i_726_, v_k_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_729_, lean_object* v_keys_730_, lean_object* v_vals_731_, lean_object* v_heq_732_, lean_object* v_i_733_, lean_object* v_k_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_729_, v_keys_730_, v_vals_731_, v_heq_732_, v_i_733_, v_k_734_);
lean_dec_ref(v_vals_731_);
lean_dec_ref(v_keys_730_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM(void){
_start:
{
lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___f_739_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0));
v___f_740_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1));
v___f_741_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2));
v___f_742_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3));
v___f_743_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4));
v___f_744_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5));
v___f_745_ = ((lean_object*)(l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6));
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___f_739_);
lean_ctor_set(v___x_746_, 1, v___f_740_);
v___x_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___f_741_);
lean_ctor_set(v___x_747_, 2, v___f_742_);
lean_ctor_set(v___x_747_, 3, v___f_743_);
lean_ctor_set(v___x_747_, 4, v___f_744_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v___f_745_);
lean_inc_ref(v___x_748_);
v___f_749_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_749_, 0, v___x_748_);
lean_inc_ref(v___x_748_);
v___f_750_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_750_, 0, v___x_748_);
lean_inc_ref(v___x_748_);
v___f_751_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_751_, 0, v___x_748_);
lean_inc_ref(v___x_748_);
v___f_752_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_752_, 0, v___x_748_);
lean_inc_ref(v___x_748_);
v___x_753_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_753_, 0, lean_box(0));
lean_closure_set(v___x_753_, 1, lean_box(0));
lean_closure_set(v___x_753_, 2, v___x_748_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___f_749_);
lean_inc_ref(v___x_748_);
v___x_755_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_755_, 0, lean_box(0));
lean_closure_set(v___x_755_, 1, lean_box(0));
lean_closure_set(v___x_755_, 2, v___x_748_);
v___x_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
lean_ctor_set(v___x_756_, 2, v___f_750_);
lean_ctor_set(v___x_756_, 3, v___f_751_);
lean_ctor_set(v___x_756_, 4, v___f_752_);
v___x_757_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_757_, 0, lean_box(0));
lean_closure_set(v___x_757_, 1, lean_box(0));
lean_closure_set(v___x_757_, 2, v___x_748_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0));
v___x_760_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1));
v___x_761_ = lean_alloc_closure((void*)(l_ReaderT_read___boxed), 4, 3);
lean_closure_set(v___x_761_, 0, lean_box(0));
lean_closure_set(v___x_761_, 1, lean_box(0));
lean_closure_set(v___x_761_, 2, v___x_758_);
v___x_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_762_, 0, v___x_759_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
lean_ctor_set(v___x_762_, 2, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS___redArg(lean_object* v_inst_763_, lean_object* v_l_764_){
_start:
{
lean_object* v_share1_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_share1_765_ = lean_ctor_get(v_inst_763_, 0);
lean_inc(v_share1_765_);
lean_dec_ref(v_inst_763_);
v___x_766_ = l_Lean_Expr_lit___override(v_l_764_);
v___x_767_ = lean_apply_1(v_share1_765_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLitS(lean_object* v_m_768_, lean_object* v_inst_769_, lean_object* v_l_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_769_, v_l_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___redArg(lean_object* v_inst_772_, lean_object* v_declName_773_, lean_object* v_us_774_){
_start:
{
lean_object* v_share1_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_share1_775_ = lean_ctor_get(v_inst_772_, 0);
lean_inc(v_share1_775_);
lean_dec_ref(v_inst_772_);
v___x_776_ = l_Lean_Expr_const___override(v_declName_773_, v_us_774_);
v___x_777_ = lean_apply_1(v_share1_775_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS(lean_object* v_m_778_, lean_object* v_inst_779_, lean_object* v_declName_780_, lean_object* v_us_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_779_, v_declName_780_, v_us_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object* v_inst_783_, lean_object* v_idx_784_){
_start:
{
lean_object* v_share1_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_share1_785_ = lean_ctor_get(v_inst_783_, 0);
lean_inc(v_share1_785_);
lean_dec_ref(v_inst_783_);
v___x_786_ = l_Lean_Expr_bvar___override(v_idx_784_);
v___x_787_ = lean_apply_1(v_share1_785_, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS(lean_object* v_m_788_, lean_object* v_inst_789_, lean_object* v_idx_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_789_, v_idx_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___redArg(lean_object* v_inst_792_, lean_object* v_u_793_){
_start:
{
lean_object* v_share1_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_share1_794_ = lean_ctor_get(v_inst_792_, 0);
lean_inc(v_share1_794_);
lean_dec_ref(v_inst_792_);
v___x_795_ = l_Lean_Expr_sort___override(v_u_793_);
v___x_796_ = lean_apply_1(v_share1_794_, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS(lean_object* v_m_797_, lean_object* v_inst_798_, lean_object* v_u_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_798_, v_u_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___redArg(lean_object* v_inst_801_, lean_object* v_fvarId_802_){
_start:
{
lean_object* v_share1_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_share1_803_ = lean_ctor_get(v_inst_801_, 0);
lean_inc(v_share1_803_);
lean_dec_ref(v_inst_801_);
v___x_804_ = l_Lean_Expr_fvar___override(v_fvarId_802_);
v___x_805_ = lean_apply_1(v_share1_803_, v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS(lean_object* v_m_806_, lean_object* v_inst_807_, lean_object* v_fvarId_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_807_, v_fvarId_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS___redArg(lean_object* v_inst_810_, lean_object* v_mvarId_811_){
_start:
{
lean_object* v_share1_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_share1_812_ = lean_ctor_get(v_inst_810_, 0);
lean_inc(v_share1_812_);
lean_dec_ref(v_inst_810_);
v___x_813_ = l_Lean_Expr_mvar___override(v_mvarId_811_);
v___x_814_ = lean_apply_1(v_share1_812_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMVarS(lean_object* v_m_815_, lean_object* v_inst_816_, lean_object* v_mvarId_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_816_, v_mvarId_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(lean_object* v_d_819_, lean_object* v_e_820_, lean_object* v_share1_821_, lean_object* v_____r_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = l_Lean_Expr_mdata___override(v_d_819_, v_e_820_);
v___x_824_ = lean_apply_1(v_share1_821_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(lean_object* v___f_825_, lean_object* v_____r_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lean_apply_1(v___f_825_, v_____r_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(lean_object* v___f_828_, lean_object* v_assertShared_829_, lean_object* v_e_830_, lean_object* v_toBind_831_, lean_object* v___f_832_, uint8_t v_____do__lift_833_){
_start:
{
if (v_____do__lift_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v___f_832_);
lean_dec(v_toBind_831_);
lean_dec_ref(v_e_830_);
lean_dec(v_assertShared_829_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_apply_1(v___f_828_, v___x_834_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v___f_828_);
v___x_836_ = lean_apply_1(v_assertShared_829_, v_e_830_);
v___x_837_ = lean_apply_4(v_toBind_831_, lean_box(0), lean_box(0), v___x_836_, v___f_832_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(lean_object* v___f_838_, lean_object* v_assertShared_839_, lean_object* v_e_840_, lean_object* v_toBind_841_, lean_object* v___f_842_, lean_object* v_____do__lift_843_){
_start:
{
uint8_t v_____do__lift_85__boxed_844_; lean_object* v_res_845_; 
v_____do__lift_85__boxed_844_ = lean_unbox(v_____do__lift_843_);
v_res_845_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(v___f_838_, v_assertShared_839_, v_e_840_, v_toBind_841_, v___f_842_, v_____do__lift_85__boxed_844_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___redArg(lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_d_848_, lean_object* v_e_849_){
_start:
{
lean_object* v_toBind_850_; lean_object* v_share1_851_; lean_object* v_assertShared_852_; lean_object* v_isDebugEnabled_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___x_857_; 
v_toBind_850_ = lean_ctor_get(v_inst_847_, 1);
lean_inc(v_toBind_850_);
lean_dec_ref(v_inst_847_);
v_share1_851_ = lean_ctor_get(v_inst_846_, 0);
lean_inc(v_share1_851_);
v_assertShared_852_ = lean_ctor_get(v_inst_846_, 1);
lean_inc(v_assertShared_852_);
v_isDebugEnabled_853_ = lean_ctor_get(v_inst_846_, 2);
lean_inc(v_isDebugEnabled_853_);
lean_dec_ref(v_inst_846_);
lean_inc_ref(v_e_849_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_854_, 0, v_d_848_);
lean_closure_set(v___f_854_, 1, v_e_849_);
lean_closure_set(v___f_854_, 2, v_share1_851_);
lean_inc_ref(v___f_854_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_855_, 0, v___f_854_);
lean_inc(v_toBind_850_);
v___f_856_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_856_, 0, v___f_854_);
lean_closure_set(v___f_856_, 1, v_assertShared_852_);
lean_closure_set(v___f_856_, 2, v_e_849_);
lean_closure_set(v___f_856_, 3, v_toBind_850_);
lean_closure_set(v___f_856_, 4, v___f_855_);
v___x_857_ = lean_apply_4(v_toBind_850_, lean_box(0), lean_box(0), v_isDebugEnabled_853_, v___f_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS(lean_object* v_m_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_d_861_, lean_object* v_e_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_859_, v_inst_860_, v_d_861_, v_e_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(lean_object* v_structName_864_, lean_object* v_idx_865_, lean_object* v_struct_866_, lean_object* v_share1_867_, lean_object* v_____r_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = l_Lean_Expr_proj___override(v_structName_864_, v_idx_865_, v_struct_866_);
v___x_870_ = lean_apply_1(v_share1_867_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(lean_object* v___f_871_, lean_object* v_assertShared_872_, lean_object* v_struct_873_, lean_object* v_toBind_874_, lean_object* v___f_875_, uint8_t v_____do__lift_876_){
_start:
{
if (v_____do__lift_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec(v___f_875_);
lean_dec(v_toBind_874_);
lean_dec_ref(v_struct_873_);
lean_dec(v_assertShared_872_);
v___x_877_ = lean_box(0);
v___x_878_ = lean_apply_1(v___f_871_, v___x_877_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec(v___f_871_);
v___x_879_ = lean_apply_1(v_assertShared_872_, v_struct_873_);
v___x_880_ = lean_apply_4(v_toBind_874_, lean_box(0), lean_box(0), v___x_879_, v___f_875_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(lean_object* v___f_881_, lean_object* v_assertShared_882_, lean_object* v_struct_883_, lean_object* v_toBind_884_, lean_object* v___f_885_, lean_object* v_____do__lift_886_){
_start:
{
uint8_t v_____do__lift_79__boxed_887_; lean_object* v_res_888_; 
v_____do__lift_79__boxed_887_ = lean_unbox(v_____do__lift_886_);
v_res_888_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(v___f_881_, v_assertShared_882_, v_struct_883_, v_toBind_884_, v___f_885_, v_____do__lift_79__boxed_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___redArg(lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_structName_891_, lean_object* v_idx_892_, lean_object* v_struct_893_){
_start:
{
lean_object* v_toBind_894_; lean_object* v_share1_895_; lean_object* v_assertShared_896_; lean_object* v_isDebugEnabled_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___f_900_; lean_object* v___x_901_; 
v_toBind_894_ = lean_ctor_get(v_inst_890_, 1);
lean_inc(v_toBind_894_);
lean_dec_ref(v_inst_890_);
v_share1_895_ = lean_ctor_get(v_inst_889_, 0);
lean_inc(v_share1_895_);
v_assertShared_896_ = lean_ctor_get(v_inst_889_, 1);
lean_inc(v_assertShared_896_);
v_isDebugEnabled_897_ = lean_ctor_get(v_inst_889_, 2);
lean_inc(v_isDebugEnabled_897_);
lean_dec_ref(v_inst_889_);
lean_inc_ref(v_struct_893_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0), 5, 4);
lean_closure_set(v___f_898_, 0, v_structName_891_);
lean_closure_set(v___f_898_, 1, v_idx_892_);
lean_closure_set(v___f_898_, 2, v_struct_893_);
lean_closure_set(v___f_898_, 3, v_share1_895_);
lean_inc_ref(v___f_898_);
v___f_899_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_899_, 0, v___f_898_);
lean_inc(v_toBind_894_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_900_, 0, v___f_898_);
lean_closure_set(v___f_900_, 1, v_assertShared_896_);
lean_closure_set(v___f_900_, 2, v_struct_893_);
lean_closure_set(v___f_900_, 3, v_toBind_894_);
lean_closure_set(v___f_900_, 4, v___f_899_);
v___x_901_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v_isDebugEnabled_897_, v___f_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS(lean_object* v_m_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_structName_905_, lean_object* v_idx_906_, lean_object* v_struct_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_903_, v_inst_904_, v_structName_905_, v_idx_906_, v_struct_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(lean_object* v_f_909_, lean_object* v_a_910_, lean_object* v_share1_911_, lean_object* v_____r_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = l_Lean_Expr_app___override(v_f_909_, v_a_910_);
v___x_914_ = lean_apply_1(v_share1_911_, v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(lean_object* v_assertShared_915_, lean_object* v_a_916_, lean_object* v_toBind_917_, lean_object* v___f_918_, lean_object* v_____r_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_apply_1(v_assertShared_915_, v_a_916_);
v___x_921_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v___x_920_, v___f_918_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(lean_object* v___f_922_, lean_object* v_assertShared_923_, lean_object* v_a_924_, lean_object* v_toBind_925_, lean_object* v___f_926_, lean_object* v_f_927_, uint8_t v_____do__lift_928_){
_start:
{
if (v_____do__lift_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec_ref(v_f_927_);
lean_dec(v___f_926_);
lean_dec(v_toBind_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_assertShared_923_);
v___x_929_ = lean_box(0);
v___x_930_ = lean_apply_1(v___f_922_, v___x_929_);
return v___x_930_;
}
else
{
lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec(v___f_922_);
lean_inc(v_toBind_925_);
lean_inc(v_assertShared_923_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_931_, 0, v_assertShared_923_);
lean_closure_set(v___f_931_, 1, v_a_924_);
lean_closure_set(v___f_931_, 2, v_toBind_925_);
lean_closure_set(v___f_931_, 3, v___f_926_);
v___x_932_ = lean_apply_1(v_assertShared_923_, v_f_927_);
v___x_933_ = lean_apply_4(v_toBind_925_, lean_box(0), lean_box(0), v___x_932_, v___f_931_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(lean_object* v___f_934_, lean_object* v_assertShared_935_, lean_object* v_a_936_, lean_object* v_toBind_937_, lean_object* v___f_938_, lean_object* v_f_939_, lean_object* v_____do__lift_940_){
_start:
{
uint8_t v_____do__lift_104__boxed_941_; lean_object* v_res_942_; 
v_____do__lift_104__boxed_941_ = lean_unbox(v_____do__lift_940_);
v_res_942_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(v___f_934_, v_assertShared_935_, v_a_936_, v_toBind_937_, v___f_938_, v_f_939_, v_____do__lift_104__boxed_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___redArg(lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_f_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_toBind_947_; lean_object* v_share1_948_; lean_object* v_assertShared_949_; lean_object* v_isDebugEnabled_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___f_953_; lean_object* v___x_954_; 
v_toBind_947_ = lean_ctor_get(v_inst_944_, 1);
lean_inc(v_toBind_947_);
lean_dec_ref(v_inst_944_);
v_share1_948_ = lean_ctor_get(v_inst_943_, 0);
lean_inc(v_share1_948_);
v_assertShared_949_ = lean_ctor_get(v_inst_943_, 1);
lean_inc(v_assertShared_949_);
v_isDebugEnabled_950_ = lean_ctor_get(v_inst_943_, 2);
lean_inc(v_isDebugEnabled_950_);
lean_dec_ref(v_inst_943_);
lean_inc_ref(v_a_946_);
lean_inc_ref(v_f_945_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0), 4, 3);
lean_closure_set(v___f_951_, 0, v_f_945_);
lean_closure_set(v___f_951_, 1, v_a_946_);
lean_closure_set(v___f_951_, 2, v_share1_948_);
lean_inc_ref(v___f_951_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_952_, 0, v___f_951_);
lean_inc(v_toBind_947_);
v___f_953_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_953_, 0, v___f_951_);
lean_closure_set(v___f_953_, 1, v_assertShared_949_);
lean_closure_set(v___f_953_, 2, v_a_946_);
lean_closure_set(v___f_953_, 3, v_toBind_947_);
lean_closure_set(v___f_953_, 4, v___f_952_);
lean_closure_set(v___f_953_, 5, v_f_945_);
v___x_954_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v_isDebugEnabled_950_, v___f_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS(lean_object* v_m_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_f_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_956_, v_inst_957_, v_f_958_, v_a_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(lean_object* v_x_961_, lean_object* v_t_962_, lean_object* v_b_963_, uint8_t v_bi_964_, lean_object* v_share1_965_, lean_object* v_____r_966_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = l_Lean_Expr_lam___override(v_x_961_, v_t_962_, v_b_963_, v_bi_964_);
v___x_968_ = lean_apply_1(v_share1_965_, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(lean_object* v_x_969_, lean_object* v_t_970_, lean_object* v_b_971_, lean_object* v_bi_972_, lean_object* v_share1_973_, lean_object* v_____r_974_){
_start:
{
uint8_t v_bi_boxed_975_; lean_object* v_res_976_; 
v_bi_boxed_975_ = lean_unbox(v_bi_972_);
v_res_976_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(v_x_969_, v_t_970_, v_b_971_, v_bi_boxed_975_, v_share1_973_, v_____r_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(lean_object* v_assertShared_977_, lean_object* v_b_978_, lean_object* v_toBind_979_, lean_object* v___f_980_, lean_object* v_____r_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_apply_1(v_assertShared_977_, v_b_978_);
v___x_983_ = lean_apply_4(v_toBind_979_, lean_box(0), lean_box(0), v___x_982_, v___f_980_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(lean_object* v___f_984_, lean_object* v_assertShared_985_, lean_object* v_b_986_, lean_object* v_toBind_987_, lean_object* v___f_988_, lean_object* v_t_989_, uint8_t v_____do__lift_990_){
_start:
{
if (v_____do__lift_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec_ref(v_t_989_);
lean_dec(v___f_988_);
lean_dec(v_toBind_987_);
lean_dec_ref(v_b_986_);
lean_dec(v_assertShared_985_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_apply_1(v___f_984_, v___x_991_);
return v___x_992_;
}
else
{
lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec(v___f_984_);
lean_inc(v_toBind_987_);
lean_inc(v_assertShared_985_);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_993_, 0, v_assertShared_985_);
lean_closure_set(v___f_993_, 1, v_b_986_);
lean_closure_set(v___f_993_, 2, v_toBind_987_);
lean_closure_set(v___f_993_, 3, v___f_988_);
v___x_994_ = lean_apply_1(v_assertShared_985_, v_t_989_);
v___x_995_ = lean_apply_4(v_toBind_987_, lean_box(0), lean_box(0), v___x_994_, v___f_993_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(lean_object* v___f_996_, lean_object* v_assertShared_997_, lean_object* v_b_998_, lean_object* v_toBind_999_, lean_object* v___f_1000_, lean_object* v_t_1001_, lean_object* v_____do__lift_1002_){
_start:
{
uint8_t v_____do__lift_105__boxed_1003_; lean_object* v_res_1004_; 
v_____do__lift_105__boxed_1003_ = lean_unbox(v_____do__lift_1002_);
v_res_1004_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(v___f_996_, v_assertShared_997_, v_b_998_, v_toBind_999_, v___f_1000_, v_t_1001_, v_____do__lift_105__boxed_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_x_1007_, uint8_t v_bi_1008_, lean_object* v_t_1009_, lean_object* v_b_1010_){
_start:
{
lean_object* v_toBind_1011_; lean_object* v_share1_1012_; lean_object* v_assertShared_1013_; lean_object* v_isDebugEnabled_1014_; lean_object* v___x_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; 
v_toBind_1011_ = lean_ctor_get(v_inst_1006_, 1);
lean_inc(v_toBind_1011_);
lean_dec_ref(v_inst_1006_);
v_share1_1012_ = lean_ctor_get(v_inst_1005_, 0);
lean_inc(v_share1_1012_);
v_assertShared_1013_ = lean_ctor_get(v_inst_1005_, 1);
lean_inc(v_assertShared_1013_);
v_isDebugEnabled_1014_ = lean_ctor_get(v_inst_1005_, 2);
lean_inc(v_isDebugEnabled_1014_);
lean_dec_ref(v_inst_1005_);
v___x_1015_ = lean_box(v_bi_1008_);
lean_inc_ref(v_b_1010_);
lean_inc_ref(v_t_1009_);
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1016_, 0, v_x_1007_);
lean_closure_set(v___f_1016_, 1, v_t_1009_);
lean_closure_set(v___f_1016_, 2, v_b_1010_);
lean_closure_set(v___f_1016_, 3, v___x_1015_);
lean_closure_set(v___f_1016_, 4, v_share1_1012_);
lean_inc_ref(v___f_1016_);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1017_, 0, v___f_1016_);
lean_inc(v_toBind_1011_);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1018_, 0, v___f_1016_);
lean_closure_set(v___f_1018_, 1, v_assertShared_1013_);
lean_closure_set(v___f_1018_, 2, v_b_1010_);
lean_closure_set(v___f_1018_, 3, v_toBind_1011_);
lean_closure_set(v___f_1018_, 4, v___f_1017_);
lean_closure_set(v___f_1018_, 5, v_t_1009_);
v___x_1019_ = lean_apply_4(v_toBind_1011_, lean_box(0), lean_box(0), v_isDebugEnabled_1014_, v___f_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_x_1022_, lean_object* v_bi_1023_, lean_object* v_t_1024_, lean_object* v_b_1025_){
_start:
{
uint8_t v_bi_boxed_1026_; lean_object* v_res_1027_; 
v_bi_boxed_1026_ = lean_unbox(v_bi_1023_);
v_res_1027_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1020_, v_inst_1021_, v_x_1022_, v_bi_boxed_1026_, v_t_1024_, v_b_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS(lean_object* v_m_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_x_1031_, uint8_t v_bi_1032_, lean_object* v_t_1033_, lean_object* v_b_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1029_, v_inst_1030_, v_x_1031_, v_bi_1032_, v_t_1033_, v_b_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(lean_object* v_m_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_x_1039_, lean_object* v_bi_1040_, lean_object* v_t_1041_, lean_object* v_b_1042_){
_start:
{
uint8_t v_bi_boxed_1043_; lean_object* v_res_1044_; 
v_bi_boxed_1043_ = lean_unbox(v_bi_1040_);
v_res_1044_ = l_Lean_Meta_Sym_Internal_mkLambdaS(v_m_1036_, v_inst_1037_, v_inst_1038_, v_x_1039_, v_bi_boxed_1043_, v_t_1041_, v_b_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(lean_object* v_x_1045_, lean_object* v_t_1046_, lean_object* v_b_1047_, uint8_t v_bi_1048_, lean_object* v_share1_1049_, lean_object* v_____r_1050_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = l_Lean_Expr_forallE___override(v_x_1045_, v_t_1046_, v_b_1047_, v_bi_1048_);
v___x_1052_ = lean_apply_1(v_share1_1049_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(lean_object* v_x_1053_, lean_object* v_t_1054_, lean_object* v_b_1055_, lean_object* v_bi_1056_, lean_object* v_share1_1057_, lean_object* v_____r_1058_){
_start:
{
uint8_t v_bi_boxed_1059_; lean_object* v_res_1060_; 
v_bi_boxed_1059_ = lean_unbox(v_bi_1056_);
v_res_1060_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(v_x_1053_, v_t_1054_, v_b_1055_, v_bi_boxed_1059_, v_share1_1057_, v_____r_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg(lean_object* v_inst_1061_, lean_object* v_inst_1062_, lean_object* v_x_1063_, uint8_t v_bi_1064_, lean_object* v_t_1065_, lean_object* v_b_1066_){
_start:
{
lean_object* v_toBind_1067_; lean_object* v_share1_1068_; lean_object* v_assertShared_1069_; lean_object* v_isDebugEnabled_1070_; lean_object* v___x_1071_; lean_object* v___f_1072_; lean_object* v___f_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; 
v_toBind_1067_ = lean_ctor_get(v_inst_1062_, 1);
lean_inc(v_toBind_1067_);
lean_dec_ref(v_inst_1062_);
v_share1_1068_ = lean_ctor_get(v_inst_1061_, 0);
lean_inc(v_share1_1068_);
v_assertShared_1069_ = lean_ctor_get(v_inst_1061_, 1);
lean_inc(v_assertShared_1069_);
v_isDebugEnabled_1070_ = lean_ctor_get(v_inst_1061_, 2);
lean_inc(v_isDebugEnabled_1070_);
lean_dec_ref(v_inst_1061_);
v___x_1071_ = lean_box(v_bi_1064_);
lean_inc_ref(v_b_1066_);
lean_inc_ref(v_t_1065_);
v___f_1072_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1072_, 0, v_x_1063_);
lean_closure_set(v___f_1072_, 1, v_t_1065_);
lean_closure_set(v___f_1072_, 2, v_b_1066_);
lean_closure_set(v___f_1072_, 3, v___x_1071_);
lean_closure_set(v___f_1072_, 4, v_share1_1068_);
lean_inc_ref(v___f_1072_);
v___f_1073_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1073_, 0, v___f_1072_);
lean_inc(v_toBind_1067_);
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_1074_, 0, v___f_1072_);
lean_closure_set(v___f_1074_, 1, v_assertShared_1069_);
lean_closure_set(v___f_1074_, 2, v_b_1066_);
lean_closure_set(v___f_1074_, 3, v_toBind_1067_);
lean_closure_set(v___f_1074_, 4, v___f_1073_);
lean_closure_set(v___f_1074_, 5, v_t_1065_);
v___x_1075_ = lean_apply_4(v_toBind_1067_, lean_box(0), lean_box(0), v_isDebugEnabled_1070_, v___f_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_x_1078_, lean_object* v_bi_1079_, lean_object* v_t_1080_, lean_object* v_b_1081_){
_start:
{
uint8_t v_bi_boxed_1082_; lean_object* v_res_1083_; 
v_bi_boxed_1082_ = lean_unbox(v_bi_1079_);
v_res_1083_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1076_, v_inst_1077_, v_x_1078_, v_bi_boxed_1082_, v_t_1080_, v_b_1081_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS(lean_object* v_m_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_x_1087_, uint8_t v_bi_1088_, lean_object* v_t_1089_, lean_object* v_b_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1085_, v_inst_1086_, v_x_1087_, v_bi_1088_, v_t_1089_, v_b_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___boxed(lean_object* v_m_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_x_1095_, lean_object* v_bi_1096_, lean_object* v_t_1097_, lean_object* v_b_1098_){
_start:
{
uint8_t v_bi_boxed_1099_; lean_object* v_res_1100_; 
v_bi_boxed_1099_ = lean_unbox(v_bi_1096_);
v_res_1100_ = l_Lean_Meta_Sym_Internal_mkForallS(v_m_1092_, v_inst_1093_, v_inst_1094_, v_x_1095_, v_bi_boxed_1099_, v_t_1097_, v_b_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(lean_object* v_x_1101_, lean_object* v_t_1102_, lean_object* v_v_1103_, lean_object* v_b_1104_, uint8_t v_nondep_1105_, lean_object* v_share1_1106_, lean_object* v_____r_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = l_Lean_Expr_letE___override(v_x_1101_, v_t_1102_, v_v_1103_, v_b_1104_, v_nondep_1105_);
v___x_1109_ = lean_apply_1(v_share1_1106_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(lean_object* v_x_1110_, lean_object* v_t_1111_, lean_object* v_v_1112_, lean_object* v_b_1113_, lean_object* v_nondep_1114_, lean_object* v_share1_1115_, lean_object* v_____r_1116_){
_start:
{
uint8_t v_nondep_boxed_1117_; lean_object* v_res_1118_; 
v_nondep_boxed_1117_ = lean_unbox(v_nondep_1114_);
v_res_1118_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(v_x_1110_, v_t_1111_, v_v_1112_, v_b_1113_, v_nondep_boxed_1117_, v_share1_1115_, v_____r_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(lean_object* v_assertShared_1119_, lean_object* v_v_1120_, lean_object* v_toBind_1121_, lean_object* v___f_1122_, lean_object* v_____r_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_apply_1(v_assertShared_1119_, v_v_1120_);
v___x_1125_ = lean_apply_4(v_toBind_1121_, lean_box(0), lean_box(0), v___x_1124_, v___f_1122_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(lean_object* v___f_1126_, lean_object* v_assertShared_1127_, lean_object* v_b_1128_, lean_object* v_toBind_1129_, lean_object* v___f_1130_, lean_object* v_v_1131_, lean_object* v_t_1132_, uint8_t v_____do__lift_1133_){
_start:
{
if (v_____do__lift_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref(v_t_1132_);
lean_dec_ref(v_v_1131_);
lean_dec(v___f_1130_);
lean_dec(v_toBind_1129_);
lean_dec_ref(v_b_1128_);
lean_dec(v_assertShared_1127_);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_apply_1(v___f_1126_, v___x_1134_);
return v___x_1135_;
}
else
{
lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v___f_1126_);
lean_inc(v_toBind_1129_);
lean_inc(v_assertShared_1127_);
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2), 5, 4);
lean_closure_set(v___f_1136_, 0, v_assertShared_1127_);
lean_closure_set(v___f_1136_, 1, v_b_1128_);
lean_closure_set(v___f_1136_, 2, v_toBind_1129_);
lean_closure_set(v___f_1136_, 3, v___f_1130_);
lean_inc(v_toBind_1129_);
lean_inc(v_assertShared_1127_);
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3), 5, 4);
lean_closure_set(v___f_1137_, 0, v_assertShared_1127_);
lean_closure_set(v___f_1137_, 1, v_v_1131_);
lean_closure_set(v___f_1137_, 2, v_toBind_1129_);
lean_closure_set(v___f_1137_, 3, v___f_1136_);
v___x_1138_ = lean_apply_1(v_assertShared_1127_, v_t_1132_);
v___x_1139_ = lean_apply_4(v_toBind_1129_, lean_box(0), lean_box(0), v___x_1138_, v___f_1137_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(lean_object* v___f_1140_, lean_object* v_assertShared_1141_, lean_object* v_b_1142_, lean_object* v_toBind_1143_, lean_object* v___f_1144_, lean_object* v_v_1145_, lean_object* v_t_1146_, lean_object* v_____do__lift_1147_){
_start:
{
uint8_t v_____do__lift_122__boxed_1148_; lean_object* v_res_1149_; 
v_____do__lift_122__boxed_1148_ = lean_unbox(v_____do__lift_1147_);
v_res_1149_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(v___f_1140_, v_assertShared_1141_, v_b_1142_, v_toBind_1143_, v___f_1144_, v_v_1145_, v_t_1146_, v_____do__lift_122__boxed_1148_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg(lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_x_1152_, lean_object* v_t_1153_, lean_object* v_v_1154_, lean_object* v_b_1155_, uint8_t v_nondep_1156_){
_start:
{
lean_object* v_toBind_1157_; lean_object* v_share1_1158_; lean_object* v_assertShared_1159_; lean_object* v_isDebugEnabled_1160_; lean_object* v___x_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; 
v_toBind_1157_ = lean_ctor_get(v_inst_1151_, 1);
lean_inc(v_toBind_1157_);
lean_dec_ref(v_inst_1151_);
v_share1_1158_ = lean_ctor_get(v_inst_1150_, 0);
lean_inc(v_share1_1158_);
v_assertShared_1159_ = lean_ctor_get(v_inst_1150_, 1);
lean_inc(v_assertShared_1159_);
v_isDebugEnabled_1160_ = lean_ctor_get(v_inst_1150_, 2);
lean_inc(v_isDebugEnabled_1160_);
lean_dec_ref(v_inst_1150_);
v___x_1161_ = lean_box(v_nondep_1156_);
lean_inc_ref(v_b_1155_);
lean_inc_ref(v_v_1154_);
lean_inc_ref(v_t_1153_);
v___f_1162_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1162_, 0, v_x_1152_);
lean_closure_set(v___f_1162_, 1, v_t_1153_);
lean_closure_set(v___f_1162_, 2, v_v_1154_);
lean_closure_set(v___f_1162_, 3, v_b_1155_);
lean_closure_set(v___f_1162_, 4, v___x_1161_);
lean_closure_set(v___f_1162_, 5, v_share1_1158_);
lean_inc_ref(v___f_1162_);
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1163_, 0, v___f_1162_);
lean_inc(v_toBind_1157_);
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1164_, 0, v___f_1162_);
lean_closure_set(v___f_1164_, 1, v_assertShared_1159_);
lean_closure_set(v___f_1164_, 2, v_b_1155_);
lean_closure_set(v___f_1164_, 3, v_toBind_1157_);
lean_closure_set(v___f_1164_, 4, v___f_1163_);
lean_closure_set(v___f_1164_, 5, v_v_1154_);
lean_closure_set(v___f_1164_, 6, v_t_1153_);
v___x_1165_ = lean_apply_4(v_toBind_1157_, lean_box(0), lean_box(0), v_isDebugEnabled_1160_, v___f_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_x_1168_, lean_object* v_t_1169_, lean_object* v_v_1170_, lean_object* v_b_1171_, lean_object* v_nondep_1172_){
_start:
{
uint8_t v_nondep_boxed_1173_; lean_object* v_res_1174_; 
v_nondep_boxed_1173_ = lean_unbox(v_nondep_1172_);
v_res_1174_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1166_, v_inst_1167_, v_x_1168_, v_t_1169_, v_v_1170_, v_b_1171_, v_nondep_boxed_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS(lean_object* v_m_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_x_1178_, lean_object* v_t_1179_, lean_object* v_v_1180_, lean_object* v_b_1181_, uint8_t v_nondep_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1176_, v_inst_1177_, v_x_1178_, v_t_1179_, v_v_1180_, v_b_1181_, v_nondep_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___boxed(lean_object* v_m_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_x_1187_, lean_object* v_t_1188_, lean_object* v_v_1189_, lean_object* v_b_1190_, lean_object* v_nondep_1191_){
_start:
{
uint8_t v_nondep_boxed_1192_; lean_object* v_res_1193_; 
v_nondep_boxed_1192_ = lean_unbox(v_nondep_1191_);
v_res_1193_ = l_Lean_Meta_Sym_Internal_mkLetS(v_m_1184_, v_inst_1185_, v_inst_1186_, v_x_1187_, v_t_1188_, v_v_1189_, v_b_1190_, v_nondep_boxed_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(lean_object* v_x_1194_, lean_object* v_t_1195_, lean_object* v_v_1196_, lean_object* v_b_1197_, lean_object* v_share1_1198_, lean_object* v_____r_1199_){
_start:
{
uint8_t v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = 1;
v___x_1201_ = l_Lean_Expr_letE___override(v_x_1194_, v_t_1195_, v_v_1196_, v_b_1197_, v___x_1200_);
v___x_1202_ = lean_apply_1(v_share1_1198_, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS___redArg(lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_x_1205_, lean_object* v_t_1206_, lean_object* v_v_1207_, lean_object* v_b_1208_){
_start:
{
lean_object* v_toBind_1209_; lean_object* v_share1_1210_; lean_object* v_assertShared_1211_; lean_object* v_isDebugEnabled_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; 
v_toBind_1209_ = lean_ctor_get(v_inst_1204_, 1);
lean_inc(v_toBind_1209_);
lean_dec_ref(v_inst_1204_);
v_share1_1210_ = lean_ctor_get(v_inst_1203_, 0);
lean_inc(v_share1_1210_);
v_assertShared_1211_ = lean_ctor_get(v_inst_1203_, 1);
lean_inc(v_assertShared_1211_);
v_isDebugEnabled_1212_ = lean_ctor_get(v_inst_1203_, 2);
lean_inc(v_isDebugEnabled_1212_);
lean_dec_ref(v_inst_1203_);
lean_inc_ref(v_b_1208_);
lean_inc_ref(v_v_1207_);
lean_inc_ref(v_t_1206_);
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1213_, 0, v_x_1205_);
lean_closure_set(v___f_1213_, 1, v_t_1206_);
lean_closure_set(v___f_1213_, 2, v_v_1207_);
lean_closure_set(v___f_1213_, 3, v_b_1208_);
lean_closure_set(v___f_1213_, 4, v_share1_1210_);
lean_inc_ref(v___f_1213_);
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1214_, 0, v___f_1213_);
lean_inc(v_toBind_1209_);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_1215_, 0, v___f_1213_);
lean_closure_set(v___f_1215_, 1, v_assertShared_1211_);
lean_closure_set(v___f_1215_, 2, v_b_1208_);
lean_closure_set(v___f_1215_, 3, v_toBind_1209_);
lean_closure_set(v___f_1215_, 4, v___f_1214_);
lean_closure_set(v___f_1215_, 5, v_v_1207_);
lean_closure_set(v___f_1215_, 6, v_t_1206_);
v___x_1216_ = lean_apply_4(v_toBind_1209_, lean_box(0), lean_box(0), v_isDebugEnabled_1212_, v___f_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkHaveS(lean_object* v_m_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_x_1220_, lean_object* v_t_1221_, lean_object* v_v_1222_, lean_object* v_b_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(v_inst_1218_, v_inst_1219_, v_x_1220_, v_t_1221_, v_v_1222_, v_b_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1227_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__1));
v___x_1228_ = lean_unsigned_to_nat(25u);
v___x_1229_ = lean_unsigned_to_nat(148u);
v___x_1230_ = ((lean_object*)(l_Lean_Expr_updateAppS_x21___redArg___closed__0));
v___x_1231_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1232_ = l_mkPanicMessageWithDecl(v___x_1231_, v___x_1230_, v___x_1229_, v___x_1228_, v___x_1227_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21___redArg(lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_e_1235_, lean_object* v_newFn_1236_, lean_object* v_newArg_1237_){
_start:
{
uint8_t v___y_1239_; 
if (lean_obj_tag(v_e_1235_) == 5)
{
lean_object* v_fn_1244_; lean_object* v_arg_1245_; uint8_t v___x_1246_; 
v_fn_1244_ = lean_ctor_get(v_e_1235_, 0);
v_arg_1245_ = lean_ctor_get(v_e_1235_, 1);
v___x_1246_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1244_, v_newFn_1236_);
if (v___x_1246_ == 0)
{
v___y_1239_ = v___x_1246_;
goto v___jp_1238_;
}
else
{
uint8_t v___x_1247_; 
v___x_1247_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1245_, v_newArg_1237_);
v___y_1239_ = v___x_1247_;
goto v___jp_1238_;
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref(v_newArg_1237_);
lean_dec_ref(v_newFn_1236_);
lean_dec_ref(v_e_1235_);
lean_dec_ref(v_inst_1233_);
v___x_1248_ = l_Lean_instInhabitedExpr;
v___x_1249_ = l_instInhabitedOfMonad___redArg(v_inst_1234_, v___x_1248_);
v___x_1250_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1251_ = l_panic___redArg(v___x_1249_, v___x_1250_);
lean_dec(v___x_1249_);
return v___x_1251_;
}
v___jp_1238_:
{
if (v___y_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v_e_1235_);
v___x_1240_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1233_, v_inst_1234_, v_newFn_1236_, v_newArg_1237_);
return v___x_1240_;
}
else
{
lean_object* v_toApplicative_1241_; lean_object* v_toPure_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v_newArg_1237_);
lean_dec_ref(v_newFn_1236_);
lean_dec_ref(v_inst_1233_);
v_toApplicative_1241_ = lean_ctor_get(v_inst_1234_, 0);
lean_inc_ref(v_toApplicative_1241_);
lean_dec_ref(v_inst_1234_);
v_toPure_1242_ = lean_ctor_get(v_toApplicative_1241_, 1);
lean_inc(v_toPure_1242_);
lean_dec_ref(v_toApplicative_1241_);
v___x_1243_ = lean_apply_2(v_toPure_1242_, lean_box(0), v_e_1235_);
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateAppS_x21(lean_object* v_m_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_e_1255_, lean_object* v_newFn_1256_, lean_object* v_newArg_1257_){
_start:
{
uint8_t v___y_1259_; 
if (lean_obj_tag(v_e_1255_) == 5)
{
lean_object* v_fn_1264_; lean_object* v_arg_1265_; uint8_t v___x_1266_; 
v_fn_1264_ = lean_ctor_get(v_e_1255_, 0);
v_arg_1265_ = lean_ctor_get(v_e_1255_, 1);
v___x_1266_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1264_, v_newFn_1256_);
if (v___x_1266_ == 0)
{
v___y_1259_ = v___x_1266_;
goto v___jp_1258_;
}
else
{
uint8_t v___x_1267_; 
v___x_1267_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1265_, v_newArg_1257_);
v___y_1259_ = v___x_1267_;
goto v___jp_1258_;
}
}
else
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v_newArg_1257_);
lean_dec_ref(v_newFn_1256_);
lean_dec_ref(v_e_1255_);
lean_dec_ref(v_inst_1253_);
v___x_1268_ = l_Lean_instInhabitedExpr;
v___x_1269_ = l_instInhabitedOfMonad___redArg(v_inst_1254_, v___x_1268_);
v___x_1270_ = lean_obj_once(&l_Lean_Expr_updateAppS_x21___redArg___closed__2, &l_Lean_Expr_updateAppS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2);
v___x_1271_ = l_panic___redArg(v___x_1269_, v___x_1270_);
lean_dec(v___x_1269_);
return v___x_1271_;
}
v___jp_1258_:
{
if (v___y_1259_ == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref(v_e_1255_);
v___x_1260_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1253_, v_inst_1254_, v_newFn_1256_, v_newArg_1257_);
return v___x_1260_;
}
else
{
lean_object* v_toApplicative_1261_; lean_object* v_toPure_1262_; lean_object* v___x_1263_; 
lean_dec_ref(v_newArg_1257_);
lean_dec_ref(v_newFn_1256_);
lean_dec_ref(v_inst_1253_);
v_toApplicative_1261_ = lean_ctor_get(v_inst_1254_, 0);
lean_inc_ref(v_toApplicative_1261_);
lean_dec_ref(v_inst_1254_);
v_toPure_1262_ = lean_ctor_get(v_toApplicative_1261_, 1);
lean_inc(v_toPure_1262_);
lean_dec_ref(v_toApplicative_1261_);
v___x_1263_ = lean_apply_2(v_toPure_1262_, lean_box(0), v_e_1255_);
return v___x_1263_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1274_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__1));
v___x_1275_ = lean_unsigned_to_nat(24u);
v___x_1276_ = lean_unsigned_to_nat(152u);
v___x_1277_ = ((lean_object*)(l_Lean_Expr_updateMDataS_x21___redArg___closed__0));
v___x_1278_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1279_ = l_mkPanicMessageWithDecl(v___x_1278_, v___x_1277_, v___x_1276_, v___x_1275_, v___x_1274_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21___redArg(lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_e_1282_, lean_object* v_newExpr_1283_){
_start:
{
if (lean_obj_tag(v_e_1282_) == 10)
{
lean_object* v_data_1284_; lean_object* v_expr_1285_; uint8_t v___x_1286_; 
v_data_1284_ = lean_ctor_get(v_e_1282_, 0);
v_expr_1285_ = lean_ctor_get(v_e_1282_, 1);
v___x_1286_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1285_, v_newExpr_1283_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_inc(v_data_1284_);
lean_dec_ref(v_e_1282_);
v___x_1287_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1280_, v_inst_1281_, v_data_1284_, v_newExpr_1283_);
return v___x_1287_;
}
else
{
lean_object* v_toApplicative_1288_; lean_object* v_toPure_1289_; lean_object* v___x_1290_; 
lean_dec_ref(v_newExpr_1283_);
lean_dec_ref(v_inst_1280_);
v_toApplicative_1288_ = lean_ctor_get(v_inst_1281_, 0);
lean_inc_ref(v_toApplicative_1288_);
lean_dec_ref(v_inst_1281_);
v_toPure_1289_ = lean_ctor_get(v_toApplicative_1288_, 1);
lean_inc(v_toPure_1289_);
lean_dec_ref(v_toApplicative_1288_);
v___x_1290_ = lean_apply_2(v_toPure_1289_, lean_box(0), v_e_1282_);
return v___x_1290_;
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref(v_newExpr_1283_);
lean_dec_ref(v_e_1282_);
lean_dec_ref(v_inst_1280_);
v___x_1291_ = l_Lean_instInhabitedExpr;
v___x_1292_ = l_instInhabitedOfMonad___redArg(v_inst_1281_, v___x_1291_);
v___x_1293_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1294_ = l_panic___redArg(v___x_1292_, v___x_1293_);
lean_dec(v___x_1292_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMDataS_x21(lean_object* v_m_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_e_1298_, lean_object* v_newExpr_1299_){
_start:
{
if (lean_obj_tag(v_e_1298_) == 10)
{
lean_object* v_data_1300_; lean_object* v_expr_1301_; uint8_t v___x_1302_; 
v_data_1300_ = lean_ctor_get(v_e_1298_, 0);
v_expr_1301_ = lean_ctor_get(v_e_1298_, 1);
v___x_1302_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1301_, v_newExpr_1299_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
lean_inc(v_data_1300_);
lean_dec_ref(v_e_1298_);
v___x_1303_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(v_inst_1296_, v_inst_1297_, v_data_1300_, v_newExpr_1299_);
return v___x_1303_;
}
else
{
lean_object* v_toApplicative_1304_; lean_object* v_toPure_1305_; lean_object* v___x_1306_; 
lean_dec_ref(v_newExpr_1299_);
lean_dec_ref(v_inst_1296_);
v_toApplicative_1304_ = lean_ctor_get(v_inst_1297_, 0);
lean_inc_ref(v_toApplicative_1304_);
lean_dec_ref(v_inst_1297_);
v_toPure_1305_ = lean_ctor_get(v_toApplicative_1304_, 1);
lean_inc(v_toPure_1305_);
lean_dec_ref(v_toApplicative_1304_);
v___x_1306_ = lean_apply_2(v_toPure_1305_, lean_box(0), v_e_1298_);
return v___x_1306_;
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v_newExpr_1299_);
lean_dec_ref(v_e_1298_);
lean_dec_ref(v_inst_1296_);
v___x_1307_ = l_Lean_instInhabitedExpr;
v___x_1308_ = l_instInhabitedOfMonad___redArg(v_inst_1297_, v___x_1307_);
v___x_1309_ = lean_obj_once(&l_Lean_Expr_updateMDataS_x21___redArg___closed__2, &l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2);
v___x_1310_ = l_panic___redArg(v___x_1308_, v___x_1309_);
lean_dec(v___x_1308_);
return v___x_1310_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1313_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__1));
v___x_1314_ = lean_unsigned_to_nat(25u);
v___x_1315_ = lean_unsigned_to_nat(156u);
v___x_1316_ = ((lean_object*)(l_Lean_Expr_updateProjS_x21___redArg___closed__0));
v___x_1317_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1318_ = l_mkPanicMessageWithDecl(v___x_1317_, v___x_1316_, v___x_1315_, v___x_1314_, v___x_1313_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21___redArg(lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_e_1321_, lean_object* v_newExpr_1322_){
_start:
{
if (lean_obj_tag(v_e_1321_) == 11)
{
lean_object* v_typeName_1323_; lean_object* v_idx_1324_; lean_object* v_struct_1325_; uint8_t v___x_1326_; 
v_typeName_1323_ = lean_ctor_get(v_e_1321_, 0);
v_idx_1324_ = lean_ctor_get(v_e_1321_, 1);
v_struct_1325_ = lean_ctor_get(v_e_1321_, 2);
v___x_1326_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1325_, v_newExpr_1322_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_inc(v_idx_1324_);
lean_inc(v_typeName_1323_);
lean_dec_ref(v_e_1321_);
v___x_1327_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1319_, v_inst_1320_, v_typeName_1323_, v_idx_1324_, v_newExpr_1322_);
return v___x_1327_;
}
else
{
lean_object* v_toApplicative_1328_; lean_object* v_toPure_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v_newExpr_1322_);
lean_dec_ref(v_inst_1319_);
v_toApplicative_1328_ = lean_ctor_get(v_inst_1320_, 0);
lean_inc_ref(v_toApplicative_1328_);
lean_dec_ref(v_inst_1320_);
v_toPure_1329_ = lean_ctor_get(v_toApplicative_1328_, 1);
lean_inc(v_toPure_1329_);
lean_dec_ref(v_toApplicative_1328_);
v___x_1330_ = lean_apply_2(v_toPure_1329_, lean_box(0), v_e_1321_);
return v___x_1330_;
}
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v_newExpr_1322_);
lean_dec_ref(v_e_1321_);
lean_dec_ref(v_inst_1319_);
v___x_1331_ = l_Lean_instInhabitedExpr;
v___x_1332_ = l_instInhabitedOfMonad___redArg(v_inst_1320_, v___x_1331_);
v___x_1333_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1334_ = l_panic___redArg(v___x_1332_, v___x_1333_);
lean_dec(v___x_1332_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProjS_x21(lean_object* v_m_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_e_1338_, lean_object* v_newExpr_1339_){
_start:
{
if (lean_obj_tag(v_e_1338_) == 11)
{
lean_object* v_typeName_1340_; lean_object* v_idx_1341_; lean_object* v_struct_1342_; uint8_t v___x_1343_; 
v_typeName_1340_ = lean_ctor_get(v_e_1338_, 0);
v_idx_1341_ = lean_ctor_get(v_e_1338_, 1);
v_struct_1342_ = lean_ctor_get(v_e_1338_, 2);
v___x_1343_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1342_, v_newExpr_1339_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_inc(v_idx_1341_);
lean_inc(v_typeName_1340_);
lean_dec_ref(v_e_1338_);
v___x_1344_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(v_inst_1336_, v_inst_1337_, v_typeName_1340_, v_idx_1341_, v_newExpr_1339_);
return v___x_1344_;
}
else
{
lean_object* v_toApplicative_1345_; lean_object* v_toPure_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v_newExpr_1339_);
lean_dec_ref(v_inst_1336_);
v_toApplicative_1345_ = lean_ctor_get(v_inst_1337_, 0);
lean_inc_ref(v_toApplicative_1345_);
lean_dec_ref(v_inst_1337_);
v_toPure_1346_ = lean_ctor_get(v_toApplicative_1345_, 1);
lean_inc(v_toPure_1346_);
lean_dec_ref(v_toApplicative_1345_);
v___x_1347_ = lean_apply_2(v_toPure_1346_, lean_box(0), v_e_1338_);
return v___x_1347_;
}
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec_ref(v_newExpr_1339_);
lean_dec_ref(v_e_1338_);
lean_dec_ref(v_inst_1336_);
v___x_1348_ = l_Lean_instInhabitedExpr;
v___x_1349_ = l_instInhabitedOfMonad___redArg(v_inst_1337_, v___x_1348_);
v___x_1350_ = lean_obj_once(&l_Lean_Expr_updateProjS_x21___redArg___closed__2, &l_Lean_Expr_updateProjS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2);
v___x_1351_ = l_panic___redArg(v___x_1349_, v___x_1350_);
lean_dec(v___x_1349_);
return v___x_1351_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1354_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__1));
v___x_1355_ = lean_unsigned_to_nat(31u);
v___x_1356_ = lean_unsigned_to_nat(160u);
v___x_1357_ = ((lean_object*)(l_Lean_Expr_updateForallS_x21___redArg___closed__0));
v___x_1358_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1359_ = l_mkPanicMessageWithDecl(v___x_1358_, v___x_1357_, v___x_1356_, v___x_1355_, v___x_1354_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21___redArg(lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_e_1362_, lean_object* v_newDomain_1363_, lean_object* v_newBody_1364_){
_start:
{
if (lean_obj_tag(v_e_1362_) == 7)
{
lean_object* v_binderName_1365_; lean_object* v_binderType_1366_; lean_object* v_body_1367_; uint8_t v_binderInfo_1368_; uint8_t v___y_1370_; uint8_t v___x_1375_; 
v_binderName_1365_ = lean_ctor_get(v_e_1362_, 0);
v_binderType_1366_ = lean_ctor_get(v_e_1362_, 1);
v_body_1367_ = lean_ctor_get(v_e_1362_, 2);
v_binderInfo_1368_ = lean_ctor_get_uint8(v_e_1362_, sizeof(void*)*3 + 8);
v___x_1375_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1366_, v_newDomain_1363_);
if (v___x_1375_ == 0)
{
v___y_1370_ = v___x_1375_;
goto v___jp_1369_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1367_, v_newBody_1364_);
v___y_1370_ = v___x_1376_;
goto v___jp_1369_;
}
v___jp_1369_:
{
if (v___y_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_inc(v_binderName_1365_);
lean_dec_ref(v_e_1362_);
v___x_1371_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1360_, v_inst_1361_, v_binderName_1365_, v_binderInfo_1368_, v_newDomain_1363_, v_newBody_1364_);
return v___x_1371_;
}
else
{
lean_object* v_toApplicative_1372_; lean_object* v_toPure_1373_; lean_object* v___x_1374_; 
lean_dec_ref(v_newBody_1364_);
lean_dec_ref(v_newDomain_1363_);
lean_dec_ref(v_inst_1360_);
v_toApplicative_1372_ = lean_ctor_get(v_inst_1361_, 0);
lean_inc_ref(v_toApplicative_1372_);
lean_dec_ref(v_inst_1361_);
v_toPure_1373_ = lean_ctor_get(v_toApplicative_1372_, 1);
lean_inc(v_toPure_1373_);
lean_dec_ref(v_toApplicative_1372_);
v___x_1374_ = lean_apply_2(v_toPure_1373_, lean_box(0), v_e_1362_);
return v___x_1374_;
}
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref(v_newBody_1364_);
lean_dec_ref(v_newDomain_1363_);
lean_dec_ref(v_e_1362_);
lean_dec_ref(v_inst_1360_);
v___x_1377_ = l_Lean_instInhabitedExpr;
v___x_1378_ = l_instInhabitedOfMonad___redArg(v_inst_1361_, v___x_1377_);
v___x_1379_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1380_ = l_panic___redArg(v___x_1378_, v___x_1379_);
lean_dec(v___x_1378_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallS_x21(lean_object* v_m_1381_, lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_e_1384_, lean_object* v_newDomain_1385_, lean_object* v_newBody_1386_){
_start:
{
if (lean_obj_tag(v_e_1384_) == 7)
{
lean_object* v_binderName_1387_; lean_object* v_binderType_1388_; lean_object* v_body_1389_; uint8_t v_binderInfo_1390_; uint8_t v___y_1392_; uint8_t v___x_1397_; 
v_binderName_1387_ = lean_ctor_get(v_e_1384_, 0);
v_binderType_1388_ = lean_ctor_get(v_e_1384_, 1);
v_body_1389_ = lean_ctor_get(v_e_1384_, 2);
v_binderInfo_1390_ = lean_ctor_get_uint8(v_e_1384_, sizeof(void*)*3 + 8);
v___x_1397_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1388_, v_newDomain_1385_);
if (v___x_1397_ == 0)
{
v___y_1392_ = v___x_1397_;
goto v___jp_1391_;
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1389_, v_newBody_1386_);
v___y_1392_ = v___x_1398_;
goto v___jp_1391_;
}
v___jp_1391_:
{
if (v___y_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_inc(v_binderName_1387_);
lean_dec_ref(v_e_1384_);
v___x_1393_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(v_inst_1382_, v_inst_1383_, v_binderName_1387_, v_binderInfo_1390_, v_newDomain_1385_, v_newBody_1386_);
return v___x_1393_;
}
else
{
lean_object* v_toApplicative_1394_; lean_object* v_toPure_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v_newBody_1386_);
lean_dec_ref(v_newDomain_1385_);
lean_dec_ref(v_inst_1382_);
v_toApplicative_1394_ = lean_ctor_get(v_inst_1383_, 0);
lean_inc_ref(v_toApplicative_1394_);
lean_dec_ref(v_inst_1383_);
v_toPure_1395_ = lean_ctor_get(v_toApplicative_1394_, 1);
lean_inc(v_toPure_1395_);
lean_dec_ref(v_toApplicative_1394_);
v___x_1396_ = lean_apply_2(v_toPure_1395_, lean_box(0), v_e_1384_);
return v___x_1396_;
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec_ref(v_newBody_1386_);
lean_dec_ref(v_newDomain_1385_);
lean_dec_ref(v_e_1384_);
lean_dec_ref(v_inst_1382_);
v___x_1399_ = l_Lean_instInhabitedExpr;
v___x_1400_ = l_instInhabitedOfMonad___redArg(v_inst_1383_, v___x_1399_);
v___x_1401_ = lean_obj_once(&l_Lean_Expr_updateForallS_x21___redArg___closed__2, &l_Lean_Expr_updateForallS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2);
v___x_1402_ = l_panic___redArg(v___x_1400_, v___x_1401_);
lean_dec(v___x_1400_);
return v___x_1402_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1405_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1));
v___x_1406_ = lean_unsigned_to_nat(27u);
v___x_1407_ = lean_unsigned_to_nat(167u);
v___x_1408_ = ((lean_object*)(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0));
v___x_1409_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1410_ = l_mkPanicMessageWithDecl(v___x_1409_, v___x_1408_, v___x_1407_, v___x_1406_, v___x_1405_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21___redArg(lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_e_1413_, lean_object* v_newDomain_1414_, lean_object* v_newBody_1415_){
_start:
{
if (lean_obj_tag(v_e_1413_) == 6)
{
lean_object* v_binderName_1416_; lean_object* v_binderType_1417_; lean_object* v_body_1418_; uint8_t v_binderInfo_1419_; uint8_t v___y_1421_; uint8_t v___x_1426_; 
v_binderName_1416_ = lean_ctor_get(v_e_1413_, 0);
v_binderType_1417_ = lean_ctor_get(v_e_1413_, 1);
v_body_1418_ = lean_ctor_get(v_e_1413_, 2);
v_binderInfo_1419_ = lean_ctor_get_uint8(v_e_1413_, sizeof(void*)*3 + 8);
v___x_1426_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1417_, v_newDomain_1414_);
if (v___x_1426_ == 0)
{
v___y_1421_ = v___x_1426_;
goto v___jp_1420_;
}
else
{
uint8_t v___x_1427_; 
v___x_1427_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1418_, v_newBody_1415_);
v___y_1421_ = v___x_1427_;
goto v___jp_1420_;
}
v___jp_1420_:
{
if (v___y_1421_ == 0)
{
lean_object* v___x_1422_; 
lean_inc(v_binderName_1416_);
lean_dec_ref(v_e_1413_);
v___x_1422_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1411_, v_inst_1412_, v_binderName_1416_, v_binderInfo_1419_, v_newDomain_1414_, v_newBody_1415_);
return v___x_1422_;
}
else
{
lean_object* v_toApplicative_1423_; lean_object* v_toPure_1424_; lean_object* v___x_1425_; 
lean_dec_ref(v_newBody_1415_);
lean_dec_ref(v_newDomain_1414_);
lean_dec_ref(v_inst_1411_);
v_toApplicative_1423_ = lean_ctor_get(v_inst_1412_, 0);
lean_inc_ref(v_toApplicative_1423_);
lean_dec_ref(v_inst_1412_);
v_toPure_1424_ = lean_ctor_get(v_toApplicative_1423_, 1);
lean_inc(v_toPure_1424_);
lean_dec_ref(v_toApplicative_1423_);
v___x_1425_ = lean_apply_2(v_toPure_1424_, lean_box(0), v_e_1413_);
return v___x_1425_;
}
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
lean_dec_ref(v_newBody_1415_);
lean_dec_ref(v_newDomain_1414_);
lean_dec_ref(v_e_1413_);
lean_dec_ref(v_inst_1411_);
v___x_1428_ = l_Lean_instInhabitedExpr;
v___x_1429_ = l_instInhabitedOfMonad___redArg(v_inst_1412_, v___x_1428_);
v___x_1430_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1431_ = l_panic___redArg(v___x_1429_, v___x_1430_);
lean_dec(v___x_1429_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaS_x21(lean_object* v_m_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_e_1435_, lean_object* v_newDomain_1436_, lean_object* v_newBody_1437_){
_start:
{
if (lean_obj_tag(v_e_1435_) == 6)
{
lean_object* v_binderName_1438_; lean_object* v_binderType_1439_; lean_object* v_body_1440_; uint8_t v_binderInfo_1441_; uint8_t v___y_1443_; uint8_t v___x_1448_; 
v_binderName_1438_ = lean_ctor_get(v_e_1435_, 0);
v_binderType_1439_ = lean_ctor_get(v_e_1435_, 1);
v_body_1440_ = lean_ctor_get(v_e_1435_, 2);
v_binderInfo_1441_ = lean_ctor_get_uint8(v_e_1435_, sizeof(void*)*3 + 8);
v___x_1448_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1439_, v_newDomain_1436_);
if (v___x_1448_ == 0)
{
v___y_1443_ = v___x_1448_;
goto v___jp_1442_;
}
else
{
uint8_t v___x_1449_; 
v___x_1449_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1440_, v_newBody_1437_);
v___y_1443_ = v___x_1449_;
goto v___jp_1442_;
}
v___jp_1442_:
{
if (v___y_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_inc(v_binderName_1438_);
lean_dec_ref(v_e_1435_);
v___x_1444_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(v_inst_1433_, v_inst_1434_, v_binderName_1438_, v_binderInfo_1441_, v_newDomain_1436_, v_newBody_1437_);
return v___x_1444_;
}
else
{
lean_object* v_toApplicative_1445_; lean_object* v_toPure_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v_newBody_1437_);
lean_dec_ref(v_newDomain_1436_);
lean_dec_ref(v_inst_1433_);
v_toApplicative_1445_ = lean_ctor_get(v_inst_1434_, 0);
lean_inc_ref(v_toApplicative_1445_);
lean_dec_ref(v_inst_1434_);
v_toPure_1446_ = lean_ctor_get(v_toApplicative_1445_, 1);
lean_inc(v_toPure_1446_);
lean_dec_ref(v_toApplicative_1445_);
v___x_1447_ = lean_apply_2(v_toPure_1446_, lean_box(0), v_e_1435_);
return v___x_1447_;
}
}
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref(v_newBody_1437_);
lean_dec_ref(v_newDomain_1436_);
lean_dec_ref(v_e_1435_);
lean_dec_ref(v_inst_1433_);
v___x_1450_ = l_Lean_instInhabitedExpr;
v___x_1451_ = l_instInhabitedOfMonad___redArg(v_inst_1434_, v___x_1450_);
v___x_1452_ = lean_obj_once(&l_Lean_Expr_updateLambdaS_x21___redArg___closed__2, &l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2);
v___x_1453_ = l_panic___redArg(v___x_1451_, v___x_1452_);
lean_dec(v___x_1451_);
return v___x_1453_;
}
}
}
static lean_object* _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1456_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__1));
v___x_1457_ = lean_unsigned_to_nat(34u);
v___x_1458_ = lean_unsigned_to_nat(174u);
v___x_1459_ = ((lean_object*)(l_Lean_Expr_updateLetS_x21___redArg___closed__0));
v___x_1460_ = ((lean_object*)(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0));
v___x_1461_ = l_mkPanicMessageWithDecl(v___x_1460_, v___x_1459_, v___x_1458_, v___x_1457_, v___x_1456_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21___redArg(lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_e_1464_, lean_object* v_newType_1465_, lean_object* v_newVal_1466_, lean_object* v_newBody_1467_){
_start:
{
if (lean_obj_tag(v_e_1464_) == 8)
{
lean_object* v_declName_1468_; lean_object* v_type_1469_; lean_object* v_value_1470_; lean_object* v_body_1471_; uint8_t v_nondep_1472_; uint8_t v___y_1474_; uint8_t v___x_1481_; 
v_declName_1468_ = lean_ctor_get(v_e_1464_, 0);
v_type_1469_ = lean_ctor_get(v_e_1464_, 1);
v_value_1470_ = lean_ctor_get(v_e_1464_, 2);
v_body_1471_ = lean_ctor_get(v_e_1464_, 3);
v_nondep_1472_ = lean_ctor_get_uint8(v_e_1464_, sizeof(void*)*4 + 8);
v___x_1481_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1469_, v_newType_1465_);
if (v___x_1481_ == 0)
{
v___y_1474_ = v___x_1481_;
goto v___jp_1473_;
}
else
{
uint8_t v___x_1482_; 
v___x_1482_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1470_, v_newVal_1466_);
v___y_1474_ = v___x_1482_;
goto v___jp_1473_;
}
v___jp_1473_:
{
if (v___y_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_inc(v_declName_1468_);
lean_dec_ref(v_e_1464_);
v___x_1475_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1462_, v_inst_1463_, v_declName_1468_, v_newType_1465_, v_newVal_1466_, v_newBody_1467_, v_nondep_1472_);
return v___x_1475_;
}
else
{
uint8_t v___x_1476_; 
v___x_1476_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1471_, v_newBody_1467_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_inc(v_declName_1468_);
lean_dec_ref(v_e_1464_);
v___x_1477_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1462_, v_inst_1463_, v_declName_1468_, v_newType_1465_, v_newVal_1466_, v_newBody_1467_, v_nondep_1472_);
return v___x_1477_;
}
else
{
lean_object* v_toApplicative_1478_; lean_object* v_toPure_1479_; lean_object* v___x_1480_; 
lean_dec_ref(v_newBody_1467_);
lean_dec_ref(v_newVal_1466_);
lean_dec_ref(v_newType_1465_);
lean_dec_ref(v_inst_1462_);
v_toApplicative_1478_ = lean_ctor_get(v_inst_1463_, 0);
lean_inc_ref(v_toApplicative_1478_);
lean_dec_ref(v_inst_1463_);
v_toPure_1479_ = lean_ctor_get(v_toApplicative_1478_, 1);
lean_inc(v_toPure_1479_);
lean_dec_ref(v_toApplicative_1478_);
v___x_1480_ = lean_apply_2(v_toPure_1479_, lean_box(0), v_e_1464_);
return v___x_1480_;
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v_newBody_1467_);
lean_dec_ref(v_newVal_1466_);
lean_dec_ref(v_newType_1465_);
lean_dec_ref(v_e_1464_);
lean_dec_ref(v_inst_1462_);
v___x_1483_ = l_Lean_instInhabitedExpr;
v___x_1484_ = l_instInhabitedOfMonad___redArg(v_inst_1463_, v___x_1483_);
v___x_1485_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1486_ = l_panic___redArg(v___x_1484_, v___x_1485_);
lean_dec(v___x_1484_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLetS_x21(lean_object* v_m_1487_, lean_object* v_inst_1488_, lean_object* v_inst_1489_, lean_object* v_e_1490_, lean_object* v_newType_1491_, lean_object* v_newVal_1492_, lean_object* v_newBody_1493_){
_start:
{
if (lean_obj_tag(v_e_1490_) == 8)
{
lean_object* v_declName_1494_; lean_object* v_type_1495_; lean_object* v_value_1496_; lean_object* v_body_1497_; uint8_t v_nondep_1498_; uint8_t v___y_1500_; uint8_t v___x_1507_; 
v_declName_1494_ = lean_ctor_get(v_e_1490_, 0);
v_type_1495_ = lean_ctor_get(v_e_1490_, 1);
v_value_1496_ = lean_ctor_get(v_e_1490_, 2);
v_body_1497_ = lean_ctor_get(v_e_1490_, 3);
v_nondep_1498_ = lean_ctor_get_uint8(v_e_1490_, sizeof(void*)*4 + 8);
v___x_1507_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1495_, v_newType_1491_);
if (v___x_1507_ == 0)
{
v___y_1500_ = v___x_1507_;
goto v___jp_1499_;
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1496_, v_newVal_1492_);
v___y_1500_ = v___x_1508_;
goto v___jp_1499_;
}
v___jp_1499_:
{
if (v___y_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_inc(v_declName_1494_);
lean_dec_ref(v_e_1490_);
v___x_1501_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1488_, v_inst_1489_, v_declName_1494_, v_newType_1491_, v_newVal_1492_, v_newBody_1493_, v_nondep_1498_);
return v___x_1501_;
}
else
{
uint8_t v___x_1502_; 
v___x_1502_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1497_, v_newBody_1493_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
lean_inc(v_declName_1494_);
lean_dec_ref(v_e_1490_);
v___x_1503_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(v_inst_1488_, v_inst_1489_, v_declName_1494_, v_newType_1491_, v_newVal_1492_, v_newBody_1493_, v_nondep_1498_);
return v___x_1503_;
}
else
{
lean_object* v_toApplicative_1504_; lean_object* v_toPure_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v_newBody_1493_);
lean_dec_ref(v_newVal_1492_);
lean_dec_ref(v_newType_1491_);
lean_dec_ref(v_inst_1488_);
v_toApplicative_1504_ = lean_ctor_get(v_inst_1489_, 0);
lean_inc_ref(v_toApplicative_1504_);
lean_dec_ref(v_inst_1489_);
v_toPure_1505_ = lean_ctor_get(v_toApplicative_1504_, 1);
lean_inc(v_toPure_1505_);
lean_dec_ref(v_toApplicative_1504_);
v___x_1506_ = lean_apply_2(v_toPure_1505_, lean_box(0), v_e_1490_);
return v___x_1506_;
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec_ref(v_newBody_1493_);
lean_dec_ref(v_newVal_1492_);
lean_dec_ref(v_newType_1491_);
lean_dec_ref(v_e_1490_);
lean_dec_ref(v_inst_1488_);
v___x_1509_ = l_Lean_instInhabitedExpr;
v___x_1510_ = l_instInhabitedOfMonad___redArg(v_inst_1489_, v___x_1509_);
v___x_1511_ = lean_obj_once(&l_Lean_Expr_updateLetS_x21___redArg___closed__2, &l_Lean_Expr_updateLetS_x21___redArg___closed__2_once, _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2);
v___x_1512_ = l_panic___redArg(v___x_1510_, v___x_1511_);
lean_dec(v___x_1510_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_a_u2082_1515_, lean_object* v_____do__lift_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1513_, v_inst_1514_, v_____do__lift_1516_, v_a_u2082_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_f_1520_, lean_object* v_a_u2081_1521_, lean_object* v_a_u2082_1522_){
_start:
{
lean_object* v_toBind_1523_; lean_object* v___f_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_toBind_1523_ = lean_ctor_get(v_inst_1519_, 1);
lean_inc(v_toBind_1523_);
lean_inc_ref(v_inst_1519_);
lean_inc_ref(v_inst_1518_);
v___f_1524_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1524_, 0, v_inst_1518_);
lean_closure_set(v___f_1524_, 1, v_inst_1519_);
lean_closure_set(v___f_1524_, 2, v_a_u2082_1522_);
v___x_1525_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1518_, v_inst_1519_, v_f_1520_, v_a_u2081_1521_);
v___x_1526_ = lean_apply_4(v_toBind_1523_, lean_box(0), lean_box(0), v___x_1525_, v___f_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082(lean_object* v_m_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_f_1530_, lean_object* v_a_u2081_1531_, lean_object* v_a_u2082_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1528_, v_inst_1529_, v_f_1530_, v_a_u2081_1531_, v_a_u2082_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_a_u2083_1536_, lean_object* v_____do__lift_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1534_, v_inst_1535_, v_____do__lift_1537_, v_a_u2083_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_f_1541_, lean_object* v_a_u2081_1542_, lean_object* v_a_u2082_1543_, lean_object* v_a_u2083_1544_){
_start:
{
lean_object* v_toBind_1545_; lean_object* v___f_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_toBind_1545_ = lean_ctor_get(v_inst_1540_, 1);
lean_inc(v_toBind_1545_);
lean_inc_ref(v_inst_1540_);
lean_inc_ref(v_inst_1539_);
v___f_1546_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1546_, 0, v_inst_1539_);
lean_closure_set(v___f_1546_, 1, v_inst_1540_);
lean_closure_set(v___f_1546_, 2, v_a_u2083_1544_);
v___x_1547_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(v_inst_1539_, v_inst_1540_, v_f_1541_, v_a_u2081_1542_, v_a_u2082_1543_);
v___x_1548_ = lean_apply_4(v_toBind_1545_, lean_box(0), lean_box(0), v___x_1547_, v___f_1546_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083(lean_object* v_m_1549_, lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_f_1552_, lean_object* v_a_u2081_1553_, lean_object* v_a_u2082_1554_, lean_object* v_a_u2083_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1550_, v_inst_1551_, v_f_1552_, v_a_u2081_1553_, v_a_u2082_1554_, v_a_u2083_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_a_u2084_1559_, lean_object* v_____do__lift_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1557_, v_inst_1558_, v_____do__lift_1560_, v_a_u2084_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(lean_object* v_inst_1562_, lean_object* v_inst_1563_, lean_object* v_f_1564_, lean_object* v_a_u2081_1565_, lean_object* v_a_u2082_1566_, lean_object* v_a_u2083_1567_, lean_object* v_a_u2084_1568_){
_start:
{
lean_object* v_toBind_1569_; lean_object* v___f_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_toBind_1569_ = lean_ctor_get(v_inst_1563_, 1);
lean_inc(v_toBind_1569_);
lean_inc_ref(v_inst_1563_);
lean_inc_ref(v_inst_1562_);
v___f_1570_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1570_, 0, v_inst_1562_);
lean_closure_set(v___f_1570_, 1, v_inst_1563_);
lean_closure_set(v___f_1570_, 2, v_a_u2084_1568_);
v___x_1571_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(v_inst_1562_, v_inst_1563_, v_f_1564_, v_a_u2081_1565_, v_a_u2082_1566_, v_a_u2083_1567_);
v___x_1572_ = lean_apply_4(v_toBind_1569_, lean_box(0), lean_box(0), v___x_1571_, v___f_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084(lean_object* v_m_1573_, lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_f_1576_, lean_object* v_a_u2081_1577_, lean_object* v_a_u2082_1578_, lean_object* v_a_u2083_1579_, lean_object* v_a_u2084_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1574_, v_inst_1575_, v_f_1576_, v_a_u2081_1577_, v_a_u2082_1578_, v_a_u2083_1579_, v_a_u2084_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_a_u2085_1584_, lean_object* v_____do__lift_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_1582_, v_inst_1583_, v_____do__lift_1585_, v_a_u2085_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_f_1589_, lean_object* v_a_u2081_1590_, lean_object* v_a_u2082_1591_, lean_object* v_a_u2083_1592_, lean_object* v_a_u2084_1593_, lean_object* v_a_u2085_1594_){
_start:
{
lean_object* v_toBind_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_toBind_1595_ = lean_ctor_get(v_inst_1588_, 1);
lean_inc(v_toBind_1595_);
lean_inc_ref(v_inst_1588_);
lean_inc_ref(v_inst_1587_);
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1596_, 0, v_inst_1587_);
lean_closure_set(v___f_1596_, 1, v_inst_1588_);
lean_closure_set(v___f_1596_, 2, v_a_u2085_1594_);
v___x_1597_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(v_inst_1587_, v_inst_1588_, v_f_1589_, v_a_u2081_1590_, v_a_u2082_1591_, v_a_u2083_1592_, v_a_u2084_1593_);
v___x_1598_ = lean_apply_4(v_toBind_1595_, lean_box(0), lean_box(0), v___x_1597_, v___f_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085(lean_object* v_m_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v_f_1602_, lean_object* v_a_u2081_1603_, lean_object* v_a_u2082_1604_, lean_object* v_a_u2083_1605_, lean_object* v_a_u2084_1606_, lean_object* v_a_u2085_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(v_inst_1600_, v_inst_1601_, v_f_1602_, v_a_u2081_1603_, v_a_u2082_1604_, v_a_u2083_1605_, v_a_u2084_1606_, v_a_u2085_1607_);
return v___x_1608_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy = _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy();
lean_mark_persistent(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy);
l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM = _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM();
lean_mark_persistent(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
}
#ifdef __cplusplus
}
#endif
