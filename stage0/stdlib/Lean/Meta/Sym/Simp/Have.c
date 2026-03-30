// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Have
// Imports: public import Lean.Meta.Sym.Simp.Lambda import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.ReplaceS import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.InferType import Lean.Meta.AppBuilder import Lean.Meta.HaveTelescope import Lean.Util.CollectFVars import Init.Omega import Init.While
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
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instInhabitedSymM(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_letNondep_x21(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2;
static const lean_array_object l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1;
static const lean_array_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: !t.hasLooseBVars\n      "};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.toBetaApp.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Sym.Simp.Have"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_Simp_toBetaApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_toBetaApp___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.elimAuxApps"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "assertion violation: numArgs == expectedNumArgs\n            "};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.toHave.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.toHave"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "congrFun'"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 239, 156, 219, 118, 185, 235, 192)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(56, 82, 209, 127, 228, 246, 91, 162)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Sym.Simp.Have.0.Lean.Meta.Sym.Simp.simpBetaApp.go"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_simpLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpLambda___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_simpLet___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpLet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__3));
v___x_10_ = lean_box(0);
v___x_11_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2, &l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__2);
v___x_12_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_11_);
lean_ctor_set(v___x_12_, 3, v___x_11_);
lean_ctor_set(v___x_12_, 4, v___x_9_);
lean_ctor_set(v___x_12_, 5, v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4, &l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default___closed__4);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default;
return v___x_14_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(lean_object* v_k_15_, lean_object* v_t_16_){
_start:
{
if (lean_obj_tag(v_t_16_) == 0)
{
lean_object* v_k_17_; lean_object* v_l_18_; lean_object* v_r_19_; uint8_t v___x_20_; 
v_k_17_ = lean_ctor_get(v_t_16_, 1);
v_l_18_ = lean_ctor_get(v_t_16_, 3);
v_r_19_ = lean_ctor_get(v_t_16_, 4);
v___x_20_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_15_, v_k_17_);
switch(v___x_20_)
{
case 0:
{
v_t_16_ = v_l_18_;
goto _start;
}
case 1:
{
uint8_t v___x_22_; 
v___x_22_ = 1;
return v___x_22_;
}
default: 
{
v_t_16_ = v_r_19_;
goto _start;
}
}
}
else
{
uint8_t v___x_24_; 
v___x_24_ = 0;
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg___boxed(lean_object* v_k_25_, lean_object* v_t_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_25_, v_t_26_);
lean_dec(v_t_26_);
lean_dec(v_k_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(lean_object* v_fvarIdToPos_29_, lean_object* v_as_30_, size_t v_i_31_, size_t v_stop_32_, lean_object* v_b_33_){
_start:
{
lean_object* v___y_35_; uint8_t v___x_39_; 
v___x_39_ = lean_usize_dec_eq(v_i_31_, v_stop_32_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_array_uget_borrowed(v_as_30_, v_i_31_);
v___x_41_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v___x_40_, v_fvarIdToPos_29_);
if (v___x_41_ == 0)
{
v___y_35_ = v_b_33_;
goto v___jp_34_;
}
else
{
lean_object* v___x_42_; 
lean_inc(v___x_40_);
v___x_42_ = lean_array_push(v_b_33_, v___x_40_);
v___y_35_ = v___x_42_;
goto v___jp_34_;
}
}
else
{
return v_b_33_;
}
v___jp_34_:
{
size_t v___x_36_; size_t v___x_37_; 
v___x_36_ = ((size_t)1ULL);
v___x_37_ = lean_usize_add(v_i_31_, v___x_36_);
v_i_31_ = v___x_37_;
v_b_33_ = v___y_35_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3___boxed(lean_object* v_fvarIdToPos_43_, lean_object* v_as_44_, lean_object* v_i_45_, lean_object* v_stop_46_, lean_object* v_b_47_){
_start:
{
size_t v_i_boxed_48_; size_t v_stop_boxed_49_; lean_object* v_res_50_; 
v_i_boxed_48_ = lean_unbox_usize(v_i_45_);
lean_dec(v_i_45_);
v_stop_boxed_49_ = lean_unbox_usize(v_stop_46_);
lean_dec(v_stop_46_);
v_res_50_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_43_, v_as_44_, v_i_boxed_48_, v_stop_boxed_49_, v_b_47_);
lean_dec_ref(v_as_44_);
lean_dec(v_fvarIdToPos_43_);
return v_res_50_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_54_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__2));
v___x_55_ = lean_unsigned_to_nat(13u);
v___x_56_ = lean_unsigned_to_nat(227u);
v___x_57_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__1));
v___x_58_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__0));
v___x_59_ = l_mkPanicMessageWithDecl(v___x_58_, v___x_57_, v___x_56_, v___x_55_, v___x_54_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(lean_object* v_inst_60_, lean_object* v_t_61_, lean_object* v_k_62_){
_start:
{
if (lean_obj_tag(v_t_61_) == 0)
{
lean_object* v_k_63_; lean_object* v_v_64_; lean_object* v_l_65_; lean_object* v_r_66_; uint8_t v___x_67_; 
v_k_63_ = lean_ctor_get(v_t_61_, 1);
v_v_64_ = lean_ctor_get(v_t_61_, 2);
v_l_65_ = lean_ctor_get(v_t_61_, 3);
v_r_66_ = lean_ctor_get(v_t_61_, 4);
v___x_67_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_62_, v_k_63_);
switch(v___x_67_)
{
case 0:
{
v_t_61_ = v_l_65_;
goto _start;
}
case 1:
{
lean_inc(v_v_64_);
return v_v_64_;
}
default: 
{
v_t_61_ = v_r_66_;
goto _start;
}
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___closed__3);
v___x_71_ = lean_panic_fn_borrowed(v_inst_60_, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg___boxed(lean_object* v_inst_72_, lean_object* v_t_73_, lean_object* v_k_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v_inst_72_, v_t_73_, v_k_74_);
lean_dec(v_k_74_);
lean_dec(v_t_73_);
lean_dec(v_inst_72_);
return v_res_75_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(lean_object* v___x_76_, lean_object* v_fvarIdToPos_77_, lean_object* v_fvarId_u2081_78_, lean_object* v_fvarId_u2082_79_){
_start:
{
lean_object* v_pos_u2081_80_; lean_object* v_pos_u2082_81_; uint8_t v___x_82_; 
v_pos_u2081_80_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v___x_76_, v_fvarIdToPos_77_, v_fvarId_u2081_78_);
v_pos_u2082_81_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v___x_76_, v_fvarIdToPos_77_, v_fvarId_u2082_79_);
v___x_82_ = lean_nat_dec_lt(v_pos_u2081_80_, v_pos_u2082_81_);
lean_dec(v_pos_u2082_81_);
lean_dec(v_pos_u2081_80_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed(lean_object* v___x_83_, lean_object* v_fvarIdToPos_84_, lean_object* v_fvarId_u2081_85_, lean_object* v_fvarId_u2082_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0(v___x_83_, v_fvarIdToPos_84_, v_fvarId_u2081_85_, v_fvarId_u2082_86_);
lean_dec(v_fvarId_u2082_86_);
lean_dec(v_fvarId_u2081_85_);
lean_dec(v_fvarIdToPos_84_);
lean_dec(v___x_83_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(lean_object* v_fvarIdToPos_89_, lean_object* v_as_90_, lean_object* v_lo_91_, lean_object* v_hi_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_nat_dec_lt(v_lo_91_, v_hi_92_);
if (v___x_93_ == 0)
{
lean_dec(v_lo_91_);
lean_dec(v_fvarIdToPos_89_);
return v_as_90_;
}
else
{
lean_object* v___x_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v_fst_97_; lean_object* v_snd_98_; uint8_t v___x_99_; 
v___x_94_ = lean_unsigned_to_nat(0u);
lean_inc(v_fvarIdToPos_89_);
v___f_95_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_95_, 0, v___x_94_);
lean_closure_set(v___f_95_, 1, v_fvarIdToPos_89_);
lean_inc(v_lo_91_);
v___x_96_ = l_Array_qpartition___redArg(v_as_90_, v___f_95_, v_lo_91_, v_hi_92_);
v_fst_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_fst_97_);
v_snd_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_snd_98_);
lean_dec_ref(v___x_96_);
v___x_99_ = lean_nat_dec_le(v_hi_92_, v_fst_97_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc(v_fvarIdToPos_89_);
v___x_100_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_89_, v_snd_98_, v_lo_91_, v_fst_97_);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_fst_97_, v___x_101_);
lean_dec(v_fst_97_);
v_as_90_ = v___x_100_;
v_lo_91_ = v___x_102_;
goto _start;
}
else
{
lean_dec(v_fst_97_);
lean_dec(v_lo_91_);
lean_dec(v_fvarIdToPos_89_);
return v_snd_98_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg___boxed(lean_object* v_fvarIdToPos_104_, lean_object* v_as_105_, lean_object* v_lo_106_, lean_object* v_hi_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_104_, v_as_105_, v_lo_106_, v_hi_107_);
lean_dec(v_hi_107_);
return v_res_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_box(0);
v___x_110_ = lean_unsigned_to_nat(16u);
v___x_111_ = lean_mk_array(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__0);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_118_ = lean_box(1);
v___x_119_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__1);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(lean_object* v_e_121_, lean_object* v_fvarIdToPos_122_){
_start:
{
lean_object* v___y_124_; lean_object* v___y_125_; lean_object* v___y_126_; lean_object* v___y_127_; lean_object* v___x_131_; lean_object* v___y_133_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_s_141_; lean_object* v_fvarIds_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__2));
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt___closed__3);
v_s_141_ = l_Lean_collectFVars(v___x_140_, v_e_121_);
v_fvarIds_142_ = lean_ctor_get(v_s_141_, 2);
lean_inc_ref(v_fvarIds_142_);
lean_dec_ref(v_s_141_);
v___x_143_ = lean_array_get_size(v_fvarIds_142_);
v___x_144_ = lean_nat_dec_lt(v___x_131_, v___x_143_);
if (v___x_144_ == 0)
{
lean_dec_ref(v_fvarIds_142_);
v___y_133_ = v___x_139_;
goto v___jp_132_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v___x_143_, v___x_143_);
if (v___x_145_ == 0)
{
if (v___x_144_ == 0)
{
lean_dec_ref(v_fvarIds_142_);
v___y_133_ = v___x_139_;
goto v___jp_132_;
}
else
{
size_t v___x_146_; size_t v___x_147_; lean_object* v___x_148_; 
v___x_146_ = ((size_t)0ULL);
v___x_147_ = lean_usize_of_nat(v___x_143_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_122_, v_fvarIds_142_, v___x_146_, v___x_147_, v___x_139_);
lean_dec_ref(v_fvarIds_142_);
v___y_133_ = v___x_148_;
goto v___jp_132_;
}
}
else
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v___x_149_ = ((size_t)0ULL);
v___x_150_ = lean_usize_of_nat(v___x_143_);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__3(v_fvarIdToPos_122_, v_fvarIds_142_, v___x_149_, v___x_150_, v___x_139_);
lean_dec_ref(v_fvarIds_142_);
v___y_133_ = v___x_151_;
goto v___jp_132_;
}
}
v___jp_123_:
{
uint8_t v___x_128_; 
lean_dec(v___y_126_);
v___x_128_ = lean_nat_dec_le(v___y_127_, v___y_124_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec(v___y_124_);
lean_inc(v___y_127_);
v___x_129_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_122_, v___y_125_, v___y_127_, v___y_127_);
lean_dec(v___y_127_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_122_, v___y_125_, v___y_127_, v___y_124_);
lean_dec(v___y_124_);
return v___x_130_;
}
}
v___jp_132_:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_array_get_size(v___y_133_);
v___x_135_ = lean_nat_dec_eq(v___x_134_, v___x_131_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_sub(v___x_134_, v___x_136_);
v___x_138_ = lean_nat_dec_le(v___x_131_, v___x_137_);
if (v___x_138_ == 0)
{
lean_inc(v___x_137_);
v___y_124_ = v___x_137_;
v___y_125_ = v___y_133_;
v___y_126_ = v___x_134_;
v___y_127_ = v___x_137_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___x_137_;
v___y_125_ = v___y_133_;
v___y_126_ = v___x_134_;
v___y_127_ = v___x_131_;
goto v___jp_123_;
}
}
else
{
lean_dec(v_fvarIdToPos_122_);
return v___y_133_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(lean_object* v_00_u03b2_152_, lean_object* v_k_153_, lean_object* v_t_154_){
_start:
{
uint8_t v___x_155_; 
v___x_155_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___redArg(v_k_153_, v_t_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0___boxed(lean_object* v_00_u03b2_156_, lean_object* v_k_157_, lean_object* v_t_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__0(v_00_u03b2_156_, v_k_157_, v_t_158_);
lean_dec(v_t_158_);
lean_dec(v_k_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___redArg(lean_object* v_inst_161_, lean_object* v_msg_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_panic_fn_borrowed(v_inst_161_, v_msg_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___redArg___boxed(lean_object* v_inst_164_, lean_object* v_msg_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___redArg(v_inst_164_, v_msg_165_);
lean_dec(v_inst_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(lean_object* v_00_u03b4_167_, lean_object* v_inst_168_, lean_object* v_msg_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_panic_fn_borrowed(v_inst_168_, v_msg_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1___boxed(lean_object* v_00_u03b4_171_, lean_object* v_inst_172_, lean_object* v_msg_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1_spec__1(v_00_u03b4_171_, v_inst_172_, v_msg_173_);
lean_dec(v_inst_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(lean_object* v_00_u03b4_175_, lean_object* v_inst_176_, lean_object* v_t_177_, lean_object* v_k_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v_inst_176_, v_t_177_, v_k_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___boxed(lean_object* v_00_u03b4_180_, lean_object* v_inst_181_, lean_object* v_t_182_, lean_object* v_k_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1(v_00_u03b4_180_, v_inst_181_, v_t_182_, v_k_183_);
lean_dec(v_k_183_);
lean_dec(v_t_182_);
lean_dec(v_inst_181_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(lean_object* v_fvarIdToPos_185_, lean_object* v_n_186_, lean_object* v_as_187_, lean_object* v_lo_188_, lean_object* v_hi_189_, lean_object* v_w_190_, lean_object* v_hlo_191_, lean_object* v_hhi_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___redArg(v_fvarIdToPos_185_, v_as_187_, v_lo_188_, v_hi_189_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2___boxed(lean_object* v_fvarIdToPos_194_, lean_object* v_n_195_, lean_object* v_as_196_, lean_object* v_lo_197_, lean_object* v_hi_198_, lean_object* v_w_199_, lean_object* v_hlo_200_, lean_object* v_hhi_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__2(v_fvarIdToPos_194_, v_n_195_, v_as_196_, v_lo_197_, v_hi_198_, v_w_199_, v_hlo_200_, v_hhi_201_);
lean_dec(v_hi_198_);
lean_dec(v_n_195_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(lean_object* v_x_203_, uint8_t v_bi_204_, lean_object* v_t_205_, lean_object* v_b_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___y_215_; lean_object* v___x_218_; uint8_t v_debug_219_; 
v___x_218_ = lean_st_ref_get(v___y_208_);
v_debug_219_ = lean_ctor_get_uint8(v___x_218_, sizeof(void*)*9);
lean_dec(v___x_218_);
if (v_debug_219_ == 0)
{
v___y_215_ = v___y_208_;
goto v___jp_214_;
}
else
{
lean_object* v___x_220_; 
lean_inc_ref(v_t_205_);
v___x_220_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_205_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
lean_dec_ref(v___x_220_);
lean_inc_ref(v_b_206_);
v___x_221_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_dec_ref(v___x_221_);
v___y_215_ = v___y_208_;
goto v___jp_214_;
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_b_206_);
lean_dec_ref(v_t_205_);
lean_dec(v_x_203_);
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v_b_206_);
lean_dec_ref(v_t_205_);
lean_dec(v_x_203_);
v_a_230_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_220_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_220_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
v___jp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_Lean_Expr_forallE___override(v_x_203_, v_t_205_, v_b_206_, v_bi_204_);
v___x_217_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_216_, v___y_215_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0___boxed(lean_object* v_x_238_, lean_object* v_bi_239_, lean_object* v_t_240_, lean_object* v_b_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
uint8_t v_bi_boxed_249_; lean_object* v_res_250_; 
v_bi_boxed_249_ = lean_unbox(v_bi_239_);
v_res_250_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v_x_238_, v_bi_boxed_249_, v_t_240_, v_b_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(lean_object* v_00_u03b1s_254_, lean_object* v_i_255_, lean_object* v_00_u03b2_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_zero_264_; uint8_t v_isZero_265_; 
v_zero_264_ = lean_unsigned_to_nat(0u);
v_isZero_265_ = lean_nat_dec_eq(v_i_255_, v_zero_264_);
if (v_isZero_265_ == 1)
{
lean_object* v___x_266_; 
lean_dec(v_i_255_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v_00_u03b2_256_);
return v___x_266_;
}
else
{
lean_object* v_one_267_; lean_object* v_n_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_one_267_ = lean_unsigned_to_nat(1u);
v_n_268_ = lean_nat_sub(v_i_255_, v_one_267_);
lean_dec(v_i_255_);
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___closed__1));
v___x_270_ = 0;
v___x_271_ = lean_array_fget_borrowed(v_00_u03b1s_254_, v_n_268_);
lean_inc(v___x_271_);
v___x_272_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go_spec__0(v___x_269_, v___x_270_, v___x_271_, v_00_u03b2_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_272_);
v_i_255_ = v_n_268_;
v_00_u03b2_256_ = v_a_273_;
goto _start;
}
else
{
lean_dec(v_n_268_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg___boxed(lean_object* v_00_u03b1s_275_, lean_object* v_i_276_, lean_object* v_00_u03b2_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_275_, v_i_276_, v_00_u03b2_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec_ref(v_00_u03b1s_275_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(lean_object* v_00_u03b1s_286_, lean_object* v_i_287_, lean_object* v_00_u03b2_288_, lean_object* v_h_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_286_, v_i_287_, v_00_u03b2_288_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___boxed(lean_object* v_00_u03b1s_298_, lean_object* v_i_299_, lean_object* v_00_u03b2_300_, lean_object* v_h_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go(v_00_u03b1s_298_, v_i_299_, v_00_u03b2_300_, v_h_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_00_u03b1s_298_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(lean_object* v_00_u03b1s_310_, lean_object* v_00_u03b2_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_array_get_size(v_00_u03b1s_310_);
v___x_320_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows_go___redArg(v_00_u03b1s_310_, v___x_319_, v_00_u03b2_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows___boxed(lean_object* v_00_u03b1s_321_, lean_object* v_00_u03b2_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_00_u03b1s_321_, v_00_u03b2_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec_ref(v_00_u03b1s_321_);
return v_res_330_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(lean_object* v_msg_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_6003__overap_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___closed__0);
v___x_6003__overap_341_ = lean_panic_fn_borrowed(v___x_340_, v_msg_332_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
lean_inc(v___y_334_);
lean_inc_ref(v___y_333_);
v___x_342_ = lean_apply_7(v___x_6003__overap_341_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, lean_box(0));
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5___boxed(lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v_msg_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(lean_object* v_fvarIdToPos_352_, lean_object* v_subst_353_, size_t v_sz_354_, size_t v_i_355_, lean_object* v_bs_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_lt(v_i_355_, v_sz_354_);
if (v___x_357_ == 0)
{
return v_bs_356_;
}
else
{
lean_object* v_v_358_; lean_object* v___x_359_; lean_object* v_bs_x27_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v___x_366_; 
v_v_358_ = lean_array_uget(v_bs_356_, v_i_355_);
v___x_359_ = lean_unsigned_to_nat(0u);
v_bs_x27_360_ = lean_array_uset(v_bs_356_, v_i_355_, v___x_359_);
v___x_361_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt_spec__1___redArg(v___x_359_, v_fvarIdToPos_352_, v_v_358_);
lean_dec(v_v_358_);
v___x_362_ = l_Lean_instInhabitedExpr;
v___x_363_ = lean_array_get_borrowed(v___x_362_, v_subst_353_, v___x_361_);
lean_dec(v___x_361_);
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_355_, v___x_364_);
lean_inc(v___x_363_);
v___x_366_ = lean_array_uset(v_bs_x27_360_, v_i_355_, v___x_363_);
v_i_355_ = v___x_365_;
v_bs_356_ = v___x_366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3___boxed(lean_object* v_fvarIdToPos_368_, lean_object* v_subst_369_, lean_object* v_sz_370_, lean_object* v_i_371_, lean_object* v_bs_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_370_);
lean_dec(v_sz_370_);
v_i_boxed_374_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_368_, v_subst_369_, v_sz_boxed_373_, v_i_boxed_374_, v_bs_372_);
lean_dec_ref(v_subst_369_);
lean_dec(v_fvarIdToPos_368_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(size_t v_sz_376_, size_t v_i_377_, lean_object* v_bs_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_usize_dec_lt(v_i_377_, v_sz_376_);
if (v___x_379_ == 0)
{
return v_bs_378_;
}
else
{
lean_object* v_v_380_; lean_object* v___x_381_; lean_object* v_bs_x27_382_; lean_object* v___x_383_; size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v_v_380_ = lean_array_uget(v_bs_378_, v_i_377_);
v___x_381_ = lean_unsigned_to_nat(0u);
v_bs_x27_382_ = lean_array_uset(v_bs_378_, v_i_377_, v___x_381_);
v___x_383_ = l_Lean_mkFVar(v_v_380_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_377_, v___x_384_);
v___x_386_ = lean_array_uset(v_bs_x27_382_, v_i_377_, v___x_383_);
v_i_377_ = v___x_385_;
v_bs_378_ = v___x_386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2___boxed(lean_object* v_sz_388_, lean_object* v_i_389_, lean_object* v_bs_390_){
_start:
{
size_t v_sz_boxed_391_; size_t v_i_boxed_392_; lean_object* v_res_393_; 
v_sz_boxed_391_ = lean_unbox_usize(v_sz_388_);
lean_dec(v_sz_388_);
v_i_boxed_392_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_boxed_391_, v_i_boxed_392_, v_bs_390_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(lean_object* v_k_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v_b_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___x_403_; 
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v___y_399_);
lean_inc_ref(v___y_398_);
lean_inc(v___y_396_);
lean_inc_ref(v___y_395_);
v___x_403_ = lean_apply_8(v_k_394_, v_b_397_, v___y_395_, v___y_396_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, lean_box(0));
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v_k_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v_b_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0(v_k_404_, v___y_405_, v___y_406_, v_b_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(lean_object* v_name_414_, uint8_t v_bi_415_, lean_object* v_type_416_, lean_object* v_k_417_, uint8_t v_kind_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___f_426_; lean_object* v___x_427_; 
lean_inc(v___y_420_);
lean_inc_ref(v___y_419_);
v___f_426_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_426_, 0, v_k_417_);
lean_closure_set(v___f_426_, 1, v___y_419_);
lean_closure_set(v___f_426_, 2, v___y_420_);
v___x_427_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_414_, v_bi_415_, v_type_416_, v___f_426_, v_kind_418_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_427_) == 0)
{
return v___x_427_;
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___boxed(lean_object* v_name_436_, lean_object* v_bi_437_, lean_object* v_type_438_, lean_object* v_k_439_, lean_object* v_kind_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v_bi_boxed_448_; uint8_t v_kind_boxed_449_; lean_object* v_res_450_; 
v_bi_boxed_448_ = lean_unbox(v_bi_437_);
v_kind_boxed_449_ = lean_unbox(v_kind_440_);
v_res_450_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_436_, v_bi_boxed_448_, v_type_438_, v_k_439_, v_kind_boxed_449_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(lean_object* v_name_451_, lean_object* v_type_452_, lean_object* v_k_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
uint8_t v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; 
v___x_461_ = 0;
v___x_462_ = 0;
v___x_463_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_451_, v___x_461_, v_type_452_, v_k_453_, v___x_462_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg___boxed(lean_object* v_name_464_, lean_object* v_type_465_, lean_object* v_k_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_464_, v_type_465_, v_k_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(lean_object* v_t_475_, lean_object* v_k_476_, lean_object* v_fallback_477_){
_start:
{
if (lean_obj_tag(v_t_475_) == 0)
{
lean_object* v_k_478_; lean_object* v_v_479_; lean_object* v_l_480_; lean_object* v_r_481_; uint8_t v___x_482_; 
v_k_478_ = lean_ctor_get(v_t_475_, 1);
v_v_479_ = lean_ctor_get(v_t_475_, 2);
v_l_480_ = lean_ctor_get(v_t_475_, 3);
v_r_481_ = lean_ctor_get(v_t_475_, 4);
v___x_482_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_476_, v_k_478_);
switch(v___x_482_)
{
case 0:
{
v_t_475_ = v_l_480_;
goto _start;
}
case 1:
{
lean_inc(v_v_479_);
return v_v_479_;
}
default: 
{
v_t_475_ = v_r_481_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_477_);
return v_fallback_477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg___boxed(lean_object* v_t_485_, lean_object* v_k_486_, lean_object* v_fallback_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_485_, v_k_486_, v_fallback_487_);
lean_dec(v_fallback_487_);
lean_dec(v_k_486_);
lean_dec(v_t_485_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(lean_object* v_fvarIdToPos_489_, size_t v_sz_490_, size_t v_i_491_, lean_object* v_bs_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_usize_dec_lt(v_i_491_, v_sz_490_);
if (v___x_493_ == 0)
{
return v_bs_492_;
}
else
{
lean_object* v_v_494_; lean_object* v___x_495_; lean_object* v_bs_x27_496_; lean_object* v___x_497_; size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v_v_494_ = lean_array_uget(v_bs_492_, v_i_491_);
v___x_495_ = lean_unsigned_to_nat(0u);
v_bs_x27_496_ = lean_array_uset(v_bs_492_, v_i_491_, v___x_495_);
v___x_497_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_fvarIdToPos_489_, v_v_494_, v___x_495_);
lean_dec(v_v_494_);
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_491_, v___x_498_);
v___x_500_ = lean_array_uset(v_bs_x27_496_, v_i_491_, v___x_497_);
v_i_491_ = v___x_499_;
v_bs_492_ = v___x_500_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1___boxed(lean_object* v_fvarIdToPos_502_, lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_bs_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_507_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_502_, v_sz_boxed_506_, v_i_boxed_507_, v_bs_505_);
lean_dec(v_fvarIdToPos_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed(lean_object** _args){
lean_object* v_fvarIdToPos_518_ = _args[0];
lean_object* v_subst_519_ = _args[1];
lean_object* v_sz_520_ = _args[2];
lean_object* v___x_521_ = _args[3];
lean_object* v_fvarIds_522_ = _args[4];
lean_object* v_x_523_ = _args[5];
lean_object* v_xs_524_ = _args[6];
lean_object* v_xs_x27_525_ = _args[7];
lean_object* v_args_526_ = _args[8];
lean_object* v_a_527_ = _args[9];
lean_object* v_types_528_ = _args[10];
lean_object* v_a_529_ = _args[11];
lean_object* v_varDeps_530_ = _args[12];
lean_object* v_varPos_531_ = _args[13];
lean_object* v_haveExpr_532_ = _args[14];
lean_object* v_body_533_ = _args[15];
lean_object* v_x_x27_534_ = _args[16];
lean_object* v___y_535_ = _args[17];
lean_object* v___y_536_ = _args[18];
lean_object* v___y_537_ = _args[19];
lean_object* v___y_538_ = _args[20];
lean_object* v___y_539_ = _args[21];
lean_object* v___y_540_ = _args[22];
lean_object* v___y_541_ = _args[23];
_start:
{
size_t v_sz_boxed_542_; size_t v___x_7252__boxed_543_; lean_object* v_res_544_; 
v_sz_boxed_542_ = lean_unbox_usize(v_sz_520_);
lean_dec(v_sz_520_);
v___x_7252__boxed_543_ = lean_unbox_usize(v___x_521_);
lean_dec(v___x_521_);
v_res_544_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(v_fvarIdToPos_518_, v_subst_519_, v_sz_boxed_542_, v___x_7252__boxed_543_, v_fvarIds_522_, v_x_523_, v_xs_524_, v_xs_x27_525_, v_args_526_, v_a_527_, v_types_528_, v_a_529_, v_varDeps_530_, v_varPos_531_, v_haveExpr_532_, v_body_533_, v_x_x27_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(lean_object* v_value_545_, lean_object* v_xs_546_, lean_object* v_fvarIdToPos_547_, uint8_t v___x_548_, uint8_t v_nondep_549_, lean_object* v_type_550_, lean_object* v_subst_551_, lean_object* v_xs_x27_552_, lean_object* v_args_553_, lean_object* v_types_554_, lean_object* v_varDeps_555_, lean_object* v_haveExpr_556_, lean_object* v_body_557_, lean_object* v_declName_558_, lean_object* v_x_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_v_567_; lean_object* v_fvarIds_568_; size_t v_sz_569_; size_t v___x_570_; lean_object* v_varPos_571_; lean_object* v_ys_572_; uint8_t v___x_573_; lean_object* v___x_574_; 
v_v_567_ = lean_expr_instantiate_rev(v_value_545_, v_xs_546_);
lean_inc(v_fvarIdToPos_547_);
lean_inc_ref(v_v_567_);
v_fvarIds_568_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_collectFVarIdsAt(v_v_567_, v_fvarIdToPos_547_);
v_sz_569_ = lean_array_size(v_fvarIds_568_);
v___x_570_ = ((size_t)0ULL);
lean_inc_ref(v_fvarIds_568_);
v_varPos_571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__1(v_fvarIdToPos_547_, v_sz_569_, v___x_570_, v_fvarIds_568_);
lean_inc_ref(v_fvarIds_568_);
v_ys_572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__2(v_sz_569_, v___x_570_, v_fvarIds_568_);
v___x_573_ = 1;
v___x_574_ = l_Lean_Meta_mkLambdaFVars(v_ys_572_, v_v_567_, v___x_548_, v_nondep_549_, v___x_548_, v_nondep_549_, v___x_573_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_Lean_Meta_mkForallFVars(v_ys_572_, v_type_550_, v___x_548_, v_nondep_549_, v_nondep_549_, v___x_573_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec_ref(v_ys_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
lean_dec_ref(v___x_576_);
v___x_578_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_577_, v___y_561_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___f_582_; lean_object* v___x_583_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v___x_580_ = lean_box_usize(v_sz_569_);
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed__const__1));
lean_inc(v_a_579_);
v___f_582_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0___boxed), 24, 16);
lean_closure_set(v___f_582_, 0, v_fvarIdToPos_547_);
lean_closure_set(v___f_582_, 1, v_subst_551_);
lean_closure_set(v___f_582_, 2, v___x_580_);
lean_closure_set(v___f_582_, 3, v___x_581_);
lean_closure_set(v___f_582_, 4, v_fvarIds_568_);
lean_closure_set(v___f_582_, 5, v_x_559_);
lean_closure_set(v___f_582_, 6, v_xs_546_);
lean_closure_set(v___f_582_, 7, v_xs_x27_552_);
lean_closure_set(v___f_582_, 8, v_args_553_);
lean_closure_set(v___f_582_, 9, v_a_575_);
lean_closure_set(v___f_582_, 10, v_types_554_);
lean_closure_set(v___f_582_, 11, v_a_579_);
lean_closure_set(v___f_582_, 12, v_varDeps_555_);
lean_closure_set(v___f_582_, 13, v_varPos_571_);
lean_closure_set(v___f_582_, 14, v_haveExpr_556_);
lean_closure_set(v___f_582_, 15, v_body_557_);
v___x_583_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_558_, v_a_579_, v___f_582_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_583_;
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_a_575_);
lean_dec_ref(v_varPos_571_);
lean_dec_ref(v_fvarIds_568_);
lean_dec_ref(v_x_559_);
lean_dec(v_declName_558_);
lean_dec_ref(v_body_557_);
lean_dec_ref(v_haveExpr_556_);
lean_dec_ref(v_varDeps_555_);
lean_dec_ref(v_types_554_);
lean_dec_ref(v_args_553_);
lean_dec_ref(v_xs_x27_552_);
lean_dec_ref(v_subst_551_);
lean_dec(v_fvarIdToPos_547_);
lean_dec_ref(v_xs_546_);
v_a_584_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_578_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_578_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_575_);
lean_dec_ref(v_varPos_571_);
lean_dec_ref(v_fvarIds_568_);
lean_dec_ref(v_x_559_);
lean_dec(v_declName_558_);
lean_dec_ref(v_body_557_);
lean_dec_ref(v_haveExpr_556_);
lean_dec_ref(v_varDeps_555_);
lean_dec_ref(v_types_554_);
lean_dec_ref(v_args_553_);
lean_dec_ref(v_xs_x27_552_);
lean_dec_ref(v_subst_551_);
lean_dec(v_fvarIdToPos_547_);
lean_dec_ref(v_xs_546_);
v_a_592_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_576_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_576_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v_ys_572_);
lean_dec_ref(v_varPos_571_);
lean_dec_ref(v_fvarIds_568_);
lean_dec_ref(v_x_559_);
lean_dec(v_declName_558_);
lean_dec_ref(v_body_557_);
lean_dec_ref(v_haveExpr_556_);
lean_dec_ref(v_varDeps_555_);
lean_dec_ref(v_types_554_);
lean_dec_ref(v_args_553_);
lean_dec_ref(v_xs_x27_552_);
lean_dec_ref(v_subst_551_);
lean_dec_ref(v_type_550_);
lean_dec(v_fvarIdToPos_547_);
lean_dec_ref(v_xs_546_);
v_a_600_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_574_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_574_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed(lean_object** _args){
lean_object* v_value_608_ = _args[0];
lean_object* v_xs_609_ = _args[1];
lean_object* v_fvarIdToPos_610_ = _args[2];
lean_object* v___x_611_ = _args[3];
lean_object* v_nondep_612_ = _args[4];
lean_object* v_type_613_ = _args[5];
lean_object* v_subst_614_ = _args[6];
lean_object* v_xs_x27_615_ = _args[7];
lean_object* v_args_616_ = _args[8];
lean_object* v_types_617_ = _args[9];
lean_object* v_varDeps_618_ = _args[10];
lean_object* v_haveExpr_619_ = _args[11];
lean_object* v_body_620_ = _args[12];
lean_object* v_declName_621_ = _args[13];
lean_object* v_x_622_ = _args[14];
lean_object* v___y_623_ = _args[15];
lean_object* v___y_624_ = _args[16];
lean_object* v___y_625_ = _args[17];
lean_object* v___y_626_ = _args[18];
lean_object* v___y_627_ = _args[19];
lean_object* v___y_628_ = _args[20];
lean_object* v___y_629_ = _args[21];
_start:
{
uint8_t v___x_7280__boxed_630_; uint8_t v_nondep_7281__boxed_631_; lean_object* v_res_632_; 
v___x_7280__boxed_630_ = lean_unbox(v___x_611_);
v_nondep_7281__boxed_631_ = lean_unbox(v_nondep_612_);
v_res_632_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1(v_value_608_, v_xs_609_, v_fvarIdToPos_610_, v___x_7280__boxed_630_, v_nondep_7281__boxed_631_, v_type_613_, v_subst_614_, v_xs_x27_615_, v_args_616_, v_types_617_, v_varDeps_618_, v_haveExpr_619_, v_body_620_, v_declName_621_, v_x_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec_ref(v_value_608_);
return v_res_632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_636_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__6));
v___x_637_ = lean_unsigned_to_nat(6u);
v___x_638_ = lean_unsigned_to_nat(168u);
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__5));
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_641_ = l_mkPanicMessageWithDecl(v___x_640_, v___x_639_, v___x_638_, v___x_637_, v___x_636_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(lean_object* v_haveExpr_642_, lean_object* v_e_643_, lean_object* v_xs_644_, lean_object* v_xs_x27_645_, lean_object* v_args_646_, lean_object* v_subst_647_, lean_object* v_types_648_, lean_object* v_varDeps_649_, lean_object* v_fvarIdToPos_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; 
if (lean_obj_tag(v_e_643_) == 8)
{
uint8_t v_nondep_745_; 
v_nondep_745_ = lean_ctor_get_uint8(v_e_643_, sizeof(void*)*4 + 8);
if (v_nondep_745_ == 1)
{
lean_object* v_declName_746_; lean_object* v_type_747_; lean_object* v_value_748_; lean_object* v_body_749_; uint8_t v___x_750_; 
v_declName_746_ = lean_ctor_get(v_e_643_, 0);
lean_inc(v_declName_746_);
v_type_747_ = lean_ctor_get(v_e_643_, 1);
lean_inc_ref(v_type_747_);
v_value_748_ = lean_ctor_get(v_e_643_, 2);
lean_inc_ref(v_value_748_);
v_body_749_ = lean_ctor_get(v_e_643_, 3);
lean_inc_ref(v_body_749_);
lean_dec_ref(v_e_643_);
v___x_750_ = l_Lean_Expr_hasLooseBVars(v_type_747_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___x_754_; 
v___x_751_ = lean_box(v___x_750_);
v___x_752_ = lean_box(v_nondep_745_);
lean_inc(v_declName_746_);
lean_inc_ref(v_type_747_);
v___f_753_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__1___boxed), 22, 14);
lean_closure_set(v___f_753_, 0, v_value_748_);
lean_closure_set(v___f_753_, 1, v_xs_644_);
lean_closure_set(v___f_753_, 2, v_fvarIdToPos_650_);
lean_closure_set(v___f_753_, 3, v___x_751_);
lean_closure_set(v___f_753_, 4, v___x_752_);
lean_closure_set(v___f_753_, 5, v_type_747_);
lean_closure_set(v___f_753_, 6, v_subst_647_);
lean_closure_set(v___f_753_, 7, v_xs_x27_645_);
lean_closure_set(v___f_753_, 8, v_args_646_);
lean_closure_set(v___f_753_, 9, v_types_648_);
lean_closure_set(v___f_753_, 10, v_varDeps_649_);
lean_closure_set(v___f_753_, 11, v_haveExpr_642_);
lean_closure_set(v___f_753_, 12, v_body_749_);
lean_closure_set(v___f_753_, 13, v_declName_746_);
v___x_754_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_declName_746_, v_type_747_, v___f_753_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
return v___x_754_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec_ref(v_body_749_);
lean_dec_ref(v_value_748_);
lean_dec_ref(v_type_747_);
lean_dec(v_declName_746_);
lean_dec(v_fvarIdToPos_650_);
lean_dec_ref(v_varDeps_649_);
lean_dec_ref(v_types_648_);
lean_dec_ref(v_subst_647_);
lean_dec_ref(v_args_646_);
lean_dec_ref(v_xs_x27_645_);
lean_dec_ref(v_xs_644_);
lean_dec_ref(v_haveExpr_642_);
v___x_755_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__7);
v___x_756_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__5(v___x_755_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
return v___x_756_;
}
}
else
{
lean_dec(v_fvarIdToPos_650_);
lean_dec_ref(v_xs_644_);
v___y_659_ = v_a_651_;
v___y_660_ = v_a_652_;
v___y_661_ = v_a_653_;
v___y_662_ = v_a_654_;
v___y_663_ = v_a_655_;
v___y_664_ = v_a_656_;
goto v___jp_658_;
}
}
else
{
lean_dec(v_fvarIdToPos_650_);
lean_dec_ref(v_xs_644_);
v___y_659_ = v_a_651_;
v___y_660_ = v_a_652_;
v___y_661_ = v_a_653_;
v___y_662_ = v_a_654_;
v___y_663_ = v_a_655_;
v___y_664_ = v_a_656_;
goto v___jp_658_;
}
v___jp_658_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_array_get_size(v_subst_647_);
v___x_667_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_643_, v___x_665_, v___x_666_, v_subst_647_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec_ref(v_subst_647_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v___x_667_);
lean_inc(v_a_668_);
v___x_669_ = l_Lean_Meta_Sym_inferType___redArg(v_a_668_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref(v___x_669_);
lean_inc(v_a_670_);
v___x_671_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_670_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref(v___x_671_);
lean_inc(v_a_670_);
v___x_673_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_mkArrows(v_types_648_, v_a_670_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec_ref(v_types_648_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_673_);
v___x_675_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_x27_645_, v_a_668_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec_ref(v_xs_x27_645_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v___x_675_);
v___x_677_ = l_Lean_mkAppN(v_a_676_, v_args_646_);
lean_dec_ref(v_args_646_);
v___x_678_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_677_, v___y_660_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_696_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_696_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_696_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_696_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
v___x_684_ = lean_box(0);
lean_inc(v_a_672_);
v___x_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_685_, 0, v_a_672_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
lean_inc_ref(v___x_685_);
v___x_686_ = l_Lean_mkConst(v___x_683_, v___x_685_);
lean_inc(v_a_679_);
lean_inc_ref(v_haveExpr_642_);
lean_inc(v_a_670_);
v___x_687_ = l_Lean_mkApp3(v___x_686_, v_a_670_, v_haveExpr_642_, v_a_679_);
v___x_688_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_689_ = l_Lean_mkConst(v___x_688_, v___x_685_);
lean_inc(v_a_670_);
v___x_690_ = l_Lean_mkAppB(v___x_689_, v_a_670_, v_haveExpr_642_);
v___x_691_ = l_Lean_Meta_mkExpectedPropHint(v___x_690_, v___x_687_);
v___x_692_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_692_, 0, v_a_670_);
lean_ctor_set(v___x_692_, 1, v_a_672_);
lean_ctor_set(v___x_692_, 2, v_a_679_);
lean_ctor_set(v___x_692_, 3, v___x_691_);
lean_ctor_set(v___x_692_, 4, v_varDeps_649_);
lean_ctor_set(v___x_692_, 5, v_a_674_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_692_);
v___x_694_ = v___x_681_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_a_674_);
lean_dec(v_a_672_);
lean_dec(v_a_670_);
lean_dec_ref(v_varDeps_649_);
lean_dec_ref(v_haveExpr_642_);
v_a_697_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_678_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_678_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_a_674_);
lean_dec(v_a_672_);
lean_dec(v_a_670_);
lean_dec_ref(v_varDeps_649_);
lean_dec_ref(v_args_646_);
lean_dec_ref(v_haveExpr_642_);
v_a_705_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_675_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_675_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_a_672_);
lean_dec(v_a_670_);
lean_dec(v_a_668_);
lean_dec_ref(v_varDeps_649_);
lean_dec_ref(v_args_646_);
lean_dec_ref(v_xs_x27_645_);
lean_dec_ref(v_haveExpr_642_);
v_a_713_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_673_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_673_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v_a_670_);
lean_dec(v_a_668_);
lean_dec_ref(v_varDeps_649_);
lean_dec_ref(v_types_648_);
lean_dec_ref(v_args_646_);
lean_dec_ref(v_xs_x27_645_);
lean_dec_ref(v_haveExpr_642_);
v_a_721_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_671_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_671_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v_a_668_);
lean_dec_ref(v_varDeps_649_);
lean_dec_ref(v_types_648_);
lean_dec_ref(v_args_646_);
lean_dec_ref(v_xs_x27_645_);
lean_dec_ref(v_haveExpr_642_);
v_a_729_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_669_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_669_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v_varDeps_649_);
lean_dec_ref(v_types_648_);
lean_dec_ref(v_args_646_);
lean_dec_ref(v_xs_x27_645_);
lean_dec_ref(v_haveExpr_642_);
v_a_737_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_667_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_667_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___lam__0(lean_object* v_fvarIdToPos_757_, lean_object* v_subst_758_, size_t v_sz_759_, size_t v___x_760_, lean_object* v_fvarIds_761_, lean_object* v_x_762_, lean_object* v_xs_763_, lean_object* v_xs_x27_764_, lean_object* v_args_765_, lean_object* v_a_766_, lean_object* v_types_767_, lean_object* v_a_768_, lean_object* v_varDeps_769_, lean_object* v_varPos_770_, lean_object* v_haveExpr_771_, lean_object* v_body_772_, lean_object* v_x_x27_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__3(v_fvarIdToPos_757_, v_subst_758_, v_sz_759_, v___x_760_, v_fvarIds_761_);
lean_inc_ref(v_x_x27_773_);
v___x_782_ = l_Lean_mkAppN(v_x_x27_773_, v___x_781_);
lean_dec_ref(v___x_781_);
v___x_783_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_782_, v___y_775_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = l_Lean_Expr_fvarId_x21(v_x_762_);
v___x_786_ = lean_array_get_size(v_xs_763_);
v___x_787_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_785_, v___x_786_, v_fvarIdToPos_757_);
v___x_788_ = lean_array_push(v_xs_763_, v_x_762_);
v___x_789_ = lean_array_push(v_xs_x27_764_, v_x_x27_773_);
v___x_790_ = lean_array_push(v_args_765_, v_a_766_);
v___x_791_ = lean_array_push(v_subst_758_, v_a_784_);
v___x_792_ = lean_array_push(v_types_767_, v_a_768_);
v___x_793_ = lean_array_push(v_varDeps_769_, v_varPos_770_);
v___x_794_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_771_, v_body_772_, v___x_788_, v___x_789_, v___x_790_, v___x_791_, v___x_792_, v___x_793_, v___x_787_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
return v___x_794_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_x_x27_773_);
lean_dec_ref(v_body_772_);
lean_dec_ref(v_haveExpr_771_);
lean_dec_ref(v_varPos_770_);
lean_dec_ref(v_varDeps_769_);
lean_dec_ref(v_a_768_);
lean_dec_ref(v_types_767_);
lean_dec_ref(v_a_766_);
lean_dec_ref(v_args_765_);
lean_dec_ref(v_xs_x27_764_);
lean_dec_ref(v_xs_763_);
lean_dec_ref(v_x_762_);
lean_dec_ref(v_subst_758_);
lean_dec(v_fvarIdToPos_757_);
v_a_795_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_783_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_783_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___boxed(lean_object* v_haveExpr_803_, lean_object* v_e_804_, lean_object* v_xs_805_, lean_object* v_xs_x27_806_, lean_object* v_args_807_, lean_object* v_subst_808_, lean_object* v_types_809_, lean_object* v_varDeps_810_, lean_object* v_fvarIdToPos_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_803_, v_e_804_, v_xs_805_, v_xs_x27_806_, v_args_807_, v_subst_808_, v_types_809_, v_varDeps_810_, v_fvarIdToPos_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(lean_object* v_00_u03b4_820_, lean_object* v_t_821_, lean_object* v_k_822_, lean_object* v_fallback_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___redArg(v_t_821_, v_k_822_, v_fallback_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0___boxed(lean_object* v_00_u03b4_825_, lean_object* v_t_826_, lean_object* v_k_827_, lean_object* v_fallback_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__0(v_00_u03b4_825_, v_t_826_, v_k_827_, v_fallback_828_);
lean_dec(v_fallback_828_);
lean_dec(v_k_827_);
lean_dec(v_t_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(lean_object* v_00_u03b1_830_, lean_object* v_name_831_, uint8_t v_bi_832_, lean_object* v_type_833_, lean_object* v_k_834_, uint8_t v_kind_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg(v_name_831_, v_bi_832_, v_type_833_, v_k_834_, v_kind_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___boxed(lean_object* v_00_u03b1_844_, lean_object* v_name_845_, lean_object* v_bi_846_, lean_object* v_type_847_, lean_object* v_k_848_, lean_object* v_kind_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v_bi_boxed_857_; uint8_t v_kind_boxed_858_; lean_object* v_res_859_; 
v_bi_boxed_857_ = lean_unbox(v_bi_846_);
v_kind_boxed_858_ = lean_unbox(v_kind_849_);
v_res_859_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4(v_00_u03b1_844_, v_name_845_, v_bi_boxed_857_, v_type_847_, v_k_848_, v_kind_boxed_858_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(lean_object* v_00_u03b1_860_, lean_object* v_name_861_, lean_object* v_type_862_, lean_object* v_k_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___redArg(v_name_861_, v_type_862_, v_k_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4___boxed(lean_object* v_00_u03b1_872_, lean_object* v_name_873_, lean_object* v_type_874_, lean_object* v_k_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4(v_00_u03b1_872_, v_name_873_, v_type_874_, v_k_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object* v_haveExpr_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_895_ = lean_box(1);
lean_inc_ref(v_haveExpr_886_);
v___x_896_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go(v_haveExpr_886_, v_haveExpr_886_, v___x_894_, v___x_894_, v___x_894_, v___x_894_, v___x_894_, v___x_894_, v___x_895_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_toBetaApp___boxed(lean_object* v_haveExpr_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_haveExpr_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(lean_object* v_type_906_, lean_object* v_n_907_){
_start:
{
lean_object* v_zero_908_; uint8_t v_isZero_909_; 
v_zero_908_ = lean_unsigned_to_nat(0u);
v_isZero_909_ = lean_nat_dec_eq(v_n_907_, v_zero_908_);
if (v_isZero_909_ == 1)
{
lean_dec(v_n_907_);
return v_type_906_;
}
else
{
lean_object* v_one_910_; lean_object* v_n_911_; lean_object* v___x_912_; 
v_one_910_ = lean_unsigned_to_nat(1u);
v_n_911_ = lean_nat_sub(v_n_907_, v_one_910_);
lean_dec(v_n_907_);
v___x_912_ = l_Lean_Expr_bindingBody_x21(v_type_906_);
lean_dec_ref(v_type_906_);
v_type_906_ = v___x_912_;
v_n_907_ = v_n_911_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0(void){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_914_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__0);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_object* v_00_u03b2_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0___closed__1);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(lean_object* v_idx_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = l_Lean_Expr_bvar___override(v_idx_919_);
v___x_922_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_921_, v___y_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(lean_object* v_idx_923_, uint8_t v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v_idx_923_, v___y_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___boxed(lean_object* v_idx_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v___y_21805__boxed_930_; lean_object* v_res_931_; 
v___y_21805__boxed_930_ = lean_unbox(v___y_928_);
v_res_931_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1(v_idx_927_, v___y_21805__boxed_930_, v___y_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(lean_object* v_msg_939_, uint8_t v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___f_942_; lean_object* v___f_943_; lean_object* v___f_944_; lean_object* v___f_945_; lean_object* v___f_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___f_952_; lean_object* v___f_953_; lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___f_964_; lean_object* v___x_1735__overap_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___f_942_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_943_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_944_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_945_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_946_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_947_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_948_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___f_942_);
lean_ctor_set(v___x_949_, 1, v___f_943_);
v___x_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___f_944_);
lean_ctor_set(v___x_950_, 2, v___f_945_);
lean_ctor_set(v___x_950_, 3, v___f_946_);
lean_ctor_set(v___x_950_, 4, v___f_947_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___f_948_);
lean_inc_ref(v___x_951_);
v___f_952_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_952_, 0, v___x_951_);
lean_inc_ref(v___x_951_);
v___f_953_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_953_, 0, v___x_951_);
lean_inc_ref(v___x_951_);
v___f_954_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_954_, 0, v___x_951_);
lean_inc_ref(v___x_951_);
v___f_955_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_955_, 0, v___x_951_);
lean_inc_ref(v___x_951_);
v___x_956_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_956_, 0, lean_box(0));
lean_closure_set(v___x_956_, 1, lean_box(0));
lean_closure_set(v___x_956_, 2, v___x_951_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___f_952_);
lean_inc_ref(v___x_951_);
v___x_958_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_958_, 0, lean_box(0));
lean_closure_set(v___x_958_, 1, lean_box(0));
lean_closure_set(v___x_958_, 2, v___x_951_);
v___x_959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_ctor_set(v___x_959_, 2, v___f_953_);
lean_ctor_set(v___x_959_, 3, v___f_954_);
lean_ctor_set(v___x_959_, 4, v___f_955_);
v___x_960_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_960_, 0, lean_box(0));
lean_closure_set(v___x_960_, 1, lean_box(0));
lean_closure_set(v___x_960_, 2, v___x_951_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_box(0);
v___x_963_ = l_instInhabitedOfMonad___redArg(v___x_961_, v___x_962_);
v___f_964_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_964_, 0, v___x_963_);
v___x_1735__overap_965_ = lean_panic_fn_borrowed(v___f_964_, v_msg_939_);
lean_dec_ref(v___f_964_);
v___x_966_ = lean_box(v___y_940_);
v___x_967_ = lean_apply_2(v___x_1735__overap_965_, v___x_966_, v___y_941_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___boxed(lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___y_21827__boxed_971_; lean_object* v_res_972_; 
v___y_21827__boxed_971_ = lean_unbox(v___y_969_);
v_res_972_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v_msg_968_, v___y_21827__boxed_971_, v___y_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(lean_object* v_structName_973_, lean_object* v_idx_974_, lean_object* v_struct_975_, lean_object* v___y_976_, uint8_t v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___y_980_; lean_object* v___y_981_; 
if (v___y_977_ == 0)
{
v___y_980_ = v___y_976_;
v___y_981_ = v___y_978_;
goto v___jp_979_;
}
else
{
lean_object* v___x_994_; lean_object* v_snd_995_; 
lean_inc_ref(v_struct_975_);
v___x_994_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_975_, v___y_977_, v___y_978_);
v_snd_995_ = lean_ctor_get(v___x_994_, 1);
lean_inc(v_snd_995_);
lean_dec_ref(v___x_994_);
v___y_980_ = v___y_976_;
v___y_981_ = v_snd_995_;
goto v___jp_979_;
}
v___jp_979_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_fst_984_; lean_object* v_snd_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v___x_982_ = l_Lean_Expr_proj___override(v_structName_973_, v_idx_974_, v_struct_975_);
v___x_983_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_982_, v___y_981_);
v_fst_984_ = lean_ctor_get(v___x_983_, 0);
v_snd_985_ = lean_ctor_get(v___x_983_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_993_ == 0)
{
v___x_987_ = v___x_983_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snd_985_);
lean_inc(v_fst_984_);
lean_dec(v___x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___y_980_);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_fst_984_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___y_980_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v_snd_985_);
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9___boxed(lean_object* v_structName_996_, lean_object* v_idx_997_, lean_object* v_struct_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v___y_21891__boxed_1002_; lean_object* v_res_1003_; 
v___y_21891__boxed_1002_ = lean_unbox(v___y_1000_);
v_res_1003_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_structName_996_, v_idx_997_, v_struct_998_, v___y_999_, v___y_21891__boxed_1002_, v___y_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(lean_object* v_x_1004_, uint8_t v_bi_1005_, lean_object* v_t_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, uint8_t v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___y_1012_; lean_object* v___y_1013_; 
if (v___y_1009_ == 0)
{
v___y_1012_ = v___y_1008_;
v___y_1013_ = v___y_1010_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1026_; lean_object* v_snd_1027_; lean_object* v___x_1028_; lean_object* v_snd_1029_; 
lean_inc_ref(v_t_1006_);
v___x_1026_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1006_, v___y_1009_, v___y_1010_);
v_snd_1027_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_snd_1027_);
lean_dec_ref(v___x_1026_);
lean_inc_ref(v_b_1007_);
v___x_1028_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1007_, v___y_1009_, v_snd_1027_);
v_snd_1029_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_snd_1029_);
lean_dec_ref(v___x_1028_);
v___y_1012_ = v___y_1008_;
v___y_1013_ = v_snd_1029_;
goto v___jp_1011_;
}
v___jp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1025_; 
v___x_1014_ = l_Lean_Expr_lam___override(v_x_1004_, v_t_1006_, v_b_1007_, v_bi_1005_);
v___x_1015_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1014_, v___y_1013_);
v_fst_1016_ = lean_ctor_get(v___x_1015_, 0);
v_snd_1017_ = lean_ctor_get(v___x_1015_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1019_ = v___x_1015_;
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_snd_1017_);
lean_inc(v_fst_1016_);
lean_dec(v___x_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v___y_1012_);
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_fst_1016_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___y_1012_);
v___x_1022_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_snd_1017_);
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5___boxed(lean_object* v_x_1030_, lean_object* v_bi_1031_, lean_object* v_t_1032_, lean_object* v_b_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v_bi_boxed_1037_; uint8_t v___y_21935__boxed_1038_; lean_object* v_res_1039_; 
v_bi_boxed_1037_ = lean_unbox(v_bi_1031_);
v___y_21935__boxed_1038_ = lean_unbox(v___y_1035_);
v_res_1039_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_x_1030_, v_bi_boxed_1037_, v_t_1032_, v_b_1033_, v___y_1034_, v___y_21935__boxed_1038_, v___y_1036_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(lean_object* v_msg_1040_, lean_object* v___y_1041_, uint8_t v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_21469__overap_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___f_1044_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__0));
v___f_1045_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__1));
v___f_1046_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__2));
v___f_1047_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__3));
v___f_1048_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__4));
v___f_1049_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__5));
v___f_1050_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2___closed__6));
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___f_1044_);
lean_ctor_set(v___x_1051_, 1, v___f_1045_);
v___x_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___f_1046_);
lean_ctor_set(v___x_1052_, 2, v___f_1047_);
lean_ctor_set(v___x_1052_, 3, v___f_1048_);
lean_ctor_set(v___x_1052_, 4, v___f_1049_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___f_1050_);
lean_inc_ref(v___x_1053_);
v___f_1054_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1054_, 0, v___x_1053_);
lean_inc_ref(v___x_1053_);
v___f_1055_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1055_, 0, v___x_1053_);
lean_inc_ref(v___x_1053_);
v___f_1056_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1056_, 0, v___x_1053_);
lean_inc_ref(v___x_1053_);
v___f_1057_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1057_, 0, v___x_1053_);
lean_inc_ref(v___x_1053_);
v___x_1058_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1058_, 0, lean_box(0));
lean_closure_set(v___x_1058_, 1, lean_box(0));
lean_closure_set(v___x_1058_, 2, v___x_1053_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___f_1054_);
lean_inc_ref(v___x_1053_);
v___x_1060_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1060_, 0, lean_box(0));
lean_closure_set(v___x_1060_, 1, lean_box(0));
lean_closure_set(v___x_1060_, 2, v___x_1053_);
v___x_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
lean_ctor_set(v___x_1061_, 2, v___f_1055_);
lean_ctor_set(v___x_1061_, 3, v___f_1056_);
lean_ctor_set(v___x_1061_, 4, v___f_1057_);
v___x_1062_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1062_, 0, lean_box(0));
lean_closure_set(v___x_1062_, 1, lean_box(0));
lean_closure_set(v___x_1062_, 2, v___x_1053_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = l_ReaderT_instMonad___redArg(v___x_1063_);
lean_inc_ref(v___x_1064_);
v___f_1065_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1065_, 0, v___x_1064_);
lean_inc_ref(v___x_1064_);
v___f_1066_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1066_, 0, v___x_1064_);
lean_inc_ref(v___x_1064_);
v___f_1067_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1067_, 0, v___x_1064_);
lean_inc_ref(v___x_1064_);
v___f_1068_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1068_, 0, v___x_1064_);
lean_inc_ref(v___x_1064_);
v___x_1069_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1069_, 0, lean_box(0));
lean_closure_set(v___x_1069_, 1, lean_box(0));
lean_closure_set(v___x_1069_, 2, v___x_1064_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___f_1065_);
lean_inc_ref(v___x_1064_);
v___x_1071_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1071_, 0, lean_box(0));
lean_closure_set(v___x_1071_, 1, lean_box(0));
lean_closure_set(v___x_1071_, 2, v___x_1064_);
v___x_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
lean_ctor_set(v___x_1072_, 2, v___f_1066_);
lean_ctor_set(v___x_1072_, 3, v___f_1067_);
lean_ctor_set(v___x_1072_, 4, v___f_1068_);
v___x_1073_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1073_, 0, lean_box(0));
lean_closure_set(v___x_1073_, 1, lean_box(0));
lean_closure_set(v___x_1073_, 2, v___x_1064_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_instInhabitedExpr;
v___x_1076_ = l_instInhabitedOfMonad___redArg(v___x_1074_, v___x_1075_);
v___x_21469__overap_1077_ = lean_panic_fn_borrowed(v___x_1076_, v_msg_1040_);
lean_dec(v___x_1076_);
v___x_1078_ = lean_box(v___y_1042_);
v___x_1079_ = lean_apply_3(v___x_21469__overap_1077_, v___y_1041_, v___x_1078_, v___y_1043_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10___boxed(lean_object* v_msg_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v___y_21991__boxed_1084_; lean_object* v_res_1085_; 
v___y_21991__boxed_1084_ = lean_unbox(v___y_1082_);
v_res_1085_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v_msg_1080_, v___y_1081_, v___y_21991__boxed_1084_, v___y_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(lean_object* v_f_1086_, lean_object* v_a_1087_, lean_object* v___y_1088_, uint8_t v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___y_1092_; lean_object* v___y_1093_; 
if (v___y_1089_ == 0)
{
v___y_1092_ = v___y_1088_;
v___y_1093_ = v___y_1090_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1106_; lean_object* v_snd_1107_; lean_object* v___x_1108_; lean_object* v_snd_1109_; 
lean_inc_ref(v_f_1086_);
v___x_1106_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_1086_, v___y_1089_, v___y_1090_);
v_snd_1107_ = lean_ctor_get(v___x_1106_, 1);
lean_inc(v_snd_1107_);
lean_dec_ref(v___x_1106_);
lean_inc_ref(v_a_1087_);
v___x_1108_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_1087_, v___y_1089_, v_snd_1107_);
v_snd_1109_ = lean_ctor_get(v___x_1108_, 1);
lean_inc(v_snd_1109_);
lean_dec_ref(v___x_1108_);
v___y_1092_ = v___y_1088_;
v___y_1093_ = v_snd_1109_;
goto v___jp_1091_;
}
v___jp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1105_; 
v___x_1094_ = l_Lean_Expr_app___override(v_f_1086_, v_a_1087_);
v___x_1095_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1094_, v___y_1093_);
v_fst_1096_ = lean_ctor_get(v___x_1095_, 0);
v_snd_1097_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1099_ = v___x_1095_;
v_isShared_1100_ = v_isSharedCheck_1105_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snd_1097_);
lean_inc(v_fst_1096_);
lean_dec(v___x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1105_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v___y_1092_);
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_fst_1096_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___y_1092_);
v___x_1102_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
lean_ctor_set(v___x_1103_, 1, v_snd_1097_);
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4___boxed(lean_object* v_f_1110_, lean_object* v_a_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
uint8_t v___y_22070__boxed_1115_; lean_object* v_res_1116_; 
v___y_22070__boxed_1115_ = lean_unbox(v___y_1113_);
v_res_1116_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_f_1110_, v_a_1111_, v___y_1112_, v___y_22070__boxed_1115_, v___y_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(lean_object* v_x_1117_, uint8_t v_bi_1118_, lean_object* v_t_1119_, lean_object* v_b_1120_, lean_object* v___y_1121_, uint8_t v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___y_1125_; lean_object* v___y_1126_; 
if (v___y_1122_ == 0)
{
v___y_1125_ = v___y_1121_;
v___y_1126_ = v___y_1123_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1139_; lean_object* v_snd_1140_; lean_object* v___x_1141_; lean_object* v_snd_1142_; 
lean_inc_ref(v_t_1119_);
v___x_1139_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1119_, v___y_1122_, v___y_1123_);
v_snd_1140_ = lean_ctor_get(v___x_1139_, 1);
lean_inc(v_snd_1140_);
lean_dec_ref(v___x_1139_);
lean_inc_ref(v_b_1120_);
v___x_1141_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1120_, v___y_1122_, v_snd_1140_);
v_snd_1142_ = lean_ctor_get(v___x_1141_, 1);
lean_inc(v_snd_1142_);
lean_dec_ref(v___x_1141_);
v___y_1125_ = v___y_1121_;
v___y_1126_ = v_snd_1142_;
goto v___jp_1124_;
}
v___jp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_fst_1129_; lean_object* v_snd_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v___x_1127_ = l_Lean_Expr_forallE___override(v_x_1117_, v_t_1119_, v_b_1120_, v_bi_1118_);
v___x_1128_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1127_, v___y_1126_);
v_fst_1129_ = lean_ctor_get(v___x_1128_, 0);
v_snd_1130_ = lean_ctor_get(v___x_1128_, 1);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v___x_1128_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snd_1130_);
lean_inc(v_fst_1129_);
lean_dec(v___x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___y_1125_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_fst_1129_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___y_1125_);
v___x_1135_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_snd_1130_);
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6___boxed(lean_object* v_x_1143_, lean_object* v_bi_1144_, lean_object* v_t_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v_bi_boxed_1150_; uint8_t v___y_22119__boxed_1151_; lean_object* v_res_1152_; 
v_bi_boxed_1150_ = lean_unbox(v_bi_1144_);
v___y_22119__boxed_1151_ = lean_unbox(v___y_1148_);
v_res_1152_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_x_1143_, v_bi_boxed_1150_, v_t_1145_, v_b_1146_, v___y_1147_, v___y_22119__boxed_1151_, v___y_1149_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(lean_object* v_x_1153_, lean_object* v_t_1154_, lean_object* v_v_1155_, lean_object* v_b_1156_, uint8_t v_nondep_1157_, lean_object* v___y_1158_, uint8_t v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___y_1162_; lean_object* v___y_1163_; 
if (v___y_1159_ == 0)
{
v___y_1162_ = v___y_1158_;
v___y_1163_ = v___y_1160_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; lean_object* v_snd_1179_; lean_object* v___x_1180_; lean_object* v_snd_1181_; 
lean_inc_ref(v_t_1154_);
v___x_1176_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_1154_, v___y_1159_, v___y_1160_);
v_snd_1177_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_snd_1177_);
lean_dec_ref(v___x_1176_);
lean_inc_ref(v_v_1155_);
v___x_1178_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_1155_, v___y_1159_, v_snd_1177_);
v_snd_1179_ = lean_ctor_get(v___x_1178_, 1);
lean_inc(v_snd_1179_);
lean_dec_ref(v___x_1178_);
lean_inc_ref(v_b_1156_);
v___x_1180_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_1156_, v___y_1159_, v_snd_1179_);
v_snd_1181_ = lean_ctor_get(v___x_1180_, 1);
lean_inc(v_snd_1181_);
lean_dec_ref(v___x_1180_);
v___y_1162_ = v___y_1158_;
v___y_1163_ = v_snd_1181_;
goto v___jp_1161_;
}
v___jp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
v___x_1164_ = l_Lean_Expr_letE___override(v_x_1153_, v_t_1154_, v_v_1155_, v_b_1156_, v_nondep_1157_);
v___x_1165_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1164_, v___y_1163_);
v_fst_1166_ = lean_ctor_get(v___x_1165_, 0);
v_snd_1167_ = lean_ctor_get(v___x_1165_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1169_ = v___x_1165_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1167_);
lean_inc(v_fst_1166_);
lean_dec(v___x_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___y_1162_);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_fst_1166_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___y_1162_);
v___x_1172_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_snd_1167_);
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7___boxed(lean_object* v_x_1182_, lean_object* v_t_1183_, lean_object* v_v_1184_, lean_object* v_b_1185_, lean_object* v_nondep_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v_nondep_boxed_1190_; uint8_t v___y_22168__boxed_1191_; lean_object* v_res_1192_; 
v_nondep_boxed_1190_ = lean_unbox(v_nondep_1186_);
v___y_22168__boxed_1191_ = lean_unbox(v___y_1188_);
v_res_1192_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_x_1182_, v_t_1183_, v_v_1184_, v_b_1185_, v_nondep_boxed_1190_, v___y_1187_, v___y_22168__boxed_1191_, v___y_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(lean_object* v_a_1193_, lean_object* v_x_1194_){
_start:
{
if (lean_obj_tag(v_x_1194_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_box(0);
return v___x_1195_;
}
else
{
lean_object* v_key_1196_; lean_object* v_value_1197_; lean_object* v_tail_1198_; uint8_t v___y_1200_; lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; uint8_t v___x_1207_; 
v_key_1196_ = lean_ctor_get(v_x_1194_, 0);
v_value_1197_ = lean_ctor_get(v_x_1194_, 1);
v_tail_1198_ = lean_ctor_get(v_x_1194_, 2);
v_fst_1203_ = lean_ctor_get(v_key_1196_, 0);
v_snd_1204_ = lean_ctor_get(v_key_1196_, 1);
v_fst_1205_ = lean_ctor_get(v_a_1193_, 0);
v_snd_1206_ = lean_ctor_get(v_a_1193_, 1);
v___x_1207_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_1203_, v_fst_1205_);
if (v___x_1207_ == 0)
{
v___y_1200_ = v___x_1207_;
goto v___jp_1199_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_nat_dec_eq(v_snd_1204_, v_snd_1206_);
v___y_1200_ = v___x_1208_;
goto v___jp_1199_;
}
v___jp_1199_:
{
if (v___y_1200_ == 0)
{
v_x_1194_ = v_tail_1198_;
goto _start;
}
else
{
lean_object* v___x_1202_; 
lean_inc(v_value_1197_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_value_1197_);
return v___x_1202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg___boxed(lean_object* v_a_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1209_, v_x_1210_);
lean_dec(v_x_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(lean_object* v_m_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_buckets_1214_; lean_object* v_fst_1215_; lean_object* v_snd_1216_; lean_object* v___x_1217_; uint64_t v___x_1218_; uint64_t v___x_1219_; uint64_t v___x_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; uint64_t v_fold_1223_; uint64_t v___x_1224_; uint64_t v___x_1225_; uint64_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_buckets_1214_ = lean_ctor_get(v_m_1212_, 1);
v_fst_1215_ = lean_ctor_get(v_a_1213_, 0);
v_snd_1216_ = lean_ctor_get(v_a_1213_, 1);
v___x_1217_ = lean_array_get_size(v_buckets_1214_);
v___x_1218_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1215_);
v___x_1219_ = lean_uint64_of_nat(v_snd_1216_);
v___x_1220_ = lean_uint64_mix_hash(v___x_1218_, v___x_1219_);
v___x_1221_ = 32ULL;
v___x_1222_ = lean_uint64_shift_right(v___x_1220_, v___x_1221_);
v_fold_1223_ = lean_uint64_xor(v___x_1220_, v___x_1222_);
v___x_1224_ = 16ULL;
v___x_1225_ = lean_uint64_shift_right(v_fold_1223_, v___x_1224_);
v___x_1226_ = lean_uint64_xor(v_fold_1223_, v___x_1225_);
v___x_1227_ = lean_uint64_to_usize(v___x_1226_);
v___x_1228_ = lean_usize_of_nat(v___x_1217_);
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_sub(v___x_1228_, v___x_1229_);
v___x_1231_ = lean_usize_land(v___x_1227_, v___x_1230_);
v___x_1232_ = lean_array_uget_borrowed(v_buckets_1214_, v___x_1231_);
v___x_1233_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1213_, v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_m_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1234_, v_a_1235_);
lean_dec_ref(v_a_1235_);
lean_dec_ref(v_m_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(lean_object* v_d_1237_, lean_object* v_e_1238_, lean_object* v___y_1239_, uint8_t v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___y_1243_; lean_object* v___y_1244_; 
if (v___y_1240_ == 0)
{
v___y_1243_ = v___y_1239_;
v___y_1244_ = v___y_1241_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1257_; lean_object* v_snd_1258_; 
lean_inc_ref(v_e_1238_);
v___x_1257_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_1238_, v___y_1240_, v___y_1241_);
v_snd_1258_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_snd_1258_);
lean_dec_ref(v___x_1257_);
v___y_1243_ = v___y_1239_;
v___y_1244_ = v_snd_1258_;
goto v___jp_1242_;
}
v___jp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_fst_1247_; lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1256_; 
v___x_1245_ = l_Lean_Expr_mdata___override(v_d_1237_, v_e_1238_);
v___x_1246_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1245_, v___y_1244_);
v_fst_1247_ = lean_ctor_get(v___x_1246_, 0);
v_snd_1248_ = lean_ctor_get(v___x_1246_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1250_ = v___x_1246_;
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_inc(v_fst_1247_);
lean_dec(v___x_1246_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___y_1243_);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_fst_1247_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___y_1243_);
v___x_1253_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v_snd_1248_);
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8___boxed(lean_object* v_d_1259_, lean_object* v_e_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v___y_22291__boxed_1264_; lean_object* v_res_1265_; 
v___y_22291__boxed_1264_ = lean_unbox(v___y_1262_);
v_res_1265_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_d_1259_, v_e_1260_, v___y_1261_, v___y_22291__boxed_1264_, v___y_1263_);
return v_res_1265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Array_instInhabited(lean_box(0));
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__2));
v___x_1270_ = lean_unsigned_to_nat(12u);
v___x_1271_ = lean_unsigned_to_nat(234u);
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__1));
v___x_1273_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1274_ = l_mkPanicMessageWithDecl(v___x_1273_, v___x_1272_, v___x_1271_, v___x_1270_, v___x_1269_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1279_ = lean_unsigned_to_nat(67u);
v___x_1280_ = lean_unsigned_to_nat(35u);
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__1));
v___x_1282_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__0));
v___x_1283_ = l_mkPanicMessageWithDecl(v___x_1282_, v___x_1281_, v___x_1280_, v___x_1279_, v___x_1278_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(lean_object* v_n_1284_, lean_object* v_varDeps_1285_, lean_object* v_xs_1286_, lean_object* v_e_1287_, lean_object* v_offset_1288_, lean_object* v_a_1289_, uint8_t v_a_1290_, lean_object* v_a_1291_){
_start:
{
switch(lean_obj_tag(v_e_1287_))
{
case 5:
{
lean_object* v_fn_1292_; lean_object* v_arg_1293_; lean_object* v___x_1294_; lean_object* v_fst_1295_; lean_object* v_snd_1296_; lean_object* v_fst_1297_; lean_object* v_snd_1298_; lean_object* v___x_1299_; lean_object* v_fst_1300_; lean_object* v_snd_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1322_; 
v_fn_1292_ = lean_ctor_get(v_e_1287_, 0);
v_arg_1293_ = lean_ctor_get(v_e_1287_, 1);
lean_inc(v_offset_1288_);
lean_inc_ref(v_fn_1292_);
v___x_1294_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_fn_1292_, v_offset_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
v_fst_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_fst_1295_);
v_snd_1296_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_snd_1296_);
lean_dec_ref(v___x_1294_);
v_fst_1297_ = lean_ctor_get(v_fst_1295_, 0);
lean_inc(v_fst_1297_);
v_snd_1298_ = lean_ctor_get(v_fst_1295_, 1);
lean_inc(v_snd_1298_);
lean_dec(v_fst_1295_);
lean_inc_ref(v_arg_1293_);
v___x_1299_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_arg_1293_, v_offset_1288_, v_snd_1298_, v_a_1290_, v_snd_1296_);
v_fst_1300_ = lean_ctor_get(v___x_1299_, 0);
v_snd_1301_ = lean_ctor_get(v___x_1299_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1303_ = v___x_1299_;
v_isShared_1304_ = v_isSharedCheck_1322_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_snd_1301_);
lean_inc(v_fst_1300_);
lean_dec(v___x_1299_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1322_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_fst_1305_; lean_object* v_snd_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1321_; 
v_fst_1305_ = lean_ctor_get(v_fst_1300_, 0);
v_snd_1306_ = lean_ctor_get(v_fst_1300_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_fst_1300_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1308_ = v_fst_1300_;
v_isShared_1309_ = v_isSharedCheck_1321_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_snd_1306_);
lean_inc(v_fst_1305_);
lean_dec(v_fst_1300_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1321_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
uint8_t v___y_1311_; uint8_t v___x_1319_; 
v___x_1319_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_1292_, v_fst_1297_);
if (v___x_1319_ == 0)
{
v___y_1311_ = v___x_1319_;
goto v___jp_1310_;
}
else
{
uint8_t v___x_1320_; 
v___x_1320_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_1293_, v_fst_1305_);
v___y_1311_ = v___x_1320_;
goto v___jp_1310_;
}
v___jp_1310_:
{
if (v___y_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_del_object(v___x_1308_);
lean_del_object(v___x_1303_);
lean_dec_ref(v_e_1287_);
v___x_1312_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__4(v_fst_1297_, v_fst_1305_, v_snd_1306_, v_a_1290_, v_snd_1301_);
return v___x_1312_;
}
else
{
lean_object* v___x_1314_; 
lean_dec(v_fst_1305_);
lean_dec(v_fst_1297_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_e_1287_);
v___x_1314_ = v___x_1308_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_e_1287_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_snd_1306_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1314_);
v___x_1316_ = v___x_1303_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_snd_1301_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_1323_; lean_object* v_binderType_1324_; lean_object* v_body_1325_; uint8_t v_binderInfo_1326_; lean_object* v___x_1327_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_fst_1335_; lean_object* v_snd_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1357_; 
v_binderName_1323_ = lean_ctor_get(v_e_1287_, 0);
v_binderType_1324_ = lean_ctor_get(v_e_1287_, 1);
v_body_1325_ = lean_ctor_get(v_e_1287_, 2);
v_binderInfo_1326_ = lean_ctor_get_uint8(v_e_1287_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1288_);
lean_inc_ref(v_binderType_1324_);
v___x_1327_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_binderType_1324_, v_offset_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
v_fst_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_fst_1328_);
v_snd_1329_ = lean_ctor_get(v___x_1327_, 1);
lean_inc(v_snd_1329_);
lean_dec_ref(v___x_1327_);
v_fst_1330_ = lean_ctor_get(v_fst_1328_, 0);
lean_inc(v_fst_1330_);
v_snd_1331_ = lean_ctor_get(v_fst_1328_, 1);
lean_inc(v_snd_1331_);
lean_dec(v_fst_1328_);
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_nat_add(v_offset_1288_, v___x_1332_);
lean_dec(v_offset_1288_);
lean_inc_ref(v_body_1325_);
v___x_1334_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_body_1325_, v___x_1333_, v_snd_1331_, v_a_1290_, v_snd_1329_);
v_fst_1335_ = lean_ctor_get(v___x_1334_, 0);
v_snd_1336_ = lean_ctor_get(v___x_1334_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1338_ = v___x_1334_;
v_isShared_1339_ = v_isSharedCheck_1357_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_snd_1336_);
lean_inc(v_fst_1335_);
lean_dec(v___x_1334_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1357_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1356_; 
v_fst_1340_ = lean_ctor_get(v_fst_1335_, 0);
v_snd_1341_ = lean_ctor_get(v_fst_1335_, 1);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_fst_1335_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1343_ = v_fst_1335_;
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_snd_1341_);
lean_inc(v_fst_1340_);
lean_dec(v_fst_1335_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
uint8_t v___y_1346_; uint8_t v___x_1354_; 
v___x_1354_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1324_, v_fst_1330_);
if (v___x_1354_ == 0)
{
v___y_1346_ = v___x_1354_;
goto v___jp_1345_;
}
else
{
uint8_t v___x_1355_; 
v___x_1355_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1325_, v_fst_1340_);
v___y_1346_ = v___x_1355_;
goto v___jp_1345_;
}
v___jp_1345_:
{
if (v___y_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_inc(v_binderName_1323_);
lean_del_object(v___x_1343_);
lean_del_object(v___x_1338_);
lean_dec_ref(v_e_1287_);
v___x_1347_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__5(v_binderName_1323_, v_binderInfo_1326_, v_fst_1330_, v_fst_1340_, v_snd_1341_, v_a_1290_, v_snd_1336_);
return v___x_1347_;
}
else
{
lean_object* v___x_1349_; 
lean_dec(v_fst_1340_);
lean_dec(v_fst_1330_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v_e_1287_);
v___x_1349_ = v___x_1343_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_e_1287_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_snd_1341_);
v___x_1349_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1351_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1349_);
v___x_1351_ = v___x_1338_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_snd_1336_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_1358_; lean_object* v_binderType_1359_; lean_object* v_body_1360_; uint8_t v_binderInfo_1361_; lean_object* v___x_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1392_; 
v_binderName_1358_ = lean_ctor_get(v_e_1287_, 0);
v_binderType_1359_ = lean_ctor_get(v_e_1287_, 1);
v_body_1360_ = lean_ctor_get(v_e_1287_, 2);
v_binderInfo_1361_ = lean_ctor_get_uint8(v_e_1287_, sizeof(void*)*3 + 8);
lean_inc(v_offset_1288_);
lean_inc_ref(v_binderType_1359_);
v___x_1362_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_binderType_1359_, v_offset_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
v_fst_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_fst_1363_);
v_snd_1364_ = lean_ctor_get(v___x_1362_, 1);
lean_inc(v_snd_1364_);
lean_dec_ref(v___x_1362_);
v_fst_1365_ = lean_ctor_get(v_fst_1363_, 0);
lean_inc(v_fst_1365_);
v_snd_1366_ = lean_ctor_get(v_fst_1363_, 1);
lean_inc(v_snd_1366_);
lean_dec(v_fst_1363_);
v___x_1367_ = lean_unsigned_to_nat(1u);
v___x_1368_ = lean_nat_add(v_offset_1288_, v___x_1367_);
lean_dec(v_offset_1288_);
lean_inc_ref(v_body_1360_);
v___x_1369_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_body_1360_, v___x_1368_, v_snd_1366_, v_a_1290_, v_snd_1364_);
v_fst_1370_ = lean_ctor_get(v___x_1369_, 0);
v_snd_1371_ = lean_ctor_get(v___x_1369_, 1);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1373_ = v___x_1369_;
v_isShared_1374_ = v_isSharedCheck_1392_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_inc(v_fst_1370_);
lean_dec(v___x_1369_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1392_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_fst_1375_; lean_object* v_snd_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1391_; 
v_fst_1375_ = lean_ctor_get(v_fst_1370_, 0);
v_snd_1376_ = lean_ctor_get(v_fst_1370_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_fst_1370_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1378_ = v_fst_1370_;
v_isShared_1379_ = v_isSharedCheck_1391_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_snd_1376_);
lean_inc(v_fst_1375_);
lean_dec(v_fst_1370_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1391_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
uint8_t v___y_1381_; uint8_t v___x_1389_; 
v___x_1389_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_1359_, v_fst_1365_);
if (v___x_1389_ == 0)
{
v___y_1381_ = v___x_1389_;
goto v___jp_1380_;
}
else
{
uint8_t v___x_1390_; 
v___x_1390_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1360_, v_fst_1375_);
v___y_1381_ = v___x_1390_;
goto v___jp_1380_;
}
v___jp_1380_:
{
if (v___y_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_inc(v_binderName_1358_);
lean_del_object(v___x_1378_);
lean_del_object(v___x_1373_);
lean_dec_ref(v_e_1287_);
v___x_1382_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__6(v_binderName_1358_, v_binderInfo_1361_, v_fst_1365_, v_fst_1375_, v_snd_1376_, v_a_1290_, v_snd_1371_);
return v___x_1382_;
}
else
{
lean_object* v___x_1384_; 
lean_dec(v_fst_1375_);
lean_dec(v_fst_1365_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v_e_1287_);
v___x_1384_ = v___x_1378_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_e_1287_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_snd_1376_);
v___x_1384_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1384_);
v___x_1386_ = v___x_1373_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_snd_1371_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_1393_; lean_object* v_type_1394_; lean_object* v_value_1395_; lean_object* v_body_1396_; uint8_t v_nondep_1397_; lean_object* v___x_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___x_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; lean_object* v_fst_1406_; lean_object* v_snd_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_fst_1411_; lean_object* v_snd_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1435_; 
v_declName_1393_ = lean_ctor_get(v_e_1287_, 0);
v_type_1394_ = lean_ctor_get(v_e_1287_, 1);
v_value_1395_ = lean_ctor_get(v_e_1287_, 2);
v_body_1396_ = lean_ctor_get(v_e_1287_, 3);
v_nondep_1397_ = lean_ctor_get_uint8(v_e_1287_, sizeof(void*)*4 + 8);
lean_inc(v_offset_1288_);
lean_inc_ref(v_type_1394_);
v___x_1398_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_type_1394_, v_offset_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
v_fst_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_fst_1399_);
v_snd_1400_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_snd_1400_);
lean_dec_ref(v___x_1398_);
v_fst_1401_ = lean_ctor_get(v_fst_1399_, 0);
lean_inc(v_fst_1401_);
v_snd_1402_ = lean_ctor_get(v_fst_1399_, 1);
lean_inc(v_snd_1402_);
lean_dec(v_fst_1399_);
lean_inc(v_offset_1288_);
lean_inc_ref(v_value_1395_);
v___x_1403_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_value_1395_, v_offset_1288_, v_snd_1402_, v_a_1290_, v_snd_1400_);
v_fst_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_fst_1404_);
v_snd_1405_ = lean_ctor_get(v___x_1403_, 1);
lean_inc(v_snd_1405_);
lean_dec_ref(v___x_1403_);
v_fst_1406_ = lean_ctor_get(v_fst_1404_, 0);
lean_inc(v_fst_1406_);
v_snd_1407_ = lean_ctor_get(v_fst_1404_, 1);
lean_inc(v_snd_1407_);
lean_dec(v_fst_1404_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_nat_add(v_offset_1288_, v___x_1408_);
lean_dec(v_offset_1288_);
lean_inc_ref(v_body_1396_);
v___x_1410_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_body_1396_, v___x_1409_, v_snd_1407_, v_a_1290_, v_snd_1405_);
v_fst_1411_ = lean_ctor_get(v___x_1410_, 0);
v_snd_1412_ = lean_ctor_get(v___x_1410_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1414_ = v___x_1410_;
v_isShared_1415_ = v_isSharedCheck_1435_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_snd_1412_);
lean_inc(v_fst_1411_);
lean_dec(v___x_1410_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1435_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_fst_1416_; lean_object* v_snd_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1434_; 
v_fst_1416_ = lean_ctor_get(v_fst_1411_, 0);
v_snd_1417_ = lean_ctor_get(v_fst_1411_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_fst_1411_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1419_ = v_fst_1411_;
v_isShared_1420_ = v_isSharedCheck_1434_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_snd_1417_);
lean_inc(v_fst_1416_);
lean_dec(v_fst_1411_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1434_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
uint8_t v___y_1422_; uint8_t v___x_1432_; 
v___x_1432_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_1394_, v_fst_1401_);
if (v___x_1432_ == 0)
{
v___y_1422_ = v___x_1432_;
goto v___jp_1421_;
}
else
{
uint8_t v___x_1433_; 
v___x_1433_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_1395_, v_fst_1406_);
v___y_1422_ = v___x_1433_;
goto v___jp_1421_;
}
v___jp_1421_:
{
if (v___y_1422_ == 0)
{
lean_object* v___x_1423_; 
lean_inc(v_declName_1393_);
lean_del_object(v___x_1419_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_e_1287_);
v___x_1423_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1393_, v_fst_1401_, v_fst_1406_, v_fst_1416_, v_nondep_1397_, v_snd_1417_, v_a_1290_, v_snd_1412_);
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_1396_, v_fst_1416_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; 
lean_inc(v_declName_1393_);
lean_del_object(v___x_1419_);
lean_del_object(v___x_1414_);
lean_dec_ref(v_e_1287_);
v___x_1425_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__7(v_declName_1393_, v_fst_1401_, v_fst_1406_, v_fst_1416_, v_nondep_1397_, v_snd_1417_, v_a_1290_, v_snd_1412_);
return v___x_1425_;
}
else
{
lean_object* v___x_1427_; 
lean_dec(v_fst_1416_);
lean_dec(v_fst_1406_);
lean_dec(v_fst_1401_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v_e_1287_);
v___x_1427_ = v___x_1419_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_e_1287_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_snd_1417_);
v___x_1427_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1427_);
v___x_1429_ = v___x_1414_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_snd_1412_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
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
lean_object* v_data_1436_; lean_object* v_expr_1437_; lean_object* v___x_1438_; lean_object* v_fst_1439_; lean_object* v_snd_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1458_; 
v_data_1436_ = lean_ctor_get(v_e_1287_, 0);
v_expr_1437_ = lean_ctor_get(v_e_1287_, 1);
lean_inc_ref(v_expr_1437_);
v___x_1438_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_expr_1437_, v_offset_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
v_fst_1439_ = lean_ctor_get(v___x_1438_, 0);
v_snd_1440_ = lean_ctor_get(v___x_1438_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1442_ = v___x_1438_;
v_isShared_1443_ = v_isSharedCheck_1458_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snd_1440_);
lean_inc(v_fst_1439_);
lean_dec(v___x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1458_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v_fst_1444_; lean_object* v_snd_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1457_; 
v_fst_1444_ = lean_ctor_get(v_fst_1439_, 0);
v_snd_1445_ = lean_ctor_get(v_fst_1439_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_fst_1439_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1447_ = v_fst_1439_;
v_isShared_1448_ = v_isSharedCheck_1457_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_snd_1445_);
lean_inc(v_fst_1444_);
lean_dec(v_fst_1439_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1457_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
uint8_t v___x_1449_; 
v___x_1449_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_1437_, v_fst_1444_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_inc(v_data_1436_);
lean_del_object(v___x_1447_);
lean_del_object(v___x_1442_);
lean_dec_ref(v_e_1287_);
v___x_1450_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__8(v_data_1436_, v_fst_1444_, v_snd_1445_, v_a_1290_, v_snd_1440_);
return v___x_1450_;
}
else
{
lean_object* v___x_1452_; 
lean_dec(v_fst_1444_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v_e_1287_);
v___x_1452_ = v___x_1447_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_e_1287_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_snd_1445_);
v___x_1452_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1452_);
v___x_1454_ = v___x_1442_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_snd_1440_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_1459_; lean_object* v_idx_1460_; lean_object* v_struct_1461_; lean_object* v___x_1462_; lean_object* v_fst_1463_; lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1482_; 
v_typeName_1459_ = lean_ctor_get(v_e_1287_, 0);
v_idx_1460_ = lean_ctor_get(v_e_1287_, 1);
v_struct_1461_ = lean_ctor_get(v_e_1287_, 2);
lean_inc_ref(v_struct_1461_);
v___x_1462_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1284_, v_varDeps_1285_, v_xs_1286_, v_struct_1461_, v_offset_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
v_fst_1463_ = lean_ctor_get(v___x_1462_, 0);
v_snd_1464_ = lean_ctor_get(v___x_1462_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1466_ = v___x_1462_;
v_isShared_1467_ = v_isSharedCheck_1482_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_inc(v_fst_1463_);
lean_dec(v___x_1462_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1482_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_fst_1468_; lean_object* v_snd_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1481_; 
v_fst_1468_ = lean_ctor_get(v_fst_1463_, 0);
v_snd_1469_ = lean_ctor_get(v_fst_1463_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_fst_1463_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1471_ = v_fst_1463_;
v_isShared_1472_ = v_isSharedCheck_1481_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_snd_1469_);
lean_inc(v_fst_1468_);
lean_dec(v_fst_1463_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1481_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
uint8_t v___x_1473_; 
v___x_1473_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_1461_, v_fst_1468_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_inc(v_idx_1460_);
lean_inc(v_typeName_1459_);
lean_del_object(v___x_1471_);
lean_del_object(v___x_1466_);
lean_dec_ref(v_e_1287_);
v___x_1474_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__9(v_typeName_1459_, v_idx_1460_, v_fst_1468_, v_snd_1469_, v_a_1290_, v_snd_1464_);
return v___x_1474_;
}
else
{
lean_object* v___x_1476_; 
lean_dec(v_fst_1468_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_e_1287_);
v___x_1476_ = v___x_1471_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_e_1287_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_snd_1469_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1476_);
v___x_1478_ = v___x_1466_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_snd_1464_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v_offset_1288_);
lean_dec_ref(v_e_1287_);
v___x_1483_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__3);
v___x_1484_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__10(v___x_1483_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(lean_object* v_n_1485_, lean_object* v_varDeps_1486_, lean_object* v_xs_1487_, lean_object* v_e_1488_, lean_object* v_offset_1489_, lean_object* v_a_1490_, uint8_t v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_key_1493_; lean_object* v_snd_1495_; lean_object* v___x_1508_; 
lean_inc(v_offset_1489_);
lean_inc_ref(v_e_1488_);
v_key_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1493_, 0, v_e_1488_);
lean_ctor_set(v_key_1493_, 1, v_offset_1489_);
v___x_1508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_a_1490_, v_key_1493_);
if (lean_obj_tag(v___x_1508_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_key_1493_);
lean_dec(v_offset_1489_);
lean_dec_ref(v_e_1488_);
v_val_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_val_1509_);
lean_dec_ref(v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_val_1509_);
lean_ctor_set(v___x_1510_, 1, v_a_1490_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v_a_1492_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
lean_dec(v___x_1508_);
v___x_1512_ = l_Lean_Expr_looseBVarRange(v_e_1488_);
v___x_1513_ = lean_nat_dec_le(v___x_1512_, v_offset_1489_);
lean_dec(v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_Expr_getAppFn(v_e_1488_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_deBruijnIndex_1515_; uint8_t v___x_1516_; 
v_deBruijnIndex_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_deBruijnIndex_1515_);
lean_dec_ref(v___x_1514_);
v___x_1516_ = lean_nat_dec_le(v_offset_1489_, v_deBruijnIndex_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec(v_deBruijnIndex_1515_);
lean_dec(v_offset_1489_);
v___x_1517_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_e_1488_, v_a_1490_, v_a_1491_, v_a_1492_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1518_ = lean_nat_add(v_offset_1489_, v_n_1485_);
v___x_1519_ = lean_nat_dec_lt(v_deBruijnIndex_1515_, v___x_1518_);
lean_dec(v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v___x_1524_; 
lean_dec(v_offset_1489_);
lean_dec_ref(v_e_1488_);
v___x_1520_ = lean_nat_sub(v_deBruijnIndex_1515_, v_n_1485_);
lean_dec(v_deBruijnIndex_1515_);
v___x_1521_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1520_, v_a_1492_);
v_fst_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_fst_1522_);
v_snd_1523_ = lean_ctor_get(v___x_1521_, 1);
lean_inc(v_snd_1523_);
lean_dec_ref(v___x_1521_);
v___x_1524_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_fst_1522_, v_a_1490_, v_a_1491_, v_snd_1523_);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_i_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_expectedNumArgs_1531_; lean_object* v_numArgs_1532_; uint8_t v___x_1533_; 
v___x_1525_ = lean_nat_sub(v_deBruijnIndex_1515_, v_offset_1489_);
lean_dec(v_deBruijnIndex_1515_);
v___x_1526_ = lean_nat_sub(v_n_1485_, v___x_1525_);
lean_dec(v___x_1525_);
v___x_1527_ = lean_unsigned_to_nat(1u);
v_i_1528_ = lean_nat_sub(v___x_1526_, v___x_1527_);
lean_dec(v___x_1526_);
v___x_1529_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1530_ = lean_array_get_borrowed(v___x_1529_, v_varDeps_1486_, v_i_1528_);
v_expectedNumArgs_1531_ = lean_array_get_size(v___x_1530_);
v_numArgs_1532_ = l_Lean_Expr_getAppNumArgs(v_e_1488_);
v___x_1533_ = lean_nat_dec_lt(v_expectedNumArgs_1531_, v_numArgs_1532_);
if (v___x_1533_ == 0)
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_nat_dec_eq(v_numArgs_1532_, v_expectedNumArgs_1531_);
lean_dec(v_numArgs_1532_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_fst_1537_; 
lean_dec(v_i_1528_);
v___x_1535_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1536_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1535_, v_a_1491_, v_a_1492_);
v_fst_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_fst_1537_);
if (lean_obj_tag(v_fst_1537_) == 1)
{
lean_object* v_snd_1538_; lean_object* v_val_1539_; lean_object* v___x_1540_; 
lean_dec(v_offset_1489_);
lean_dec_ref(v_e_1488_);
v_snd_1538_ = lean_ctor_get(v___x_1536_, 1);
lean_inc(v_snd_1538_);
lean_dec_ref(v___x_1536_);
v_val_1539_ = lean_ctor_get(v_fst_1537_, 0);
lean_inc(v_val_1539_);
lean_dec_ref(v_fst_1537_);
v___x_1540_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_val_1539_, v_a_1490_, v_a_1491_, v_snd_1538_);
return v___x_1540_;
}
else
{
lean_object* v_snd_1541_; 
lean_dec(v_fst_1537_);
v_snd_1541_ = lean_ctor_get(v___x_1536_, 1);
lean_inc(v_snd_1541_);
lean_dec_ref(v___x_1536_);
v_snd_1495_ = v_snd_1541_;
goto v___jp_1494_;
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v_offset_1489_);
lean_dec_ref(v_e_1488_);
v___x_1542_ = lean_array_fget_borrowed(v_xs_1487_, v_i_1528_);
lean_dec(v_i_1528_);
lean_inc(v___x_1542_);
v___x_1543_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v___x_1542_, v_a_1490_, v_a_1491_, v_a_1492_);
return v___x_1543_;
}
}
else
{
lean_dec(v_numArgs_1532_);
lean_dec(v_i_1528_);
v_snd_1495_ = v_a_1492_;
goto v___jp_1494_;
}
}
}
}
else
{
lean_dec_ref(v___x_1514_);
v_snd_1495_ = v_a_1492_;
goto v___jp_1494_;
}
}
else
{
lean_object* v___x_1544_; 
lean_dec(v_offset_1489_);
v___x_1544_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_e_1488_, v_a_1490_, v_a_1491_, v_a_1492_);
return v___x_1544_;
}
}
v___jp_1494_:
{
switch(lean_obj_tag(v_e_1488_))
{
case 9:
{
lean_object* v___x_1496_; 
lean_dec(v_offset_1489_);
v___x_1496_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_e_1488_, v_a_1490_, v_a_1491_, v_snd_1495_);
return v___x_1496_;
}
case 2:
{
lean_object* v___x_1497_; 
lean_dec(v_offset_1489_);
v___x_1497_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_e_1488_, v_a_1490_, v_a_1491_, v_snd_1495_);
return v___x_1497_;
}
case 0:
{
lean_object* v___x_1498_; 
lean_dec(v_offset_1489_);
v___x_1498_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_e_1488_, v_a_1490_, v_a_1491_, v_snd_1495_);
return v___x_1498_;
}
case 1:
{
lean_object* v___x_1499_; 
lean_dec(v_offset_1489_);
v___x_1499_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_e_1488_, v_a_1490_, v_a_1491_, v_snd_1495_);
return v___x_1499_;
}
case 4:
{
lean_object* v___x_1500_; 
lean_dec(v_offset_1489_);
v___x_1500_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_e_1488_, v_a_1490_, v_a_1491_, v_snd_1495_);
return v___x_1500_;
}
case 3:
{
lean_object* v___x_1501_; 
lean_dec(v_offset_1489_);
v___x_1501_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_e_1488_, v_a_1490_, v_a_1491_, v_snd_1495_);
return v___x_1501_;
}
default: 
{
lean_object* v___x_1502_; lean_object* v_fst_1503_; lean_object* v_snd_1504_; lean_object* v_fst_1505_; lean_object* v_snd_1506_; lean_object* v___x_1507_; 
v___x_1502_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1485_, v_varDeps_1486_, v_xs_1487_, v_e_1488_, v_offset_1489_, v_a_1490_, v_a_1491_, v_snd_1495_);
v_fst_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_fst_1503_);
v_snd_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_snd_1504_);
lean_dec_ref(v___x_1502_);
v_fst_1505_ = lean_ctor_get(v_fst_1503_, 0);
lean_inc(v_fst_1505_);
v_snd_1506_ = lean_ctor_get(v_fst_1503_, 1);
lean_inc(v_snd_1506_);
lean_dec(v_fst_1503_);
v___x_1507_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_1493_, v_fst_1505_, v_snd_1506_, v_a_1491_, v_snd_1504_);
return v___x_1507_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___boxed(lean_object* v_n_1545_, lean_object* v_varDeps_1546_, lean_object* v_xs_1547_, lean_object* v_e_1548_, lean_object* v_offset_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
uint8_t v_a_boxed_1553_; lean_object* v_res_1554_; 
v_a_boxed_1553_ = lean_unbox(v_a_1551_);
v_res_1554_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3(v_n_1545_, v_varDeps_1546_, v_xs_1547_, v_e_1548_, v_offset_1549_, v_a_1550_, v_a_boxed_1553_, v_a_1552_);
lean_dec_ref(v_xs_1547_);
lean_dec_ref(v_varDeps_1546_);
lean_dec(v_n_1545_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___boxed(lean_object* v_n_1555_, lean_object* v_varDeps_1556_, lean_object* v_xs_1557_, lean_object* v_e_1558_, lean_object* v_offset_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
uint8_t v_a_boxed_1563_; lean_object* v_res_1564_; 
v_a_boxed_1563_ = lean_unbox(v_a_1561_);
v_res_1564_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1555_, v_varDeps_1556_, v_xs_1557_, v_e_1558_, v_offset_1559_, v_a_1560_, v_a_boxed_1563_, v_a_1562_);
lean_dec_ref(v_xs_1557_);
lean_dec_ref(v_varDeps_1556_);
lean_dec(v_n_1555_);
return v_res_1564_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0(void){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__0(lean_box(0));
return v___x_1565_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_unsigned_to_nat(16u);
v___x_1568_ = lean_mk_array(v___x_1567_, v___x_1566_);
return v___x_1568_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__1);
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(lean_object* v_e_1572_, lean_object* v_xs_1573_, lean_object* v_varDeps_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v_share_1578_; lean_object* v_maxFVar_1579_; lean_object* v_proofInstInfo_1580_; lean_object* v_inferType_1581_; lean_object* v_getLevel_1582_; lean_object* v_congrInfo_1583_; lean_object* v_defEqI_1584_; lean_object* v_extensions_1585_; lean_object* v_issues_1586_; uint8_t v_debug_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1656_; 
v___x_1577_ = lean_st_ref_take(v_a_1575_);
v_share_1578_ = lean_ctor_get(v___x_1577_, 0);
v_maxFVar_1579_ = lean_ctor_get(v___x_1577_, 1);
v_proofInstInfo_1580_ = lean_ctor_get(v___x_1577_, 2);
v_inferType_1581_ = lean_ctor_get(v___x_1577_, 3);
v_getLevel_1582_ = lean_ctor_get(v___x_1577_, 4);
v_congrInfo_1583_ = lean_ctor_get(v___x_1577_, 5);
v_defEqI_1584_ = lean_ctor_get(v___x_1577_, 6);
v_extensions_1585_ = lean_ctor_get(v___x_1577_, 7);
v_issues_1586_ = lean_ctor_get(v___x_1577_, 8);
v_debug_1587_ = lean_ctor_get_uint8(v___x_1577_, sizeof(void*)*9);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1589_ = v___x_1577_;
v_isShared_1590_ = v_isSharedCheck_1656_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_issues_1586_);
lean_inc(v_extensions_1585_);
lean_inc(v_defEqI_1584_);
lean_inc(v_congrInfo_1583_);
lean_inc(v_getLevel_1582_);
lean_inc(v_inferType_1581_);
lean_inc(v_proofInstInfo_1580_);
lean_inc(v_maxFVar_1579_);
lean_inc(v_share_1578_);
lean_dec(v___x_1577_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1656_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__0);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1591_);
v___x_1593_ = v___x_1589_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_maxFVar_1579_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_proofInstInfo_1580_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_inferType_1581_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_getLevel_1582_);
lean_ctor_set(v_reuseFailAlloc_1655_, 5, v_congrInfo_1583_);
lean_ctor_set(v_reuseFailAlloc_1655_, 6, v_defEqI_1584_);
lean_ctor_set(v_reuseFailAlloc_1655_, 7, v_extensions_1585_);
lean_ctor_set(v_reuseFailAlloc_1655_, 8, v_issues_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*9, v_debug_1587_);
v___x_1593_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_fst_1597_; lean_object* v_snd_1598_; uint8_t v_debug_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1594_ = lean_st_ref_set(v_a_1575_, v___x_1593_);
v___x_1595_ = lean_st_ref_get(v_a_1575_);
v_debug_1619_ = lean_ctor_get_uint8(v___x_1595_, sizeof(void*)*9);
lean_dec(v___x_1595_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = l_Lean_Expr_looseBVarRange(v_e_1572_);
v___x_1622_ = lean_nat_dec_le(v___x_1621_, v___x_1620_);
lean_dec(v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v_n_1623_; lean_object* v_snd_1625_; lean_object* v___x_1631_; 
v_n_1623_ = lean_array_get_size(v_xs_1573_);
v___x_1631_ = l_Lean_Expr_getAppFn(v_e_1572_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_deBruijnIndex_1632_; uint8_t v___x_1633_; 
v_deBruijnIndex_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_deBruijnIndex_1632_);
lean_dec_ref(v___x_1631_);
v___x_1633_ = lean_nat_dec_le(v___x_1620_, v_deBruijnIndex_1632_);
if (v___x_1633_ == 0)
{
lean_dec(v_deBruijnIndex_1632_);
v_fst_1597_ = v_e_1572_;
v_snd_1598_ = v_share_1578_;
goto v___jp_1596_;
}
else
{
uint8_t v___x_1634_; 
v___x_1634_ = lean_nat_dec_lt(v_deBruijnIndex_1632_, v_n_1623_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v_fst_1637_; lean_object* v_snd_1638_; 
lean_dec_ref(v_e_1572_);
v___x_1635_ = lean_nat_sub(v_deBruijnIndex_1632_, v_n_1623_);
lean_dec(v_deBruijnIndex_1632_);
v___x_1636_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__1___redArg(v___x_1635_, v_share_1578_);
v_fst_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_fst_1637_);
v_snd_1638_ = lean_ctor_get(v___x_1636_, 1);
lean_inc(v_snd_1638_);
lean_dec_ref(v___x_1636_);
v_fst_1597_ = v_fst_1637_;
v_snd_1598_ = v_snd_1638_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_i_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_expectedNumArgs_1644_; lean_object* v_numArgs_1645_; uint8_t v___x_1646_; 
v___x_1639_ = lean_nat_sub(v_n_1623_, v_deBruijnIndex_1632_);
lean_dec(v_deBruijnIndex_1632_);
v___x_1640_ = lean_unsigned_to_nat(1u);
v_i_1641_ = lean_nat_sub(v___x_1639_, v___x_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__0);
v___x_1643_ = lean_array_get_borrowed(v___x_1642_, v_varDeps_1574_, v_i_1641_);
v_expectedNumArgs_1644_ = lean_array_get_size(v___x_1643_);
v_numArgs_1645_ = l_Lean_Expr_getAppNumArgs(v_e_1572_);
v___x_1646_ = lean_nat_dec_lt(v_expectedNumArgs_1644_, v_numArgs_1645_);
if (v___x_1646_ == 0)
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_eq(v_numArgs_1645_, v_expectedNumArgs_1644_);
lean_dec(v_numArgs_1645_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_fst_1650_; 
lean_dec(v_i_1641_);
v___x_1648_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3___closed__3);
v___x_1649_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__2(v___x_1648_, v_debug_1619_, v_share_1578_);
v_fst_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_fst_1650_);
if (lean_obj_tag(v_fst_1650_) == 1)
{
lean_object* v_snd_1651_; lean_object* v_val_1652_; 
lean_dec_ref(v_e_1572_);
v_snd_1651_ = lean_ctor_get(v___x_1649_, 1);
lean_inc(v_snd_1651_);
lean_dec_ref(v___x_1649_);
v_val_1652_ = lean_ctor_get(v_fst_1650_, 0);
lean_inc(v_val_1652_);
lean_dec_ref(v_fst_1650_);
v_fst_1597_ = v_val_1652_;
v_snd_1598_ = v_snd_1651_;
goto v___jp_1596_;
}
else
{
lean_object* v_snd_1653_; 
lean_dec(v_fst_1650_);
v_snd_1653_ = lean_ctor_get(v___x_1649_, 1);
lean_inc(v_snd_1653_);
lean_dec_ref(v___x_1649_);
v_snd_1625_ = v_snd_1653_;
goto v___jp_1624_;
}
}
else
{
lean_object* v___x_1654_; 
lean_dec_ref(v_e_1572_);
v___x_1654_ = lean_array_fget_borrowed(v_xs_1573_, v_i_1641_);
lean_dec(v_i_1641_);
lean_inc(v___x_1654_);
v_fst_1597_ = v___x_1654_;
v_snd_1598_ = v_share_1578_;
goto v___jp_1596_;
}
}
else
{
lean_dec(v_numArgs_1645_);
lean_dec(v_i_1641_);
v_snd_1625_ = v_share_1578_;
goto v___jp_1624_;
}
}
}
}
else
{
lean_dec_ref(v___x_1631_);
v_snd_1625_ = v_share_1578_;
goto v___jp_1624_;
}
v___jp_1624_:
{
switch(lean_obj_tag(v_e_1572_))
{
case 9:
{
v_fst_1597_ = v_e_1572_;
v_snd_1598_ = v_snd_1625_;
goto v___jp_1596_;
}
case 2:
{
v_fst_1597_ = v_e_1572_;
v_snd_1598_ = v_snd_1625_;
goto v___jp_1596_;
}
case 0:
{
v_fst_1597_ = v_e_1572_;
v_snd_1598_ = v_snd_1625_;
goto v___jp_1596_;
}
case 1:
{
v_fst_1597_ = v_e_1572_;
v_snd_1598_ = v_snd_1625_;
goto v___jp_1596_;
}
case 4:
{
v_fst_1597_ = v_e_1572_;
v_snd_1598_ = v_snd_1625_;
goto v___jp_1596_;
}
case 3:
{
v_fst_1597_ = v_e_1572_;
v_snd_1598_ = v_snd_1625_;
goto v___jp_1596_;
}
default: 
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_fst_1628_; lean_object* v_snd_1629_; lean_object* v_fst_1630_; 
v___x_1626_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___closed__2);
v___x_1627_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3(v_n_1623_, v_varDeps_1574_, v_xs_1573_, v_e_1572_, v___x_1620_, v___x_1626_, v_debug_1619_, v_snd_1625_);
v_fst_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_fst_1628_);
v_snd_1629_ = lean_ctor_get(v___x_1627_, 1);
lean_inc(v_snd_1629_);
lean_dec_ref(v___x_1627_);
v_fst_1630_ = lean_ctor_get(v_fst_1628_, 0);
lean_inc(v_fst_1630_);
lean_dec(v_fst_1628_);
v_fst_1597_ = v_fst_1630_;
v_snd_1598_ = v_snd_1629_;
goto v___jp_1596_;
}
}
}
}
else
{
v_fst_1597_ = v_e_1572_;
v_snd_1598_ = v_share_1578_;
goto v___jp_1596_;
}
v___jp_1596_:
{
lean_object* v___x_1599_; lean_object* v_maxFVar_1600_; lean_object* v_proofInstInfo_1601_; lean_object* v_inferType_1602_; lean_object* v_getLevel_1603_; lean_object* v_congrInfo_1604_; lean_object* v_defEqI_1605_; lean_object* v_extensions_1606_; lean_object* v_issues_1607_; uint8_t v_debug_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1617_; 
v___x_1599_ = lean_st_ref_take(v_a_1575_);
v_maxFVar_1600_ = lean_ctor_get(v___x_1599_, 1);
v_proofInstInfo_1601_ = lean_ctor_get(v___x_1599_, 2);
v_inferType_1602_ = lean_ctor_get(v___x_1599_, 3);
v_getLevel_1603_ = lean_ctor_get(v___x_1599_, 4);
v_congrInfo_1604_ = lean_ctor_get(v___x_1599_, 5);
v_defEqI_1605_ = lean_ctor_get(v___x_1599_, 6);
v_extensions_1606_ = lean_ctor_get(v___x_1599_, 7);
v_issues_1607_ = lean_ctor_get(v___x_1599_, 8);
v_debug_1608_ = lean_ctor_get_uint8(v___x_1599_, sizeof(void*)*9);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1617_ == 0)
{
lean_object* v_unused_1618_; 
v_unused_1618_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1618_);
v___x_1610_ = v___x_1599_;
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_issues_1607_);
lean_inc(v_extensions_1606_);
lean_inc(v_defEqI_1605_);
lean_inc(v_congrInfo_1604_);
lean_inc(v_getLevel_1603_);
lean_inc(v_inferType_1602_);
lean_inc(v_proofInstInfo_1601_);
lean_inc(v_maxFVar_1600_);
lean_dec(v___x_1599_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_snd_1598_);
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_snd_1598_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_maxFVar_1600_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_proofInstInfo_1601_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_inferType_1602_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v_getLevel_1603_);
lean_ctor_set(v_reuseFailAlloc_1616_, 5, v_congrInfo_1604_);
lean_ctor_set(v_reuseFailAlloc_1616_, 6, v_defEqI_1605_);
lean_ctor_set(v_reuseFailAlloc_1616_, 7, v_extensions_1606_);
lean_ctor_set(v_reuseFailAlloc_1616_, 8, v_issues_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1616_, sizeof(void*)*9, v_debug_1608_);
v___x_1613_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_st_ref_set(v_a_1575_, v___x_1613_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_fst_1597_);
return v___x_1615_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg___boxed(lean_object* v_e_1657_, lean_object* v_xs_1658_, lean_object* v_varDeps_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1657_, v_xs_1658_, v_varDeps_1659_, v_a_1660_);
lean_dec(v_a_1660_);
lean_dec_ref(v_varDeps_1659_);
lean_dec_ref(v_xs_1658_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(lean_object* v_e_1663_, lean_object* v_xs_1664_, lean_object* v_varDeps_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_e_1663_, v_xs_1664_, v_varDeps_1665_, v_a_1667_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___boxed(lean_object* v_e_1674_, lean_object* v_xs_1675_, lean_object* v_varDeps_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps(v_e_1674_, v_xs_1675_, v_varDeps_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec_ref(v_varDeps_1676_);
lean_dec_ref(v_xs_1675_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_1685_, lean_object* v_m_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___redArg(v_m_1686_, v_a_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1689_, lean_object* v_m_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4(v_00_u03b2_1689_, v_m_1690_, v_a_1691_);
lean_dec_ref(v_a_1691_);
lean_dec_ref(v_m_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(lean_object* v_00_u03b2_1693_, lean_object* v_a_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___redArg(v_a_1694_, v_x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12___boxed(lean_object* v_00_u03b2_1697_, lean_object* v_a_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3_spec__3_spec__4_spec__12(v_00_u03b2_1697_, v_a_1698_, v_x_1699_);
lean_dec(v_x_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(lean_object* v_name_1701_, lean_object* v_type_1702_, lean_object* v_val_1703_, lean_object* v_k_1704_, uint8_t v_nondep_1705_, uint8_t v_kind_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___f_1714_; lean_object* v___x_1715_; 
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
v___f_1714_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go_spec__4_spec__4___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1714_, 0, v_k_1704_);
lean_closure_set(v___f_1714_, 1, v___y_1707_);
lean_closure_set(v___f_1714_, 2, v___y_1708_);
v___x_1715_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1701_, v_type_1702_, v_val_1703_, v___f_1714_, v_nondep_1705_, v_kind_1706_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1715_) == 0)
{
return v___x_1715_;
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg___boxed(lean_object* v_name_1724_, lean_object* v_type_1725_, lean_object* v_val_1726_, lean_object* v_k_1727_, lean_object* v_nondep_1728_, lean_object* v_kind_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v_nondep_boxed_1737_; uint8_t v_kind_boxed_1738_; lean_object* v_res_1739_; 
v_nondep_boxed_1737_ = lean_unbox(v_nondep_1728_);
v_kind_boxed_1738_ = lean_unbox(v_kind_1729_);
v_res_1739_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1724_, v_type_1725_, v_val_1726_, v_k_1727_, v_nondep_boxed_1737_, v_kind_boxed_1738_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(lean_object* v_00_u03b1_1740_, lean_object* v_name_1741_, lean_object* v_type_1742_, lean_object* v_val_1743_, lean_object* v_k_1744_, uint8_t v_nondep_1745_, uint8_t v_kind_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_name_1741_, v_type_1742_, v_val_1743_, v_k_1744_, v_nondep_1745_, v_kind_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___boxed(lean_object* v_00_u03b1_1755_, lean_object* v_name_1756_, lean_object* v_type_1757_, lean_object* v_val_1758_, lean_object* v_k_1759_, lean_object* v_nondep_1760_, lean_object* v_kind_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v_nondep_boxed_1769_; uint8_t v_kind_boxed_1770_; lean_object* v_res_1771_; 
v_nondep_boxed_1769_ = lean_unbox(v_nondep_1760_);
v_kind_boxed_1770_ = lean_unbox(v_kind_1761_);
v_res_1771_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1(v_00_u03b1_1755_, v_name_1756_, v_type_1757_, v_val_1758_, v_k_1759_, v_nondep_boxed_1769_, v_kind_boxed_1770_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
return v_res_1771_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(lean_object* v_msg_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_2402__overap_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___closed__0);
v___x_2402__overap_1782_ = lean_panic_fn_borrowed(v___x_1781_, v_msg_1773_);
lean_inc(v___y_1779_);
lean_inc_ref(v___y_1778_);
lean_inc(v___y_1777_);
lean_inc_ref(v___y_1776_);
lean_inc(v___y_1775_);
lean_inc_ref(v___y_1774_);
v___x_1783_ = lean_apply_7(v___x_2402__overap_1782_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, lean_box(0));
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2___boxed(lean_object* v_msg_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v_msg_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(lean_object* v_xs_1793_, size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_bs_1796_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_lt(v_i_1795_, v_sz_1794_);
if (v___x_1797_ == 0)
{
return v_bs_1796_;
}
else
{
lean_object* v_v_1798_; lean_object* v___x_1799_; lean_object* v_bs_x27_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; lean_object* v___x_1805_; 
v_v_1798_ = lean_array_uget(v_bs_1796_, v_i_1795_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v_bs_x27_1800_ = lean_array_uset(v_bs_1796_, v_i_1795_, v___x_1799_);
v___x_1801_ = l_Lean_instInhabitedExpr;
v___x_1802_ = lean_array_get_borrowed(v___x_1801_, v_xs_1793_, v_v_1798_);
lean_dec(v_v_1798_);
v___x_1803_ = ((size_t)1ULL);
v___x_1804_ = lean_usize_add(v_i_1795_, v___x_1803_);
lean_inc(v___x_1802_);
v___x_1805_ = lean_array_uset(v_bs_x27_1800_, v_i_1795_, v___x_1802_);
v_i_1795_ = v___x_1804_;
v_bs_1796_ = v___x_1805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0___boxed(lean_object* v_xs_1807_, lean_object* v_sz_1808_, lean_object* v_i_1809_, lean_object* v_bs_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1808_);
lean_dec(v_sz_1808_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1809_);
lean_dec(v_i_1809_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1807_, v_sz_boxed_1811_, v_i_boxed_1812_, v_bs_1810_);
lean_dec_ref(v_xs_1807_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed(lean_object* v_xs_1814_, lean_object* v_i_1815_, lean_object* v_varDeps_1816_, lean_object* v_args_1817_, lean_object* v_body_1818_, lean_object* v_x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(v_xs_1814_, v_i_1815_, v_varDeps_1816_, v_args_1817_, v_body_1818_, v_x_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v_i_1815_);
return v_res_1827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1829_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1830_ = lean_unsigned_to_nat(30u);
v___x_1831_ = lean_unsigned_to_nat(254u);
v___x_1832_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__0));
v___x_1833_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1834_ = l_mkPanicMessageWithDecl(v___x_1833_, v___x_1832_, v___x_1831_, v___x_1830_, v___x_1829_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(lean_object* v_varDeps_1835_, lean_object* v_args_1836_, lean_object* v_f_1837_, lean_object* v_xs_1838_, lean_object* v_i_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = lean_array_get_size(v_args_1836_);
v___x_1848_ = lean_nat_dec_lt(v_i_1839_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v_a_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; 
lean_dec(v_i_1839_);
lean_dec_ref(v_args_1836_);
v___x_1849_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps___redArg(v_f_1837_, v_xs_1838_, v_varDeps_1835_, v_a_1841_);
lean_dec_ref(v_varDeps_1835_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1849_);
v___x_1851_ = 1;
v___x_1852_ = l_Lean_Meta_mkLetFVars(v_xs_1838_, v_a_1850_, v___x_1848_, v___x_1848_, v___x_1851_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
lean_dec_ref(v_xs_1838_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v___x_1854_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_1853_, v_a_1841_);
return v___x_1854_;
}
else
{
return v___x_1852_;
}
}
else
{
if (lean_obj_tag(v_f_1837_) == 6)
{
lean_object* v_binderName_1855_; lean_object* v_binderType_1856_; lean_object* v_body_1857_; lean_object* v_varPos_1858_; size_t v_sz_1859_; size_t v___x_1860_; lean_object* v_ys_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_binderName_1855_ = lean_ctor_get(v_f_1837_, 0);
lean_inc(v_binderName_1855_);
v_binderType_1856_ = lean_ctor_get(v_f_1837_, 1);
lean_inc_ref(v_binderType_1856_);
v_body_1857_ = lean_ctor_get(v_f_1837_, 2);
lean_inc_ref(v_body_1857_);
lean_dec_ref(v_f_1837_);
v_varPos_1858_ = lean_array_fget(v_varDeps_1835_, v_i_1839_);
v_sz_1859_ = lean_array_size(v_varPos_1858_);
v___x_1860_ = ((size_t)0ULL);
lean_inc(v_varPos_1858_);
v_ys_1861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__0(v_xs_1838_, v_sz_1859_, v___x_1860_, v_varPos_1858_);
v___x_1862_ = lean_array_fget_borrowed(v_args_1836_, v_i_1839_);
v___x_1863_ = 0;
lean_inc(v___x_1862_);
v___x_1864_ = l_Lean_Expr_betaRev(v___x_1862_, v_ys_1861_, v___x_1863_, v___x_1863_);
lean_dec_ref(v_ys_1861_);
v___x_1865_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1864_, v_a_1841_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___f_1867_; lean_object* v___x_1868_; lean_object* v_type_1869_; uint8_t v___x_1870_; lean_object* v___x_1871_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref(v___x_1865_);
v___f_1867_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1867_, 0, v_xs_1838_);
lean_closure_set(v___f_1867_, 1, v_i_1839_);
lean_closure_set(v___f_1867_, 2, v_varDeps_1835_);
lean_closure_set(v___f_1867_, 3, v_args_1836_);
lean_closure_set(v___f_1867_, 4, v_body_1857_);
v___x_1868_ = lean_array_get_size(v_varPos_1858_);
lean_dec(v_varPos_1858_);
v_type_1869_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_consumeForallN(v_binderType_1856_, v___x_1868_);
v___x_1870_ = 0;
v___x_1871_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__1___redArg(v_binderName_1855_, v_type_1869_, v_a_1866_, v___f_1867_, v___x_1848_, v___x_1870_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
return v___x_1871_;
}
else
{
lean_dec(v_varPos_1858_);
lean_dec_ref(v_body_1857_);
lean_dec_ref(v_binderType_1856_);
lean_dec(v_binderName_1855_);
lean_dec(v_i_1839_);
lean_dec_ref(v_xs_1838_);
lean_dec_ref(v_args_1836_);
lean_dec_ref(v_varDeps_1835_);
return v___x_1865_;
}
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
lean_dec(v_i_1839_);
lean_dec_ref(v_xs_1838_);
lean_dec_ref(v_f_1837_);
lean_dec_ref(v_args_1836_);
lean_dec_ref(v_varDeps_1835_);
v___x_1872_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___closed__1);
v___x_1873_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_1872_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
return v___x_1873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___lam__0(lean_object* v_xs_1874_, lean_object* v_i_1875_, lean_object* v_varDeps_1876_, lean_object* v_args_1877_, lean_object* v_body_1878_, lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_x_1879_, v___y_1881_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
v___x_1889_ = lean_array_push(v_xs_1874_, v_a_1888_);
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_nat_add(v_i_1875_, v___x_1890_);
v___x_1892_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1876_, v_args_1877_, v_body_1878_, v___x_1889_, v___x_1891_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1892_;
}
else
{
lean_dec_ref(v_body_1878_);
lean_dec_ref(v_args_1877_);
lean_dec_ref(v_varDeps_1876_);
lean_dec_ref(v_xs_1874_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg___boxed(lean_object* v_varDeps_1893_, lean_object* v_args_1894_, lean_object* v_f_1895_, lean_object* v_xs_1896_, lean_object* v_i_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1893_, v_args_1894_, v_f_1895_, v_xs_1896_, v_i_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(lean_object* v_varDeps_1906_, lean_object* v_args_1907_, lean_object* v___h_1908_, lean_object* v_f_1909_, lean_object* v_xs_1910_, lean_object* v_i_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1906_, v_args_1907_, v_f_1909_, v_xs_1910_, v_i_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___boxed(lean_object* v_varDeps_1920_, lean_object* v_args_1921_, lean_object* v___h_1922_, lean_object* v_f_1923_, lean_object* v_xs_1924_, lean_object* v_i_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go(v_varDeps_1920_, v_args_1921_, v___h_1922_, v_f_1923_, v_xs_1924_, v_i_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
return v_res_1933_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1935_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_1936_ = lean_unsigned_to_nat(40u);
v___x_1937_ = lean_unsigned_to_nat(251u);
v___x_1938_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__0));
v___x_1939_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_1940_ = l_mkPanicMessageWithDecl(v___x_1939_, v___x_1938_, v___x_1937_, v___x_1936_, v___x_1935_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(lean_object* v_varDeps_1941_, lean_object* v_x_1942_, lean_object* v_x_1943_, lean_object* v_x_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
if (lean_obj_tag(v_x_1942_) == 5)
{
lean_object* v_fn_1952_; lean_object* v_arg_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v_fn_1952_ = lean_ctor_get(v_x_1942_, 0);
lean_inc_ref(v_fn_1952_);
v_arg_1953_ = lean_ctor_get(v_x_1942_, 1);
lean_inc_ref(v_arg_1953_);
lean_dec_ref(v_x_1942_);
v___x_1954_ = lean_array_set(v_x_1943_, v_x_1944_, v_arg_1953_);
v___x_1955_ = lean_unsigned_to_nat(1u);
v___x_1956_ = lean_nat_sub(v_x_1944_, v___x_1955_);
lean_dec(v_x_1944_);
v_x_1942_ = v_fn_1952_;
v_x_1943_ = v___x_1954_;
v_x_1944_ = v___x_1956_;
goto _start;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
lean_dec(v_x_1944_);
v___x_1958_ = lean_array_get_size(v_x_1943_);
v___x_1959_ = lean_array_get_size(v_varDeps_1941_);
v___x_1960_ = lean_nat_dec_eq(v___x_1958_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec_ref(v_x_1943_);
lean_dec_ref(v_x_1942_);
lean_dec_ref(v_varDeps_1941_);
v___x_1961_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___closed__1);
v___x_1962_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go_spec__2(v___x_1961_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1962_;
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_toBetaApp___closed__0));
v___x_1965_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_go___redArg(v_varDeps_1941_, v_x_1943_, v_x_1942_, v___x_1964_, v___x_1963_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0___boxed(lean_object* v_varDeps_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_1966_, v_x_1967_, v_x_1968_, v_x_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1977_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0(void){
_start:
{
lean_object* v___x_1978_; lean_object* v_dummy_1979_; 
v___x_1978_ = lean_box(0);
v_dummy_1979_ = l_Lean_Expr_sort___override(v___x_1978_);
return v_dummy_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(lean_object* v_e_1980_, lean_object* v_varDeps_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v_dummy_1989_; lean_object* v_nargs_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_dummy_1989_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___closed__0);
v_nargs_1990_ = l_Lean_Expr_getAppNumArgs(v_e_1980_);
lean_inc(v_nargs_1990_);
v___x_1991_ = lean_mk_array(v_nargs_1990_, v_dummy_1989_);
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = lean_nat_sub(v_nargs_1990_, v___x_1992_);
lean_dec(v_nargs_1990_);
v___x_1994_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave_spec__0(v_varDeps_1981_, v_e_1980_, v___x_1991_, v___x_1993_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave___boxed(lean_object* v_e_1995_, lean_object* v_varDeps_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_1995_, v_varDeps_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(lean_object* v_argUnivs_2005_, lean_object* v_b_2006_){
_start:
{
lean_object* v_snd_2008_; lean_object* v_fst_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2042_; 
v_snd_2008_ = lean_ctor_get(v_b_2006_, 1);
v_fst_2009_ = lean_ctor_get(v_b_2006_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_b_2006_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2011_ = v_b_2006_;
v_isShared_2012_ = v_isSharedCheck_2042_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2009_);
lean_dec(v_b_2006_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2042_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_fst_2013_; lean_object* v_snd_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2041_; 
v_fst_2013_ = lean_ctor_get(v_snd_2008_, 0);
v_snd_2014_ = lean_ctor_get(v_snd_2008_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_snd_2008_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2016_ = v_snd_2008_;
v_isShared_2017_ = v_isSharedCheck_2041_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_snd_2014_);
lean_inc(v_fst_2013_);
lean_dec(v_snd_2008_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2041_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = lean_nat_dec_lt(v___x_2018_, v_fst_2013_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2021_; 
if (v_isShared_2017_ == 0)
{
v___x_2021_ = v___x_2016_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_fst_2013_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_snd_2014_);
v___x_2021_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v___x_2021_);
v___x_2023_ = v___x_2011_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_fst_2009_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
return v___x_2024_;
}
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_sub(v_fst_2013_, v___x_2027_);
lean_dec(v_fst_2013_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_array_get_borrowed(v___x_2029_, v_argUnivs_2005_, v___x_2028_);
lean_inc(v___x_2030_);
v___x_2031_ = l_Lean_mkLevelIMax_x27(v___x_2030_, v_fst_2009_);
v___x_2032_ = l_Lean_Level_normalize(v___x_2031_);
lean_dec(v___x_2031_);
lean_inc(v___x_2032_);
v___x_2033_ = lean_array_push(v_snd_2014_, v___x_2032_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 1, v___x_2033_);
lean_ctor_set(v___x_2016_, 0, v___x_2028_);
v___x_2035_ = v___x_2016_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v___x_2035_);
lean_ctor_set(v___x_2011_, 0, v___x_2032_);
v___x_2037_ = v___x_2011_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
v_b_2006_ = v___x_2037_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg___boxed(lean_object* v_argUnivs_2043_, lean_object* v_b_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2043_, v_b_2044_);
lean_dec_ref(v_argUnivs_2043_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(lean_object* v_type_2049_, lean_object* v_argUnivs_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
if (lean_obj_tag(v_type_2049_) == 7)
{
lean_object* v_binderType_2058_; lean_object* v_body_2059_; lean_object* v___x_2060_; 
v_binderType_2058_ = lean_ctor_get(v_type_2049_, 1);
lean_inc_ref(v_binderType_2058_);
v_body_2059_ = lean_ctor_get(v_type_2049_, 2);
lean_inc_ref(v_body_2059_);
lean_dec_ref(v_type_2049_);
v___x_2060_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2058_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2060_);
v___x_2062_ = lean_array_push(v_argUnivs_2050_, v_a_2061_);
v_type_2049_ = v_body_2059_;
v_argUnivs_2050_ = v___x_2062_;
goto _start;
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v_body_2059_);
lean_dec_ref(v_argUnivs_2050_);
v_a_2064_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2060_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2060_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_2049_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
v___x_2074_ = lean_array_get_size(v_argUnivs_2050_);
v___x_2075_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_a_2073_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2050_, v___x_2077_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2097_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2097_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2097_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_snd_2083_; lean_object* v_snd_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2095_; 
v_snd_2083_ = lean_ctor_get(v_a_2079_, 1);
lean_inc(v_snd_2083_);
lean_dec(v_a_2079_);
v_snd_2084_ = lean_ctor_get(v_snd_2083_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_snd_2083_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v_snd_2083_, 0);
lean_dec(v_unused_2096_);
v___x_2086_ = v_snd_2083_;
v_isShared_2087_ = v_isSharedCheck_2095_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_snd_2084_);
lean_dec(v_snd_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2095_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = l_Array_reverse___redArg(v_snd_2084_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v___x_2088_);
lean_ctor_set(v___x_2086_, 0, v_argUnivs_2050_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_argUnivs_2050_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2092_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2090_);
v___x_2092_ = v___x_2081_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref(v_argUnivs_2050_);
v_a_2098_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2078_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2078_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec_ref(v_argUnivs_2050_);
v_a_2106_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2072_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2072_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___boxed(lean_object* v_type_2114_, lean_object* v_argUnivs_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_type_2114_, v_argUnivs_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(lean_object* v_argUnivs_2124_, lean_object* v_b_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___redArg(v_argUnivs_2124_, v_b_2125_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0___boxed(lean_object* v_argUnivs_2134_, lean_object* v_b_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go_spec__0(v_argUnivs_2134_, v_b_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec_ref(v_argUnivs_2134_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(lean_object* v_fType_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go___closed__0));
v___x_2153_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs_go(v_fType_2144_, v___x_2152_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs___boxed(lean_object* v_fType_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(lean_object* v_fnUnivs_2163_, lean_object* v_argUnivs_2164_, lean_object* v_declName_2165_, lean_object* v_fType_2166_, lean_object* v_i_2167_){
_start:
{
lean_object* v___x_2169_; lean_object* v_00_u03b1_2170_; lean_object* v_00_u03b2_2171_; lean_object* v_u_2172_; lean_object* v_v_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2169_ = lean_box(0);
v_00_u03b1_2170_ = l_Lean_Expr_bindingDomain_x21(v_fType_2166_);
v_00_u03b2_2171_ = l_Lean_Expr_bindingBody_x21(v_fType_2166_);
v_u_2172_ = lean_array_get_borrowed(v___x_2169_, v_argUnivs_2164_, v_i_2167_);
v_v_2173_ = lean_array_get_borrowed(v___x_2169_, v_fnUnivs_2163_, v_i_2167_);
v___x_2174_ = lean_box(0);
lean_inc(v_v_2173_);
v___x_2175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2175_, 0, v_v_2173_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
lean_inc(v_u_2172_);
v___x_2176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2176_, 0, v_u_2172_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = l_Lean_mkConst(v_declName_2165_, v___x_2176_);
v___x_2178_ = l_Lean_mkAppB(v___x_2177_, v_00_u03b1_2170_, v_00_u03b2_2171_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg___boxed(lean_object* v_fnUnivs_2180_, lean_object* v_argUnivs_2181_, lean_object* v_declName_2182_, lean_object* v_fType_2183_, lean_object* v_i_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2180_, v_argUnivs_2181_, v_declName_2182_, v_fType_2183_, v_i_2184_);
lean_dec(v_i_2184_);
lean_dec_ref(v_fType_2183_);
lean_dec_ref(v_argUnivs_2181_);
lean_dec_ref(v_fnUnivs_2180_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(lean_object* v_fnUnivs_2187_, lean_object* v_argUnivs_2188_, lean_object* v_declName_2189_, lean_object* v_fType_2190_, lean_object* v_i_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2187_, v_argUnivs_2188_, v_declName_2189_, v_fType_2190_, v_i_2191_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___boxed(lean_object* v_fnUnivs_2200_, lean_object* v_argUnivs_2201_, lean_object* v_declName_2202_, lean_object* v_fType_2203_, lean_object* v_i_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix(v_fnUnivs_2200_, v_argUnivs_2201_, v_declName_2202_, v_fType_2203_, v_i_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_i_2204_);
lean_dec_ref(v_fType_2203_);
lean_dec_ref(v_argUnivs_2201_);
lean_dec_ref(v_fnUnivs_2200_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(lean_object* v_f_2213_, lean_object* v_a_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___y_2223_; lean_object* v___x_2226_; uint8_t v_debug_2227_; 
v___x_2226_ = lean_st_ref_get(v___y_2216_);
v_debug_2227_ = lean_ctor_get_uint8(v___x_2226_, sizeof(void*)*9);
lean_dec(v___x_2226_);
if (v_debug_2227_ == 0)
{
v___y_2223_ = v___y_2216_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2228_; 
lean_inc_ref(v_f_2213_);
v___x_2228_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2213_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref(v___x_2228_);
lean_inc_ref(v_a_2214_);
v___x_2229_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_dec_ref(v___x_2229_);
v___y_2223_ = v___y_2216_;
goto v___jp_2222_;
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_a_2214_);
lean_dec_ref(v_f_2213_);
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_a_2214_);
lean_dec_ref(v_f_2213_);
v_a_2238_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2228_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2228_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
v___jp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = l_Lean_Expr_app___override(v_f_2213_, v_a_2214_);
v___x_2225_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2224_, v___y_2223_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg___boxed(lean_object* v_f_2246_, lean_object* v_a_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2246_, v_a_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(lean_object* v_f_2256_, lean_object* v_a_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_f_2256_, v_a_2257_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___boxed(lean_object* v_f_2269_, lean_object* v_a_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0(v_f_2269_, v_a_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
return v_res_2281_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(lean_object* v_msg_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_15370__overap_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___closed__0);
v___x_15370__overap_2295_ = lean_panic_fn_borrowed(v___x_2294_, v_msg_2283_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2291_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2287_);
lean_inc(v___y_2286_);
lean_inc_ref(v___y_2285_);
lean_inc(v___y_2284_);
v___x_2296_ = lean_apply_10(v___x_15370__overap_2295_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, lean_box(0));
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1___boxed(lean_object* v_msg_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v_msg_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
return v_res_2308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_elimAuxApps_spec__3___closed__2));
v___x_2320_ = lean_unsigned_to_nat(11u);
v___x_2321_ = lean_unsigned_to_nat(346u);
v___x_2322_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__6));
v___x_2323_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__4));
v___x_2324_ = l_mkPanicMessageWithDecl(v___x_2323_, v___x_2322_, v___x_2321_, v___x_2320_, v___x_2319_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(lean_object* v_fType_2325_, lean_object* v_fnUnivs_2326_, lean_object* v_argUnivs_2327_, lean_object* v_simpBody_2328_, lean_object* v_e_2329_, lean_object* v_i_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
switch(lean_obj_tag(v_e_2329_))
{
case 5:
{
lean_object* v_fn_2341_; lean_object* v_arg_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_fn_2341_ = lean_ctor_get(v_e_2329_, 0);
lean_inc_ref(v_fn_2341_);
v_arg_2342_ = lean_ctor_get(v_e_2329_, 1);
lean_inc_ref(v_arg_2342_);
lean_dec_ref(v_e_2329_);
v___x_2343_ = lean_unsigned_to_nat(1u);
v___x_2344_ = lean_nat_sub(v_i_2330_, v___x_2343_);
lean_inc_ref(v_fn_2341_);
v___x_2345_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2325_, v_fnUnivs_2326_, v_argUnivs_2327_, v_simpBody_2328_, v_fn_2341_, v___x_2344_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v___x_2344_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2466_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2466_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2466_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_fst_2350_; lean_object* v_snd_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2465_; 
v_fst_2350_ = lean_ctor_get(v_a_2346_, 0);
v_snd_2351_ = lean_ctor_get(v_a_2346_, 1);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_a_2346_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2353_ = v_a_2346_;
v_isShared_2354_ = v_isSharedCheck_2465_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_snd_2351_);
lean_inc(v_fst_2350_);
lean_dec(v_a_2346_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2465_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_r_2356_; lean_object* v___x_2364_; 
lean_inc(v_a_2339_);
lean_inc_ref(v_a_2338_);
lean_inc(v_a_2337_);
lean_inc_ref(v_a_2336_);
lean_inc(v_a_2335_);
lean_inc_ref(v_a_2334_);
lean_inc(v_a_2333_);
lean_inc_ref(v_a_2332_);
lean_inc(v_a_2331_);
lean_inc_ref(v_arg_2342_);
v___x_2364_ = lean_sym_simp(v_arg_2342_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; uint8_t v___y_2367_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref(v___x_2364_);
if (lean_obj_tag(v_fst_2350_) == 0)
{
if (lean_obj_tag(v_a_2365_) == 0)
{
uint8_t v_contextDependent_2369_; 
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_fn_2341_);
v_contextDependent_2369_ = lean_ctor_get_uint8(v_fst_2350_, 1);
lean_dec_ref(v_fst_2350_);
if (v_contextDependent_2369_ == 0)
{
uint8_t v_contextDependent_2370_; 
v_contextDependent_2370_ = lean_ctor_get_uint8(v_a_2365_, 1);
lean_dec_ref(v_a_2365_);
v___y_2367_ = v_contextDependent_2370_;
goto v___jp_2366_;
}
else
{
lean_dec_ref(v_a_2365_);
v___y_2367_ = v_contextDependent_2369_;
goto v___jp_2366_;
}
}
else
{
uint8_t v_contextDependent_2371_; lean_object* v_e_x27_2372_; lean_object* v_proof_2373_; uint8_t v_contextDependent_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2398_; 
v_contextDependent_2371_ = lean_ctor_get_uint8(v_fst_2350_, 1);
lean_dec_ref(v_fst_2350_);
v_e_x27_2372_ = lean_ctor_get(v_a_2365_, 0);
v_proof_2373_ = lean_ctor_get(v_a_2365_, 1);
v_contextDependent_2374_ = lean_ctor_get_uint8(v_a_2365_, sizeof(void*)*2 + 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_a_2365_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2376_ = v_a_2365_;
v_isShared_2377_ = v_isSharedCheck_2398_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_proof_2373_);
lean_inc(v_e_x27_2372_);
lean_dec(v_a_2365_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2398_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; 
lean_inc_ref(v_e_x27_2372_);
lean_inc_ref(v_fn_2341_);
v___x_2378_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_fn_2341_, v_e_x27_2372_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_a_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; uint8_t v___y_2386_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__1));
v___x_2381_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2326_, v_argUnivs_2327_, v___x_2380_, v_snd_2351_, v_i_2330_);
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = l_Lean_mkApp4(v_a_2382_, v_arg_2342_, v_e_x27_2372_, v_fn_2341_, v_proof_2373_);
v___x_2384_ = 0;
if (v_contextDependent_2371_ == 0)
{
v___y_2386_ = v_contextDependent_2374_;
goto v___jp_2385_;
}
else
{
v___y_2386_ = v_contextDependent_2371_;
goto v___jp_2385_;
}
v___jp_2385_:
{
lean_object* v___x_2388_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v___x_2383_);
lean_ctor_set(v___x_2376_, 0, v_a_2379_);
v___x_2388_ = v___x_2376_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2379_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___x_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*2, v___x_2384_);
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*2 + 1, v___y_2386_);
v_r_2356_ = v___x_2388_;
goto v___jp_2355_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_del_object(v___x_2376_);
lean_dec_ref(v_proof_2373_);
lean_dec_ref(v_e_x27_2372_);
lean_del_object(v___x_2353_);
lean_dec(v_snd_2351_);
lean_del_object(v___x_2348_);
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_fn_2341_);
v_a_2390_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2378_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2378_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_a_2365_) == 0)
{
lean_object* v_e_x27_2399_; lean_object* v_proof_2400_; uint8_t v_contextDependent_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2426_; 
v_e_x27_2399_ = lean_ctor_get(v_fst_2350_, 0);
v_proof_2400_ = lean_ctor_get(v_fst_2350_, 1);
v_contextDependent_2401_ = lean_ctor_get_uint8(v_fst_2350_, sizeof(void*)*2 + 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_fst_2350_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2403_ = v_fst_2350_;
v_isShared_2404_ = v_isSharedCheck_2426_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_proof_2400_);
lean_inc(v_e_x27_2399_);
lean_dec(v_fst_2350_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2426_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
uint8_t v_contextDependent_2405_; lean_object* v___x_2406_; 
v_contextDependent_2405_ = lean_ctor_get_uint8(v_a_2365_, 1);
lean_dec_ref(v_a_2365_);
lean_inc_ref(v_arg_2342_);
lean_inc_ref(v_e_x27_2399_);
v___x_2406_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2399_, v_arg_2342_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v_a_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; uint8_t v___y_2414_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v___x_2408_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__3));
v___x_2409_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2326_, v_argUnivs_2327_, v___x_2408_, v_snd_2351_, v_i_2330_);
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = l_Lean_mkApp4(v_a_2410_, v_fn_2341_, v_e_x27_2399_, v_proof_2400_, v_arg_2342_);
v___x_2412_ = 0;
if (v_contextDependent_2401_ == 0)
{
v___y_2414_ = v_contextDependent_2405_;
goto v___jp_2413_;
}
else
{
v___y_2414_ = v_contextDependent_2401_;
goto v___jp_2413_;
}
v___jp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v___x_2411_);
lean_ctor_set(v___x_2403_, 0, v_a_2407_);
v___x_2416_ = v___x_2403_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2407_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*2, v___x_2412_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*2 + 1, v___y_2414_);
v_r_2356_ = v___x_2416_;
goto v___jp_2355_;
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_del_object(v___x_2403_);
lean_dec_ref(v_proof_2400_);
lean_dec_ref(v_e_x27_2399_);
lean_del_object(v___x_2353_);
lean_dec(v_snd_2351_);
lean_del_object(v___x_2348_);
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_fn_2341_);
v_a_2418_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2406_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2406_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2427_; lean_object* v_proof_2428_; uint8_t v_contextDependent_2429_; lean_object* v_e_x27_2430_; lean_object* v_proof_2431_; uint8_t v_contextDependent_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2456_; 
v_e_x27_2427_ = lean_ctor_get(v_fst_2350_, 0);
lean_inc_ref(v_e_x27_2427_);
v_proof_2428_ = lean_ctor_get(v_fst_2350_, 1);
lean_inc_ref(v_proof_2428_);
v_contextDependent_2429_ = lean_ctor_get_uint8(v_fst_2350_, sizeof(void*)*2 + 1);
lean_dec_ref(v_fst_2350_);
v_e_x27_2430_ = lean_ctor_get(v_a_2365_, 0);
v_proof_2431_ = lean_ctor_get(v_a_2365_, 1);
v_contextDependent_2432_ = lean_ctor_get_uint8(v_a_2365_, sizeof(void*)*2 + 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_a_2365_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2434_ = v_a_2365_;
v_isShared_2435_ = v_isSharedCheck_2456_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_proof_2431_);
lean_inc(v_e_x27_2430_);
lean_dec(v_a_2365_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2456_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; 
lean_inc_ref(v_e_x27_2430_);
lean_inc_ref(v_e_x27_2427_);
v___x_2436_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__0___redArg(v_e_x27_2427_, v_e_x27_2430_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_a_2440_; lean_object* v___x_2441_; uint8_t v___x_2442_; uint8_t v___y_2444_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__5));
v___x_2439_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_mkCongrPrefix___redArg(v_fnUnivs_2326_, v_argUnivs_2327_, v___x_2438_, v_snd_2351_, v_i_2330_);
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___x_2439_);
v___x_2441_ = l_Lean_mkApp6(v_a_2440_, v_fn_2341_, v_e_x27_2427_, v_arg_2342_, v_e_x27_2430_, v_proof_2428_, v_proof_2431_);
v___x_2442_ = 0;
if (v_contextDependent_2429_ == 0)
{
v___y_2444_ = v_contextDependent_2432_;
goto v___jp_2443_;
}
else
{
v___y_2444_ = v_contextDependent_2429_;
goto v___jp_2443_;
}
v___jp_2443_:
{
lean_object* v___x_2446_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 1, v___x_2441_);
lean_ctor_set(v___x_2434_, 0, v_a_2437_);
v___x_2446_ = v___x_2434_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2437_);
lean_ctor_set(v_reuseFailAlloc_2447_, 1, v___x_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*2, v___x_2442_);
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*2 + 1, v___y_2444_);
v_r_2356_ = v___x_2446_;
goto v___jp_2355_;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_del_object(v___x_2434_);
lean_dec_ref(v_proof_2431_);
lean_dec_ref(v_e_x27_2430_);
lean_dec_ref(v_proof_2428_);
lean_dec_ref(v_e_x27_2427_);
lean_del_object(v___x_2353_);
lean_dec(v_snd_2351_);
lean_del_object(v___x_2348_);
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_fn_2341_);
v_a_2448_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2436_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2436_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
}
v___jp_2366_:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_2367_);
v_r_2356_ = v___x_2368_;
goto v___jp_2355_;
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_del_object(v___x_2353_);
lean_dec(v_snd_2351_);
lean_dec(v_fst_2350_);
lean_del_object(v___x_2348_);
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_fn_2341_);
v_a_2457_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2364_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2364_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
v___jp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = l_Lean_Expr_bindingBody_x21(v_snd_2351_);
lean_dec(v_snd_2351_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v___x_2357_);
lean_ctor_set(v___x_2353_, 0, v_r_2356_);
v___x_2359_ = v___x_2353_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_r_2356_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2361_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2359_);
v___x_2361_ = v___x_2348_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2342_);
lean_dec_ref(v_fn_2341_);
return v___x_2345_;
}
}
case 6:
{
lean_object* v___x_2467_; 
lean_inc(v_a_2339_);
lean_inc_ref(v_a_2338_);
lean_inc(v_a_2337_);
lean_inc_ref(v_a_2336_);
lean_inc(v_a_2335_);
lean_inc_ref(v_a_2334_);
lean_inc(v_a_2333_);
lean_inc_ref(v_a_2332_);
lean_inc(v_a_2331_);
v___x_2467_ = lean_apply_11(v_simpBody_2328_, v_e_2329_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, lean_box(0));
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2476_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2476_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2476_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2472_, 0, v_a_2468_);
lean_ctor_set(v___x_2472_, 1, v_fType_2325_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2472_);
v___x_2474_ = v___x_2470_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_fType_2325_);
v_a_2477_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2467_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2467_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
default: 
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v_e_2329_);
lean_dec_ref(v_simpBody_2328_);
lean_dec_ref(v_fType_2325_);
v___x_2485_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7, &l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7_once, _init_l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___closed__7);
v___x_2486_ = l_panic___at___00__private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go_spec__1(v___x_2485_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
return v___x_2486_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go___boxed(lean_object* v_fType_2487_, lean_object* v_fnUnivs_2488_, lean_object* v_argUnivs_2489_, lean_object* v_simpBody_2490_, lean_object* v_e_2491_, lean_object* v_i_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2487_, v_fnUnivs_2488_, v_argUnivs_2489_, v_simpBody_2490_, v_e_2491_, v_i_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec(v_i_2492_);
lean_dec_ref(v_argUnivs_2489_);
lean_dec_ref(v_fnUnivs_2488_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(lean_object* v_e_2504_, lean_object* v_fType_2505_, lean_object* v_fnUnivs_2506_, lean_object* v_argUnivs_2507_, lean_object* v_simpBody_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_numArgs_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v_numArgs_2519_ = lean_array_get_size(v_argUnivs_2507_);
v___x_2520_ = lean_unsigned_to_nat(1u);
v___x_2521_ = lean_nat_sub(v_numArgs_2519_, v___x_2520_);
v___x_2522_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp_go(v_fType_2505_, v_fnUnivs_2506_, v_argUnivs_2507_, v_simpBody_2508_, v_e_2504_, v___x_2521_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v___x_2521_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2531_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_fst_2527_; lean_object* v___x_2529_; 
v_fst_2527_ = lean_ctor_get(v_a_2523_, 0);
lean_inc(v_fst_2527_);
lean_dec(v_a_2523_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_fst_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_fst_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_a_2532_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2522_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2522_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp___boxed(lean_object* v_e_2540_, lean_object* v_fType_2541_, lean_object* v_fnUnivs_2542_, lean_object* v_argUnivs_2543_, lean_object* v_simpBody_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2540_, v_fType_2541_, v_fnUnivs_2542_, v_argUnivs_2543_, v_simpBody_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_argUnivs_2543_);
lean_dec_ref(v_fnUnivs_2542_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(lean_object* v_e_2560_, lean_object* v_simpBody_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___x_2572_; 
lean_inc_ref(v_e_2560_);
v___x_2572_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_2560_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v_00_u03b1_2574_; lean_object* v_u_2575_; lean_object* v_e_2576_; lean_object* v_h_2577_; lean_object* v_varDeps_2578_; lean_object* v_fType_2579_; lean_object* v___x_2580_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref(v___x_2572_);
v_00_u03b1_2574_ = lean_ctor_get(v_a_2573_, 0);
lean_inc_ref(v_00_u03b1_2574_);
v_u_2575_ = lean_ctor_get(v_a_2573_, 1);
lean_inc(v_u_2575_);
v_e_2576_ = lean_ctor_get(v_a_2573_, 2);
lean_inc_ref(v_e_2576_);
v_h_2577_ = lean_ctor_get(v_a_2573_, 3);
lean_inc_ref(v_h_2577_);
v_varDeps_2578_ = lean_ctor_get(v_a_2573_, 4);
lean_inc_ref(v_varDeps_2578_);
v_fType_2579_ = lean_ctor_get(v_a_2573_, 5);
lean_inc_ref(v_fType_2579_);
lean_dec(v_a_2573_);
lean_inc_ref(v_fType_2579_);
v___x_2580_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_getUnivs(v_fType_2579_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v_argUnivs_2582_; lean_object* v_fnUnivs_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2651_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref(v___x_2580_);
v_argUnivs_2582_ = lean_ctor_get(v_a_2581_, 0);
v_fnUnivs_2583_ = lean_ctor_get(v_a_2581_, 1);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_a_2581_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2585_ = v_a_2581_;
v_isShared_2586_ = v_isSharedCheck_2651_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_fnUnivs_2583_);
lean_inc(v_argUnivs_2582_);
lean_dec(v_a_2581_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2651_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; 
lean_inc_ref(v_e_2576_);
v___x_2587_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpBetaApp(v_e_2576_, v_fType_2579_, v_fnUnivs_2583_, v_argUnivs_2582_, v_simpBody_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
lean_dec_ref(v_argUnivs_2582_);
lean_dec_ref(v_fnUnivs_2583_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2642_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2642_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2642_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
if (lean_obj_tag(v_a_2588_) == 0)
{
uint8_t v_contextDependent_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_del_object(v___x_2585_);
lean_dec_ref(v_varDeps_2578_);
lean_dec_ref(v_h_2577_);
lean_dec_ref(v_e_2576_);
lean_dec_ref(v_e_2560_);
v_contextDependent_2592_ = lean_ctor_get_uint8(v_a_2588_, 1);
lean_dec_ref(v_a_2588_);
v___x_2593_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2592_);
v___x_2594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v_00_u03b1_2574_);
lean_ctor_set(v___x_2594_, 2, v_u_2575_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2594_);
v___x_2596_ = v___x_2590_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
else
{
lean_object* v_e_x27_2598_; lean_object* v_proof_2599_; uint8_t v_contextDependent_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2641_; 
lean_del_object(v___x_2590_);
v_e_x27_2598_ = lean_ctor_get(v_a_2588_, 0);
v_proof_2599_ = lean_ctor_get(v_a_2588_, 1);
v_contextDependent_2600_ = lean_ctor_get_uint8(v_a_2588_, sizeof(void*)*2 + 1);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_a_2588_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2602_ = v_a_2588_;
v_isShared_2603_ = v_isSharedCheck_2641_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_proof_2599_);
lean_inc(v_e_x27_2598_);
lean_dec(v_a_2588_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2641_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2605_ = lean_box(0);
lean_inc(v_u_2575_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 1);
lean_ctor_set(v___x_2585_, 1, v___x_2605_);
lean_ctor_set(v___x_2585_, 0, v_u_2575_);
v___x_2607_ = v___x_2585_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_u_2575_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_inc_ref(v___x_2607_);
v___x_2608_ = l_Lean_mkConst(v___x_2604_, v___x_2607_);
lean_inc_ref(v_e_x27_2598_);
lean_inc_ref(v_e_2560_);
lean_inc_ref(v_00_u03b1_2574_);
lean_inc_ref(v___x_2608_);
v___x_2609_ = l_Lean_mkApp6(v___x_2608_, v_00_u03b1_2574_, v_e_2560_, v_e_2576_, v_e_x27_2598_, v_h_2577_, v_proof_2599_);
lean_inc_ref(v_e_x27_2598_);
v___x_2610_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toHave(v_e_x27_2598_, v_varDeps_2578_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2631_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2631_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2631_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; lean_object* v___x_2625_; 
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__1));
lean_inc_ref(v___x_2607_);
v___x_2616_ = l_Lean_mkConst(v___x_2615_, v___x_2607_);
lean_inc(v_a_2611_);
lean_inc_ref(v_e_x27_2598_);
lean_inc_ref(v_00_u03b1_2574_);
v___x_2617_ = l_Lean_mkApp3(v___x_2616_, v_00_u03b1_2574_, v_e_x27_2598_, v_a_2611_);
v___x_2618_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2619_ = l_Lean_mkConst(v___x_2618_, v___x_2607_);
lean_inc_ref(v_e_x27_2598_);
lean_inc_ref(v_00_u03b1_2574_);
v___x_2620_ = l_Lean_mkAppB(v___x_2619_, v_00_u03b1_2574_, v_e_x27_2598_);
v___x_2621_ = l_Lean_Meta_mkExpectedPropHint(v___x_2620_, v___x_2617_);
lean_inc(v_a_2611_);
lean_inc_ref(v_00_u03b1_2574_);
v___x_2622_ = l_Lean_mkApp6(v___x_2608_, v_00_u03b1_2574_, v_e_2560_, v_e_x27_2598_, v_a_2611_, v___x_2609_, v___x_2621_);
v___x_2623_ = 0;
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v___x_2622_);
lean_ctor_set(v___x_2602_, 0, v_a_2611_);
v___x_2625_ = v___x_2602_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2611_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v___x_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2630_, sizeof(void*)*2 + 1, v_contextDependent_2600_);
v___x_2625_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_ctor_set_uint8(v___x_2625_, sizeof(void*)*2, v___x_2623_);
v___x_2626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v_00_u03b1_2574_);
lean_ctor_set(v___x_2626_, 2, v_u_2575_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2626_);
v___x_2628_ = v___x_2613_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v___x_2609_);
lean_dec_ref(v___x_2608_);
lean_dec_ref(v___x_2607_);
lean_del_object(v___x_2602_);
lean_dec_ref(v_e_x27_2598_);
lean_dec(v_u_2575_);
lean_dec_ref(v_00_u03b1_2574_);
lean_dec_ref(v_e_2560_);
v_a_2632_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2610_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2610_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_del_object(v___x_2585_);
lean_dec_ref(v_varDeps_2578_);
lean_dec_ref(v_h_2577_);
lean_dec_ref(v_e_2576_);
lean_dec(v_u_2575_);
lean_dec_ref(v_00_u03b1_2574_);
lean_dec_ref(v_e_2560_);
v_a_2643_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2587_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2587_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec_ref(v_fType_2579_);
lean_dec_ref(v_varDeps_2578_);
lean_dec_ref(v_h_2577_);
lean_dec_ref(v_e_2576_);
lean_dec(v_u_2575_);
lean_dec_ref(v_00_u03b1_2574_);
lean_dec_ref(v_simpBody_2561_);
lean_dec_ref(v_e_2560_);
v_a_2652_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2580_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2580_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec_ref(v_simpBody_2561_);
lean_dec_ref(v_e_2560_);
v_a_2660_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2572_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2572_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___boxed(lean_object* v_e_2668_, lean_object* v_simpBody_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2668_, v_simpBody_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave(lean_object* v_e_2681_, lean_object* v_simpBody_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_2681_, v_simpBody_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2702_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2702_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2702_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v_result_2698_; lean_object* v___x_2700_; 
v_result_2698_ = lean_ctor_get(v_a_2694_, 0);
lean_inc_ref(v_result_2698_);
lean_dec(v_a_2694_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v_result_2698_);
v___x_2700_ = v___x_2696_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_result_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_a_2703_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2693_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2693_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHave___boxed(lean_object* v_e_2711_, lean_object* v_simpBody_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Meta_Sym_Simp_simpHave(v_e_2711_, v_simpBody_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(lean_object* v_e_u2081_2724_, lean_object* v_simpBody_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v___x_2736_; 
lean_inc_ref(v_e_u2081_2724_);
v___x_2736_ = l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore(v_e_u2081_2724_, v_simpBody_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v_result_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref(v___x_2736_);
v_result_2738_ = lean_ctor_get(v_a_2737_, 0);
lean_inc_ref(v_result_2738_);
if (lean_obj_tag(v_result_2738_) == 0)
{
lean_object* v_00_u03b1_2739_; lean_object* v_u_2740_; uint8_t v_contextDependent_2741_; lean_object* v___x_2742_; 
v_00_u03b1_2739_ = lean_ctor_get(v_a_2737_, 1);
lean_inc_ref(v_00_u03b1_2739_);
v_u_2740_ = lean_ctor_get(v_a_2737_, 2);
lean_inc(v_u_2740_);
lean_dec(v_a_2737_);
v_contextDependent_2741_ = lean_ctor_get_uint8(v_result_2738_, 1);
lean_dec_ref(v_result_2738_);
lean_inc_ref(v_e_u2081_2724_);
v___x_2742_ = l_Lean_Meta_zetaUnused(v_e_u2081_2724_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2761_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2761_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2761_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
uint8_t v___x_2747_; 
v___x_2747_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_u2081_2724_, v_a_2743_);
lean_dec_ref(v_e_u2081_2724_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2749_ = lean_box(0);
v___x_2750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_u_2740_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = l_Lean_mkConst(v___x_2748_, v___x_2750_);
lean_inc(v_a_2743_);
v___x_2752_ = l_Lean_mkAppB(v___x_2751_, v_00_u03b1_2739_, v_a_2743_);
v___x_2753_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2753_, 0, v_a_2743_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
lean_ctor_set_uint8(v___x_2753_, sizeof(void*)*2, v___x_2747_);
lean_ctor_set_uint8(v___x_2753_, sizeof(void*)*2 + 1, v_contextDependent_2741_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2753_);
v___x_2755_ = v___x_2745_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_dec(v_a_2743_);
lean_dec(v_u_2740_);
lean_dec_ref(v_00_u03b1_2739_);
v___x_2757_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_2741_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2757_);
v___x_2759_ = v___x_2745_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_u_2740_);
lean_dec_ref(v_00_u03b1_2739_);
lean_dec_ref(v_e_u2081_2724_);
v_a_2762_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2742_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2742_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_00_u03b1_2770_; lean_object* v_u_2771_; lean_object* v_e_x27_2772_; lean_object* v_proof_2773_; uint8_t v_contextDependent_2774_; lean_object* v___x_2775_; 
v_00_u03b1_2770_ = lean_ctor_get(v_a_2737_, 1);
lean_inc_ref(v_00_u03b1_2770_);
v_u_2771_ = lean_ctor_get(v_a_2737_, 2);
lean_inc(v_u_2771_);
lean_dec(v_a_2737_);
v_e_x27_2772_ = lean_ctor_get(v_result_2738_, 0);
v_proof_2773_ = lean_ctor_get(v_result_2738_, 1);
v_contextDependent_2774_ = lean_ctor_get_uint8(v_result_2738_, sizeof(void*)*2 + 1);
lean_inc_ref(v_e_x27_2772_);
v___x_2775_ = l_Lean_Meta_zetaUnused(v_e_x27_2772_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2804_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2804_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2804_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
uint8_t v___x_2780_; 
v___x_2780_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_x27_2772_, v_a_2776_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2798_; 
lean_inc_ref(v_proof_2773_);
lean_inc_ref(v_e_x27_2772_);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_result_2738_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; lean_object* v_unused_2800_; 
v_unused_2799_ = lean_ctor_get(v_result_2738_, 1);
lean_dec(v_unused_2799_);
v_unused_2800_ = lean_ctor_get(v_result_2738_, 0);
lean_dec(v_unused_2800_);
v___x_2782_ = v_result_2738_;
v_isShared_2783_ = v_isSharedCheck_2798_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v_result_2738_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2798_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2784_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_simpHaveCore___closed__1));
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v_u_2771_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
lean_inc_ref(v___x_2786_);
v___x_2787_ = l_Lean_mkConst(v___x_2784_, v___x_2786_);
v___x_2788_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Have_0__Lean_Meta_Sym_Simp_toBetaApp_go___closed__3));
v___x_2789_ = l_Lean_mkConst(v___x_2788_, v___x_2786_);
lean_inc(v_a_2776_);
lean_inc_ref(v_00_u03b1_2770_);
v___x_2790_ = l_Lean_mkAppB(v___x_2789_, v_00_u03b1_2770_, v_a_2776_);
lean_inc(v_a_2776_);
v___x_2791_ = l_Lean_mkApp6(v___x_2787_, v_00_u03b1_2770_, v_e_u2081_2724_, v_e_x27_2772_, v_a_2776_, v_proof_2773_, v___x_2790_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 1, v___x_2791_);
lean_ctor_set(v___x_2782_, 0, v_a_2776_);
v___x_2793_ = v___x_2782_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2776_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2791_);
lean_ctor_set_uint8(v_reuseFailAlloc_2797_, sizeof(void*)*2 + 1, v_contextDependent_2774_);
v___x_2793_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2795_; 
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*2, v___x_2780_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2793_);
v___x_2795_ = v___x_2778_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
else
{
lean_object* v___x_2802_; 
lean_dec(v_a_2776_);
lean_dec(v_u_2771_);
lean_dec_ref(v_00_u03b1_2770_);
lean_dec_ref(v_e_u2081_2724_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v_result_2738_);
v___x_2802_ = v___x_2778_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_result_2738_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v_u_2771_);
lean_dec_ref(v_00_u03b1_2770_);
lean_dec_ref(v_result_2738_);
lean_dec_ref(v_e_u2081_2724_);
v_a_2805_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2775_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2775_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v_e_u2081_2724_);
v_a_2813_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2736_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2736_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused___boxed(lean_object* v_e_u2081_2821_, lean_object* v_simpBody_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_u2081_2821_, v_simpBody_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27(lean_object* v_simpBody_2834_, lean_object* v_e_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
uint8_t v___x_2846_; 
v___x_2846_ = l_Lean_Expr_letNondep_x21(v_e_2835_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec_ref(v_e_2835_);
lean_dec_ref(v_simpBody_2834_);
v___x_2847_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2847_, 0, v___x_2846_);
lean_ctor_set_uint8(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
else
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Meta_Sym_Simp_simpHaveAndZetaUnused(v_e_2835_, v_simpBody_2834_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
return v___x_2849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet_x27___boxed(lean_object* v_simpBody_2850_, lean_object* v_e_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v_simpBody_2850_, v_e_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet(lean_object* v_e_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpLet___closed__0));
v___x_2876_ = l_Lean_Meta_Sym_Simp_simpLet_x27(v___x_2875_, v_e_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpLet___boxed(lean_object* v_e_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_Meta_Sym_Simp_simpLet(v_e_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
return v_res_2888_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HaveTelescope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HaveTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default = _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult_default);
l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult = _init_l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedToBetaAppResult);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Lambda(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_HaveTelescope(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Have(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HaveTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Have(builtin);
}
#ifdef __cplusplus
}
#endif
