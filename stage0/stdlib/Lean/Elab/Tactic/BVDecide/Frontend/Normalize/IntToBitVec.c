// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.IntToBitVec
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClearMany_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Platform"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numBits"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 13, 33, 186, 170, 198, 65, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(lean_object*, lean_object*, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "z"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 196, 150, 181, 147, 170, 254, 79)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(250, 240, 184, 175, 50, 245, 157, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "failed to create binder due to failure when reverting variable dependencies"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "Detected USize/ISize in the goal but no hypothesis about System.Platform.numBits, consider case splitting on "};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numBits_eq"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(128, 236, 129, 7, 244, 3, 115, 42)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 163, 238, 100, 187, 225, 152, 164)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(156, 179, 78, 164, 17, 99, 115, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(91, 57, 122, 235, 182, 82, 28, 168)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "intToBitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(130, 217, 71, 86, 75, 235, 18, 78)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg(lean_object* v_e_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_6_; lean_object* v_relevantTerms_7_; lean_object* v_relevantHyps_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v___x_6_ = lean_st_ref_take(v_a_4_);
v_relevantTerms_7_ = lean_ctor_get(v___x_6_, 0);
v_relevantHyps_8_ = lean_ctor_get(v___x_6_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v___x_6_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_relevantHyps_8_);
lean_inc(v_relevantTerms_7_);
lean_dec(v___x_6_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v___x_12_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_13_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1));
v___x_14_ = lean_box(0);
v___x_15_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_12_, v___x_13_, v_relevantTerms_7_, v_e_3_, v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_relevantHyps_8_);
v___x_17_ = v_reuseFailAlloc_20_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_st_ref_set(v_a_4_, v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_14_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___boxed(lean_object* v_e_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg(v_e_22_, v_a_23_);
lean_dec(v_a_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm(lean_object* v_e_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_33_; lean_object* v_relevantTerms_34_; lean_object* v_relevantHyps_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_48_; 
v___x_33_ = lean_st_ref_take(v_a_27_);
v_relevantTerms_34_ = lean_ctor_get(v___x_33_, 0);
v_relevantHyps_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_48_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_48_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_relevantHyps_35_);
lean_inc(v_relevantTerms_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_48_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_39_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__0));
v___x_40_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___redArg___closed__1));
v___x_41_ = lean_box(0);
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_39_, v___x_40_, v_relevantTerms_34_, v_e_26_, v___x_41_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_42_);
v___x_44_ = v___x_37_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_relevantHyps_35_);
v___x_44_ = v_reuseFailAlloc_47_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_st_ref_set(v_a_27_, v___x_44_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_41_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm___boxed(lean_object* v_e_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeTerm(v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg(lean_object* v_f_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_relevantTerms_63_; lean_object* v_relevantHyps_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_77_; 
v___x_62_ = lean_st_ref_take(v_a_60_);
v_relevantTerms_63_ = lean_ctor_get(v___x_62_, 0);
v_relevantHyps_64_ = lean_ctor_get(v___x_62_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_77_ == 0)
{
v___x_66_ = v___x_62_;
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_relevantHyps_64_);
lean_inc(v_relevantTerms_63_);
lean_dec(v___x_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_77_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_69_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1));
v___x_70_ = lean_box(0);
v___x_71_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_68_, v___x_69_, v_relevantHyps_64_, v_f_59_, v___x_70_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_71_);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_relevantTerms_63_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_76_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_st_ref_set(v_a_60_, v___x_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_70_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___boxed(lean_object* v_f_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg(v_f_78_, v_a_79_);
lean_dec(v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp(lean_object* v_f_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_relevantTerms_90_; lean_object* v_relevantHyps_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_104_; 
v___x_89_ = lean_st_ref_take(v_a_83_);
v_relevantTerms_90_ = lean_ctor_get(v___x_89_, 0);
v_relevantHyps_91_ = lean_ctor_get(v___x_89_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_104_ == 0)
{
v___x_93_ = v___x_89_;
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_relevantHyps_91_);
lean_inc(v_relevantTerms_90_);
lean_dec(v___x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_104_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__0));
v___x_96_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___redArg___closed__1));
v___x_97_ = lean_box(0);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___x_95_, v___x_96_, v_relevantHyps_91_, v_f_82_, v___x_97_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v___x_98_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_relevantTerms_90_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_103_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_st_ref_set(v_a_83_, v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_97_);
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp___boxed(lean_object* v_f_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_M_addSizeHyp(v_f_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(lean_object* v_e_113_, lean_object* v___y_114_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = l_Lean_Expr_hasMVar(v_e_113_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v_e_113_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v_mctx_119_; lean_object* v___x_120_; lean_object* v_fst_121_; lean_object* v_snd_122_; lean_object* v___x_123_; lean_object* v_cache_124_; lean_object* v_zetaDeltaFVarIds_125_; lean_object* v_postponed_126_; lean_object* v_diag_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_136_; 
v___x_118_ = lean_st_ref_get(v___y_114_);
v_mctx_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc_ref(v_mctx_119_);
lean_dec(v___x_118_);
v___x_120_ = l_Lean_instantiateMVarsCore(v_mctx_119_, v_e_113_);
v_fst_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_fst_121_);
v_snd_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_snd_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = lean_st_ref_take(v___y_114_);
v_cache_124_ = lean_ctor_get(v___x_123_, 1);
v_zetaDeltaFVarIds_125_ = lean_ctor_get(v___x_123_, 2);
v_postponed_126_ = lean_ctor_get(v___x_123_, 3);
v_diag_127_ = lean_ctor_get(v___x_123_, 4);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_123_, 0);
lean_dec(v_unused_137_);
v___x_129_ = v___x_123_;
v_isShared_130_ = v_isSharedCheck_136_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_diag_127_);
lean_inc(v_postponed_126_);
lean_inc(v_zetaDeltaFVarIds_125_);
lean_inc(v_cache_124_);
lean_dec(v___x_123_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_136_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 0, v_snd_122_);
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_snd_122_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_cache_124_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_zetaDeltaFVarIds_125_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_postponed_126_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v_diag_127_);
v___x_132_ = v_reuseFailAlloc_135_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_st_ref_set(v___y_114_, v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v_fst_121_);
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(lean_object* v_e_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_138_, v___y_139_);
lean_dec(v___y_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0(lean_object* v_e_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_142_, v___y_144_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(lean_object* v_e_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0(v_e_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(lean_object* v_mvarId_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_156_, v_x_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_a_172_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_163_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_163_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(lean_object* v_mvarId_180_, lean_object* v_x_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_180_, v_x_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2(lean_object* v_00_u03b1_188_, lean_object* v_mvarId_189_, lean_object* v_x_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_189_, v_x_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(lean_object* v_00_u03b1_197_, lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2(v_00_u03b1_197_, v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_205_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = l_Lean_Level_ofNat(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
v___x_231_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
v___x_234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10));
v___x_235_ = l_Lean_mkConst(v___x_234_, v___x_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1(lean_object* v_as_236_, size_t v_sz_237_, size_t v_i_238_, lean_object* v_b_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_238_, v_sz_237_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_b_239_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; 
lean_dec_ref(v_b_239_);
v_a_247_ = lean_array_uget_borrowed(v_as_236_, v_i_238_);
lean_inc(v_a_247_);
v___x_248_ = l_Lean_FVarId_getType___redArg(v_a_247_, v___y_240_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref(v___x_248_);
v___x_250_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_a_249_, v___y_241_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v___x_250_);
v___x_252_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_251_, v___y_241_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_255_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_252_);
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v___x_261_ = l_Lean_Expr_cleanupAnnotations(v_a_253_);
v___x_262_ = l_Lean_Expr_isApp(v___x_261_);
if (v___x_262_ == 0)
{
lean_dec_ref(v___x_261_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v_arg_263_ = lean_ctor_get(v___x_261_, 1);
lean_inc_ref(v_arg_263_);
v___x_264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_261_);
v___x_265_ = l_Lean_Expr_isApp(v___x_264_);
if (v___x_265_ == 0)
{
lean_dec_ref(v___x_264_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_arg_266_ = lean_ctor_get(v___x_264_, 1);
lean_inc_ref(v_arg_266_);
v___x_267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_264_);
v___x_268_ = l_Lean_Expr_isApp(v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v___x_267_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v_arg_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_arg_269_ = lean_ctor_get(v___x_267_, 1);
lean_inc_ref(v_arg_269_);
v___x_270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_267_);
v___x_271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_272_ = l_Lean_Expr_isConstOf(v___x_270_, v___x_271_);
lean_dec_ref(v___x_270_);
if (v___x_272_ == 0)
{
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_274_ = l_Lean_Expr_isConstOf(v_arg_266_, v___x_273_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; 
lean_dec_ref(v_arg_269_);
v___x_275_ = l_Lean_Expr_isConstOf(v_arg_263_, v___x_273_);
lean_dec_ref(v_arg_263_);
if (v___x_275_ == 0)
{
lean_dec_ref(v_arg_266_);
v_a_255_ = v___x_260_;
goto v___jp_254_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_getNatValue_x3f(v_arg_266_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec_ref(v_arg_266_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_300_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_300_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_300_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_300_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
if (lean_obj_tag(v_a_277_) == 1)
{
lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_295_; 
v_val_281_ = lean_ctor_get(v_a_277_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_277_);
if (v_isSharedCheck_295_ == 0)
{
v___x_283_ = v_a_277_;
v_isShared_284_ = v_isSharedCheck_295_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_dec(v_a_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_295_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
lean_inc(v_a_247_);
v___x_285_ = l_Lean_mkFVar(v_a_247_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v_val_281_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_286_);
v___x_288_ = v___x_283_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_294_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_259_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_290_);
v___x_292_ = v___x_279_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_296_; lean_object* v___x_298_; 
lean_dec(v_a_277_);
v___x_296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8));
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_296_);
v___x_298_ = v___x_279_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_a_301_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_276_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_276_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
else
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_getNatValue_x3f(v_arg_263_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_335_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_335_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_335_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_335_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
if (lean_obj_tag(v_a_310_) == 1)
{
lean_object* v_val_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_330_; 
v_val_314_ = lean_ctor_get(v_a_310_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_316_ = v_a_310_;
v_isShared_317_ = v_isSharedCheck_330_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_val_314_);
lean_dec(v_a_310_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_330_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_318_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13);
lean_inc(v_a_247_);
v___x_319_ = l_Lean_mkFVar(v_a_247_);
v___x_320_ = l_Lean_mkApp4(v___x_318_, v_arg_269_, v_arg_266_, v_arg_263_, v___x_319_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_val_314_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v___x_321_);
v___x_323_ = v___x_316_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_329_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_259_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_325_);
v___x_327_ = v___x_312_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_333_; 
lean_dec(v_a_310_);
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8));
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_331_);
v___x_333_ = v___x_312_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v_arg_269_);
lean_dec_ref(v_arg_266_);
lean_dec_ref(v_arg_263_);
v_a_336_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_309_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_309_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
}
}
v___jp_254_:
{
size_t v___x_256_; size_t v___x_257_; 
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_add(v_i_238_, v___x_256_);
lean_inc_ref(v_a_255_);
v_i_238_ = v___x_257_;
v_b_239_ = v_a_255_;
goto _start;
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_a_344_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_252_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_252_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_250_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_250_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_248_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_248_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(lean_object* v_as_368_, lean_object* v_sz_369_, lean_object* v_i_370_, lean_object* v_b_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
size_t v_sz_boxed_377_; size_t v_i_boxed_378_; lean_object* v_res_379_; 
v_sz_boxed_377_ = lean_unbox_usize(v_sz_369_);
lean_dec(v_sz_369_);
v_i_boxed_378_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_as_368_, v_sz_boxed_377_, v_i_boxed_378_, v_b_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec_ref(v_as_368_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_getPropHyps(v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; size_t v_sz_389_; size_t v___x_390_; lean_object* v___x_391_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref(v___x_385_);
v___x_387_ = lean_box(0);
v___x_388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0));
v_sz_389_ = lean_array_size(v_a_386_);
v___x_390_ = ((size_t)0ULL);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_a_386_, v_sz_389_, v___x_390_, v___x_388_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v_a_386_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_404_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_404_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_fst_396_; 
v_fst_396_ = lean_ctor_get(v_a_392_, 0);
lean_inc(v_fst_396_);
lean_dec(v_a_392_);
if (lean_obj_tag(v_fst_396_) == 0)
{
lean_object* v___x_398_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_387_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_387_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; 
v_val_400_ = lean_ctor_get(v_fst_396_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v_fst_396_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_val_400_);
v___x_402_ = v___x_394_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_val_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_391_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_391_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v_a_413_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_385_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_385_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___lam__0(v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(lean_object* v_goal_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; 
v___f_434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___closed__0));
v___x_435_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_goal_428_, v___f_434_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq___boxed(lean_object* v_goal_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(v_goal_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
lean_inc(v___y_444_);
v___x_450_ = lean_apply_6(v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, lean_box(0));
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(v_x_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(lean_object* v_mvarId_459_, lean_object* v_x_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___f_467_; lean_object* v___x_468_; 
lean_inc(v___y_461_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_467_, 0, v_x_460_);
lean_closure_set(v___f_467_, 1, v___y_461_);
v___x_468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_459_, v___f_467_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
return v___x_468_;
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___boxed(lean_object* v_mvarId_477_, lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_477_, v_x_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14(lean_object* v_00_u03b1_486_, lean_object* v_mvarId_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_487_, v_x_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___boxed(lean_object* v_00_u03b1_496_, lean_object* v_mvarId_497_, lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14(v_00_u03b1_496_, v_mvarId_497_, v_x_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(lean_object* v_a_506_, lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v_key_509_; lean_object* v_value_510_; lean_object* v_tail_511_; uint8_t v___x_512_; 
v_key_509_ = lean_ctor_get(v_x_507_, 0);
v_value_510_ = lean_ctor_get(v_x_507_, 1);
v_tail_511_ = lean_ctor_get(v_x_507_, 2);
v___x_512_ = lean_expr_eqv(v_key_509_, v_a_506_);
if (v___x_512_ == 0)
{
v_x_507_ = v_tail_511_;
goto _start;
}
else
{
lean_object* v___x_514_; 
lean_inc(v_value_510_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_value_510_);
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg___boxed(lean_object* v_a_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_515_, v_x_516_);
lean_dec(v_x_516_);
lean_dec_ref(v_a_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(lean_object* v_m_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_buckets_520_; lean_object* v___x_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v_fold_525_; uint64_t v___x_526_; uint64_t v___x_527_; uint64_t v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_buckets_520_ = lean_ctor_get(v_m_518_, 1);
v___x_521_ = lean_array_get_size(v_buckets_520_);
v___x_522_ = l_Lean_Expr_hash(v_a_519_);
v___x_523_ = 32ULL;
v___x_524_ = lean_uint64_shift_right(v___x_522_, v___x_523_);
v_fold_525_ = lean_uint64_xor(v___x_522_, v___x_524_);
v___x_526_ = 16ULL;
v___x_527_ = lean_uint64_shift_right(v_fold_525_, v___x_526_);
v___x_528_ = lean_uint64_xor(v_fold_525_, v___x_527_);
v___x_529_ = lean_uint64_to_usize(v___x_528_);
v___x_530_ = lean_usize_of_nat(v___x_521_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_sub(v___x_530_, v___x_531_);
v___x_533_ = lean_usize_land(v___x_529_, v___x_532_);
v___x_534_ = lean_array_uget_borrowed(v_buckets_520_, v___x_533_);
v___x_535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_519_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg___boxed(lean_object* v_m_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_536_, v_a_537_);
lean_dec_ref(v_a_537_);
lean_dec_ref(v_m_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0(lean_object* v_fst_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_fst_539_, v___y_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0___boxed(lean_object* v_fst_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0(v_fst_542_, v___y_543_);
lean_dec_ref(v___y_543_);
lean_dec(v_fst_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(lean_object* v_a_545_, lean_object* v_b_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_dec(v_b_546_);
lean_dec_ref(v_a_545_);
return v_x_547_;
}
else
{
lean_object* v_key_548_; lean_object* v_value_549_; lean_object* v_tail_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_562_; 
v_key_548_ = lean_ctor_get(v_x_547_, 0);
v_value_549_ = lean_ctor_get(v_x_547_, 1);
v_tail_550_ = lean_ctor_get(v_x_547_, 2);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_562_ == 0)
{
v___x_552_ = v_x_547_;
v_isShared_553_ = v_isSharedCheck_562_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_tail_550_);
lean_inc(v_value_549_);
lean_inc(v_key_548_);
lean_dec(v_x_547_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_562_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v___x_554_; 
v___x_554_ = lean_expr_eqv(v_key_548_, v_a_545_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_545_, v_b_546_, v_tail_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 2, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_key_548_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_value_549_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
else
{
lean_object* v___x_560_; 
lean_dec(v_value_549_);
lean_dec(v_key_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v_b_546_);
lean_ctor_set(v___x_552_, 0, v_a_545_);
v___x_560_ = v___x_552_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_545_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_b_546_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_tail_550_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
return v_x_563_;
}
else
{
lean_object* v_key_565_; lean_object* v_value_566_; lean_object* v_tail_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_590_; 
v_key_565_ = lean_ctor_get(v_x_564_, 0);
v_value_566_ = lean_ctor_get(v_x_564_, 1);
v_tail_567_ = lean_ctor_get(v_x_564_, 2);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_564_);
if (v_isSharedCheck_590_ == 0)
{
v___x_569_ = v_x_564_;
v_isShared_570_ = v_isSharedCheck_590_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_tail_567_);
lean_inc(v_value_566_);
lean_inc(v_key_565_);
lean_dec(v_x_564_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_590_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; uint64_t v___x_572_; uint64_t v___x_573_; uint64_t v___x_574_; uint64_t v_fold_575_; uint64_t v___x_576_; uint64_t v___x_577_; uint64_t v___x_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_571_ = lean_array_get_size(v_x_563_);
v___x_572_ = l_Lean_Expr_hash(v_key_565_);
v___x_573_ = 32ULL;
v___x_574_ = lean_uint64_shift_right(v___x_572_, v___x_573_);
v_fold_575_ = lean_uint64_xor(v___x_572_, v___x_574_);
v___x_576_ = 16ULL;
v___x_577_ = lean_uint64_shift_right(v_fold_575_, v___x_576_);
v___x_578_ = lean_uint64_xor(v_fold_575_, v___x_577_);
v___x_579_ = lean_uint64_to_usize(v___x_578_);
v___x_580_ = lean_usize_of_nat(v___x_571_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_sub(v___x_580_, v___x_581_);
v___x_583_ = lean_usize_land(v___x_579_, v___x_582_);
v___x_584_ = lean_array_uget_borrowed(v_x_563_, v___x_583_);
lean_inc(v___x_584_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v___x_584_);
v___x_586_ = v___x_569_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_key_565_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_value_566_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v___x_584_);
v___x_586_ = v_reuseFailAlloc_589_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; 
v___x_587_ = lean_array_uset(v_x_563_, v___x_583_, v___x_586_);
v_x_563_ = v___x_587_;
v_x_564_ = v_tail_567_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(lean_object* v_i_591_, lean_object* v_source_592_, lean_object* v_target_593_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_array_get_size(v_source_592_);
v___x_595_ = lean_nat_dec_lt(v_i_591_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec_ref(v_source_592_);
lean_dec(v_i_591_);
return v_target_593_;
}
else
{
lean_object* v_es_596_; lean_object* v___x_597_; lean_object* v_source_598_; lean_object* v_target_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_es_596_ = lean_array_fget(v_source_592_, v_i_591_);
v___x_597_ = lean_box(0);
v_source_598_ = lean_array_fset(v_source_592_, v_i_591_, v___x_597_);
v_target_599_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_target_593_, v_es_596_);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_i_591_, v___x_600_);
lean_dec(v_i_591_);
v_i_591_ = v___x_601_;
v_source_592_ = v_source_598_;
v_target_593_ = v_target_599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(lean_object* v_data_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_nbuckets_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_604_ = lean_array_get_size(v_data_603_);
v___x_605_ = lean_unsigned_to_nat(2u);
v_nbuckets_606_ = lean_nat_mul(v___x_604_, v___x_605_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_box(0);
v___x_609_ = lean_mk_array(v_nbuckets_606_, v___x_608_);
v___x_610_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v___x_607_, v_data_603_, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(lean_object* v_a_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
else
{
lean_object* v_key_614_; lean_object* v_tail_615_; uint8_t v___x_616_; 
v_key_614_ = lean_ctor_get(v_x_612_, 0);
v_tail_615_ = lean_ctor_get(v_x_612_, 2);
v___x_616_ = lean_expr_eqv(v_key_614_, v_a_611_);
if (v___x_616_ == 0)
{
v_x_612_ = v_tail_615_;
goto _start;
}
else
{
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg___boxed(lean_object* v_a_618_, lean_object* v_x_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_618_, v_x_619_);
lean_dec(v_x_619_);
lean_dec_ref(v_a_618_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(lean_object* v_m_622_, lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
lean_object* v_size_625_; lean_object* v_buckets_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_669_; 
v_size_625_ = lean_ctor_get(v_m_622_, 0);
v_buckets_626_ = lean_ctor_get(v_m_622_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_m_622_);
if (v_isSharedCheck_669_ == 0)
{
v___x_628_ = v_m_622_;
v_isShared_629_ = v_isSharedCheck_669_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_buckets_626_);
lean_inc(v_size_625_);
lean_dec(v_m_622_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_669_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; uint64_t v___x_631_; uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v_fold_634_; uint64_t v___x_635_; uint64_t v___x_636_; uint64_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; size_t v___x_642_; lean_object* v_bkt_643_; uint8_t v___x_644_; 
v___x_630_ = lean_array_get_size(v_buckets_626_);
v___x_631_ = l_Lean_Expr_hash(v_a_623_);
v___x_632_ = 32ULL;
v___x_633_ = lean_uint64_shift_right(v___x_631_, v___x_632_);
v_fold_634_ = lean_uint64_xor(v___x_631_, v___x_633_);
v___x_635_ = 16ULL;
v___x_636_ = lean_uint64_shift_right(v_fold_634_, v___x_635_);
v___x_637_ = lean_uint64_xor(v_fold_634_, v___x_636_);
v___x_638_ = lean_uint64_to_usize(v___x_637_);
v___x_639_ = lean_usize_of_nat(v___x_630_);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_sub(v___x_639_, v___x_640_);
v___x_642_ = lean_usize_land(v___x_638_, v___x_641_);
v_bkt_643_ = lean_array_uget_borrowed(v_buckets_626_, v___x_642_);
v___x_644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_623_, v_bkt_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v_size_x27_646_; lean_object* v___x_647_; lean_object* v_buckets_x27_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v_size_x27_646_ = lean_nat_add(v_size_625_, v___x_645_);
lean_dec(v_size_625_);
lean_inc(v_bkt_643_);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v_a_623_);
lean_ctor_set(v___x_647_, 1, v_b_624_);
lean_ctor_set(v___x_647_, 2, v_bkt_643_);
v_buckets_x27_648_ = lean_array_uset(v_buckets_626_, v___x_642_, v___x_647_);
v___x_649_ = lean_unsigned_to_nat(4u);
v___x_650_ = lean_nat_mul(v_size_x27_646_, v___x_649_);
v___x_651_ = lean_unsigned_to_nat(3u);
v___x_652_ = lean_nat_div(v___x_650_, v___x_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_array_get_size(v_buckets_x27_648_);
v___x_654_ = lean_nat_dec_le(v___x_652_, v___x_653_);
lean_dec(v___x_652_);
if (v___x_654_ == 0)
{
lean_object* v_val_655_; lean_object* v___x_657_; 
v_val_655_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_648_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_val_655_);
lean_ctor_set(v___x_628_, 0, v_size_x27_646_);
v___x_657_ = v___x_628_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_size_x27_646_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_val_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
lean_object* v___x_660_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v_buckets_x27_648_);
lean_ctor_set(v___x_628_, 0, v_size_x27_646_);
v___x_660_ = v___x_628_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_size_x27_646_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_buckets_x27_648_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v___x_662_; lean_object* v_buckets_x27_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_inc(v_bkt_643_);
v___x_662_ = lean_box(0);
v_buckets_x27_663_ = lean_array_uset(v_buckets_626_, v___x_642_, v___x_662_);
v___x_664_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_623_, v_b_624_, v_bkt_643_);
v___x_665_ = lean_array_uset(v_buckets_x27_663_, v___x_642_, v___x_664_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 1, v___x_665_);
v___x_667_ = v___x_628_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_size_625_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(lean_object* v_as_670_, size_t v_sz_671_, size_t v_i_672_, lean_object* v_b_673_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_lt(v_i_672_, v_sz_671_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_b_673_);
return v___x_676_;
}
else
{
lean_object* v_snd_677_; lean_object* v_fst_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_711_; 
v_snd_677_ = lean_ctor_get(v_b_673_, 1);
v_fst_678_ = lean_ctor_get(v_b_673_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v_b_673_);
if (v_isSharedCheck_711_ == 0)
{
v___x_680_ = v_b_673_;
v_isShared_681_ = v_isSharedCheck_711_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_677_);
lean_inc(v_fst_678_);
lean_dec(v_b_673_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_711_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_array_682_; lean_object* v_start_683_; lean_object* v_stop_684_; uint8_t v___x_685_; 
v_array_682_ = lean_ctor_get(v_snd_677_, 0);
v_start_683_ = lean_ctor_get(v_snd_677_, 1);
v_stop_684_ = lean_ctor_get(v_snd_677_, 2);
v___x_685_ = lean_nat_dec_lt(v_start_683_, v_stop_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_687_; 
if (v_isShared_681_ == 0)
{
v___x_687_ = v___x_680_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_fst_678_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_snd_677_);
v___x_687_ = v_reuseFailAlloc_689_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
else
{
lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_707_; 
lean_inc(v_stop_684_);
lean_inc(v_start_683_);
lean_inc_ref(v_array_682_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_snd_677_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; lean_object* v_unused_710_; 
v_unused_708_ = lean_ctor_get(v_snd_677_, 2);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_snd_677_, 1);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_snd_677_, 0);
lean_dec(v_unused_710_);
v___x_691_ = v_snd_677_;
v_isShared_692_ = v_isSharedCheck_707_;
goto v_resetjp_690_;
}
else
{
lean_dec(v_snd_677_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_707_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v_a_693_ = lean_array_uget_borrowed(v_as_670_, v_i_672_);
v___x_694_ = lean_array_fget(v_array_682_, v_start_683_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_add(v_start_683_, v___x_695_);
lean_dec(v_start_683_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_696_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_array_682_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_stop_684_);
v___x_698_ = v_reuseFailAlloc_706_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
lean_inc(v_a_693_);
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_fst_678_, v_a_693_, v___x_694_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_698_);
lean_ctor_set(v___x_680_, 0, v___x_699_);
v___x_701_ = v___x_680_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_698_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
size_t v___x_702_; size_t v___x_703_; 
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_add(v_i_672_, v___x_702_);
v_i_672_ = v___x_703_;
v_b_673_ = v___x_701_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg___boxed(lean_object* v_as_712_, lean_object* v_sz_713_, lean_object* v_i_714_, lean_object* v_b_715_, lean_object* v___y_716_){
_start:
{
size_t v_sz_boxed_717_; size_t v_i_boxed_718_; lean_object* v_res_719_; 
v_sz_boxed_717_ = lean_unbox_usize(v_sz_713_);
lean_dec(v_sz_713_);
v_i_boxed_718_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_712_, v_sz_boxed_717_, v_i_boxed_718_, v_b_715_);
lean_dec_ref(v_as_712_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1(lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v_z_722_, lean_object* v___y_723_, size_t v___x_724_, lean_object* v_a_725_, uint8_t v___x_726_, lean_object* v_args_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; size_t v_sz_750_; lean_object* v___x_751_; 
v___x_734_ = lean_array_get_size(v_args_727_);
v___x_735_ = lean_nat_add(v___x_734_, v___x_720_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = lean_unsigned_to_nat(4u);
v___x_738_ = lean_nat_mul(v___x_735_, v___x_737_);
lean_dec(v___x_735_);
v___x_739_ = lean_unsigned_to_nat(3u);
v___x_740_ = lean_nat_div(v___x_738_, v___x_739_);
lean_dec(v___x_738_);
v___x_741_ = l_Nat_nextPowerOfTwo(v___x_740_);
lean_dec(v___x_740_);
v___x_742_ = lean_box(0);
v___x_743_ = lean_mk_array(v___x_741_, v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_736_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_746_ = l_Lean_mkConst(v___x_745_, v___x_721_);
v___x_747_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v___x_744_, v___x_746_, v_z_722_);
lean_inc_ref(v_args_727_);
v___x_748_ = l_Array_toSubarray___redArg(v_args_727_, v___x_736_, v___x_734_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v_sz_750_ = lean_array_size(v___y_723_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v___y_723_, v_sz_750_, v___x_724_, v___x_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v_fst_753_; lean_object* v___f_754_; lean_object* v___x_755_; uint8_t v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
v_fst_753_ = lean_ctor_get(v_a_752_, 0);
lean_inc(v_fst_753_);
lean_dec(v_a_752_);
v___f_754_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__0___boxed), 2, 1);
lean_closure_set(v___f_754_, 0, v_fst_753_);
v___x_755_ = lean_replace_expr(v___f_754_, v_a_725_);
lean_dec_ref(v___f_754_);
v___x_756_ = 0;
v___x_757_ = 1;
v___x_758_ = l_Lean_Meta_mkForallFVars(v_args_727_, v___x_755_, v___x_756_, v___x_726_, v___x_726_, v___x_757_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec_ref(v_args_727_);
return v___x_758_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_args_727_);
v_a_759_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_751_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_751_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1___boxed(lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v_z_769_, lean_object* v___y_770_, lean_object* v___x_771_, lean_object* v_a_772_, lean_object* v___x_773_, lean_object* v_args_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
size_t v___x_21243__boxed_781_; uint8_t v___x_21245__boxed_782_; lean_object* v_res_783_; 
v___x_21243__boxed_781_ = lean_unbox_usize(v___x_771_);
lean_dec(v___x_771_);
v___x_21245__boxed_782_ = lean_unbox(v___x_773_);
v_res_783_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1(v___x_767_, v___x_768_, v_z_769_, v___y_770_, v___x_21243__boxed_781_, v_a_772_, v___x_21245__boxed_782_, v_args_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v_a_772_);
lean_dec_ref(v___y_770_);
lean_dec(v___x_767_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(lean_object* v___x_787_, size_t v_sz_788_, size_t v_i_789_, lean_object* v_bs_790_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_usize_dec_lt(v_i_789_, v_sz_788_);
if (v___x_791_ == 0)
{
lean_dec_ref(v___x_787_);
return v_bs_790_;
}
else
{
lean_object* v___x_792_; lean_object* v_bs_x27_793_; lean_object* v___x_794_; lean_object* v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v_bs_x27_793_ = lean_array_uset(v_bs_790_, v_i_789_, v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1));
lean_inc_ref(v___x_787_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___x_787_);
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_add(v_i_789_, v___x_796_);
v___x_798_ = lean_array_uset(v_bs_x27_793_, v_i_789_, v___x_795_);
v_i_789_ = v___x_797_;
v_bs_790_ = v___x_798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4___boxed(lean_object* v___x_800_, lean_object* v_sz_801_, lean_object* v_i_802_, lean_object* v_bs_803_){
_start:
{
size_t v_sz_boxed_804_; size_t v_i_boxed_805_; lean_object* v_res_806_; 
v_sz_boxed_804_ = lean_unbox_usize(v_sz_801_);
lean_dec(v_sz_801_);
v_i_boxed_805_ = lean_unbox_usize(v_i_802_);
lean_dec(v_i_802_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_800_, v_sz_boxed_804_, v_i_boxed_805_, v_bs_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(lean_object* v_snd_807_, lean_object* v_x_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v_snd_807_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed(lean_object* v_snd_816_, lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(v_snd_816_, v_x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v_x_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(size_t v_sz_825_, size_t v_i_826_, lean_object* v_bs_827_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_828_ == 0)
{
return v_bs_827_;
}
else
{
lean_object* v_v_829_; lean_object* v_fst_830_; lean_object* v_snd_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_845_; 
v_v_829_ = lean_array_uget(v_bs_827_, v_i_826_);
v_fst_830_ = lean_ctor_get(v_v_829_, 0);
v_snd_831_ = lean_ctor_get(v_v_829_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_v_829_);
if (v_isSharedCheck_845_ == 0)
{
v___x_833_ = v_v_829_;
v_isShared_834_ = v_isSharedCheck_845_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snd_831_);
lean_inc(v_fst_830_);
lean_dec(v_v_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_845_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v_bs_x27_836_; lean_object* v___f_837_; lean_object* v___x_839_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v_bs_x27_836_ = lean_array_uset(v_bs_827_, v_i_826_, v___x_835_);
v___f_837_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed), 8, 1);
lean_closure_set(v___f_837_, 0, v_snd_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___f_837_);
v___x_839_ = v___x_833_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_fst_830_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___f_837_);
v___x_839_ = v_reuseFailAlloc_844_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_i_826_, v___x_840_);
v___x_842_ = lean_array_uset(v_bs_x27_836_, v_i_826_, v___x_839_);
v_i_826_ = v___x_841_;
v_bs_827_ = v___x_842_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___boxed(lean_object* v_sz_846_, lean_object* v_i_847_, lean_object* v_bs_848_){
_start:
{
size_t v_sz_boxed_849_; size_t v_i_boxed_850_; lean_object* v_res_851_; 
v_sz_boxed_849_ = lean_unbox_usize(v_sz_846_);
lean_dec(v_sz_846_);
v_i_boxed_850_ = lean_unbox_usize(v_i_847_);
lean_dec(v_i_847_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_boxed_849_, v_i_boxed_850_, v_bs_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0(lean_object* v___x_852_, lean_object* v_a_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_20831__overap_861_; lean_object* v___x_862_; 
v___x_860_ = l_Lean_instInhabitedExpr;
v___x_20831__overap_861_ = l_instInhabitedOfMonad___redArg(v___x_852_, v___x_860_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
v___x_862_ = lean_apply_6(v___x_20831__overap_861_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0___boxed(lean_object* v___x_863_, lean_object* v_a_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0(v___x_863_, v_a_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v_a_864_);
return v_res_871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_instMonadEIO(lean_box(0));
return v___x_872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__0);
v___x_874_ = l_StateRefT_x27_instMonad___redArg(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0___boxed(lean_object* v_acc_879_, lean_object* v_declInfos_880_, lean_object* v_k_881_, lean_object* v_kind_882_, lean_object* v_inst_883_, lean_object* v___y_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v_kind_boxed_891_; lean_object* v_res_892_; 
v_kind_boxed_891_ = lean_unbox(v_kind_882_);
v_res_892_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0(v_acc_879_, v_declInfos_880_, v_k_881_, v_kind_boxed_891_, v_inst_883_, v___y_884_, v_b_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_884_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(lean_object* v_acc_893_, lean_object* v_declInfos_894_, lean_object* v_k_895_, uint8_t v_kind_896_, lean_object* v_inst_897_, lean_object* v_name_898_, uint8_t v_bi_899_, lean_object* v_type_900_, uint8_t v_kind_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; 
v___x_908_ = lean_box(v_kind_896_);
lean_inc(v___y_902_);
v___f_909_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_909_, 0, v_acc_893_);
lean_closure_set(v___f_909_, 1, v_declInfos_894_);
lean_closure_set(v___f_909_, 2, v_k_895_);
lean_closure_set(v___f_909_, 3, v___x_908_);
lean_closure_set(v___f_909_, 4, v_inst_897_);
lean_closure_set(v___f_909_, 5, v___y_902_);
v___x_910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_898_, v_bi_899_, v_type_900_, v___f_909_, v_kind_901_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_910_) == 0)
{
return v___x_910_;
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(lean_object* v_declInfos_919_, lean_object* v_k_920_, uint8_t v_kind_921_, lean_object* v_inst_922_, lean_object* v_acc_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_toApplicative_931_; lean_object* v_toFunctor_932_; lean_object* v_toSeq_933_; lean_object* v_toSeqLeft_934_; lean_object* v_toSeqRight_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___f_938_; lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___f_941_; lean_object* v___f_942_; lean_object* v___f_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_toApplicative_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_1003_; 
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__1);
v_toApplicative_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_toApplicative_931_);
v_toFunctor_932_ = lean_ctor_get(v_toApplicative_931_, 0);
lean_inc_ref(v_toFunctor_932_);
v_toSeq_933_ = lean_ctor_get(v_toApplicative_931_, 2);
lean_inc(v_toSeq_933_);
v_toSeqLeft_934_ = lean_ctor_get(v_toApplicative_931_, 3);
lean_inc(v_toSeqLeft_934_);
v_toSeqRight_935_ = lean_ctor_get(v_toApplicative_931_, 4);
lean_inc(v_toSeqRight_935_);
lean_dec_ref(v_toApplicative_931_);
v___f_936_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__2));
v___f_937_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__3));
lean_inc_ref(v_toFunctor_932_);
v___f_938_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_938_, 0, v_toFunctor_932_);
v___f_939_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_939_, 0, v_toFunctor_932_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___f_938_);
lean_ctor_set(v___x_940_, 1, v___f_939_);
v___f_941_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_941_, 0, v_toSeqRight_935_);
v___f_942_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_942_, 0, v_toSeqLeft_934_);
v___f_943_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_943_, 0, v_toSeq_933_);
v___x_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_944_, 0, v___x_940_);
lean_ctor_set(v___x_944_, 1, v___f_936_);
lean_ctor_set(v___x_944_, 2, v___f_943_);
lean_ctor_set(v___x_944_, 3, v___f_942_);
lean_ctor_set(v___x_944_, 4, v___f_941_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___f_937_);
v___x_946_ = l_StateRefT_x27_instMonad___redArg(v___x_945_);
v_toApplicative_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v___x_946_, 1);
lean_dec(v_unused_1004_);
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_1003_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_toApplicative_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_1003_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_toFunctor_951_; lean_object* v_toSeq_952_; lean_object* v_toSeqLeft_953_; lean_object* v_toSeqRight_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1001_; 
v_toFunctor_951_ = lean_ctor_get(v_toApplicative_947_, 0);
v_toSeq_952_ = lean_ctor_get(v_toApplicative_947_, 2);
v_toSeqLeft_953_ = lean_ctor_get(v_toApplicative_947_, 3);
v_toSeqRight_954_ = lean_ctor_get(v_toApplicative_947_, 4);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_toApplicative_947_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; 
v_unused_1002_ = lean_ctor_get(v_toApplicative_947_, 1);
lean_dec(v_unused_1002_);
v___x_956_ = v_toApplicative_947_;
v_isShared_957_ = v_isSharedCheck_1001_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_toSeqRight_954_);
lean_inc(v_toSeqLeft_953_);
lean_inc(v_toSeq_952_);
lean_inc(v_toFunctor_951_);
lean_dec(v_toApplicative_947_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1001_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___f_958_; lean_object* v___f_959_; lean_object* v___f_960_; lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___f_963_; lean_object* v___f_964_; lean_object* v___f_965_; lean_object* v___x_967_; 
v___f_958_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__4));
v___f_959_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___closed__5));
lean_inc_ref(v_toFunctor_951_);
v___f_960_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_960_, 0, v_toFunctor_951_);
v___f_961_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_961_, 0, v_toFunctor_951_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___f_960_);
lean_ctor_set(v___x_962_, 1, v___f_961_);
v___f_963_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_963_, 0, v_toSeqRight_954_);
v___f_964_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_964_, 0, v_toSeqLeft_953_);
v___f_965_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_965_, 0, v_toSeq_952_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 4, v___f_963_);
lean_ctor_set(v___x_956_, 3, v___f_964_);
lean_ctor_set(v___x_956_, 2, v___f_965_);
lean_ctor_set(v___x_956_, 1, v___f_958_);
lean_ctor_set(v___x_956_, 0, v___x_962_);
v___x_967_ = v___x_956_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___f_958_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v___f_965_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v___f_964_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v___f_963_);
v___x_967_ = v_reuseFailAlloc_1000_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___f_959_);
lean_ctor_set(v___x_949_, 0, v___x_967_);
v___x_969_ = v___x_949_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___f_959_);
v___x_969_ = v_reuseFailAlloc_999_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_970_ = l_StateRefT_x27_instMonad___redArg(v___x_969_);
v___x_971_ = lean_array_get_size(v_acc_923_);
v___x_972_ = lean_array_get_size(v_declInfos_919_);
v___x_973_ = lean_nat_dec_lt(v___x_971_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec_ref(v___x_970_);
lean_dec(v_inst_922_);
lean_dec_ref(v_declInfos_919_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
v___x_974_ = lean_apply_7(v_k_920_, v_acc_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
return v___x_974_;
}
else
{
lean_object* v___f_975_; lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_snd_983_; lean_object* v_fst_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_987_; 
v___f_975_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_975_, 0, v___x_970_);
v___x_976_ = lean_box(0);
v___x_977_ = 0;
v___f_978_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_978_, 0, v___f_975_);
v___x_979_ = lean_box(v___x_977_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___f_978_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_976_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_array_get_borrowed(v___x_981_, v_declInfos_919_, v___x_971_);
lean_dec_ref(v___x_981_);
v_snd_983_ = lean_ctor_get(v___x_982_, 1);
v_fst_984_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_984_);
v_fst_985_ = lean_ctor_get(v_snd_983_, 0);
v_snd_986_ = lean_ctor_get(v_snd_983_, 1);
lean_inc(v_snd_986_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
lean_inc_ref(v_acc_923_);
v___x_987_ = lean_apply_7(v_snd_986_, v_acc_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; uint8_t v___x_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v___x_989_ = lean_unbox(v_fst_985_);
v___x_990_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(v_acc_923_, v_declInfos_919_, v_k_920_, v_kind_921_, v_inst_922_, v_fst_984_, v___x_989_, v_a_988_, v_kind_921_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_990_;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v_fst_984_);
lean_dec_ref(v_acc_923_);
lean_dec(v_inst_922_);
lean_dec_ref(v_k_920_);
lean_dec_ref(v_declInfos_919_);
v_a_991_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_987_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___lam__0(lean_object* v_acc_1005_, lean_object* v_declInfos_1006_, lean_object* v_k_1007_, uint8_t v_kind_1008_, lean_object* v_inst_1009_, lean_object* v___y_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_array_push(v_acc_1005_, v_b_1011_);
v___x_1018_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(v_declInfos_1006_, v_k_1007_, v_kind_1008_, v_inst_1009_, v___x_1017_, v___y_1010_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg___boxed(lean_object* v_acc_1019_, lean_object* v_declInfos_1020_, lean_object* v_k_1021_, lean_object* v_kind_1022_, lean_object* v_inst_1023_, lean_object* v_name_1024_, lean_object* v_bi_1025_, lean_object* v_type_1026_, lean_object* v_kind_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v_kind_boxed_1034_; uint8_t v_bi_boxed_1035_; uint8_t v_kind_boxed_1036_; lean_object* v_res_1037_; 
v_kind_boxed_1034_ = lean_unbox(v_kind_1022_);
v_bi_boxed_1035_ = lean_unbox(v_bi_1025_);
v_kind_boxed_1036_ = lean_unbox(v_kind_1027_);
v_res_1037_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(v_acc_1019_, v_declInfos_1020_, v_k_1021_, v_kind_boxed_1034_, v_inst_1023_, v_name_1024_, v_bi_boxed_1035_, v_type_1026_, v_kind_boxed_1036_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg___boxed(lean_object* v_declInfos_1038_, lean_object* v_k_1039_, lean_object* v_kind_1040_, lean_object* v_inst_1041_, lean_object* v_acc_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
uint8_t v_kind_boxed_1049_; lean_object* v_res_1050_; 
v_kind_boxed_1049_ = lean_unbox(v_kind_1040_);
v_res_1050_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(v_declInfos_1038_, v_k_1039_, v_kind_boxed_1049_, v_inst_1041_, v_acc_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(lean_object* v_inst_1053_, lean_object* v_declInfos_1054_, lean_object* v_k_1055_, uint8_t v_kind_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___closed__0));
v___x_1064_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(v_declInfos_1054_, v_k_1055_, v_kind_1056_, v_inst_1053_, v___x_1063_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg___boxed(lean_object* v_inst_1065_, lean_object* v_declInfos_1066_, lean_object* v_k_1067_, lean_object* v_kind_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v_kind_boxed_1075_; lean_object* v_res_1076_; 
v_kind_boxed_1075_ = lean_unbox(v_kind_1068_);
v_res_1076_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(v_inst_1065_, v_declInfos_1066_, v_k_1067_, v_kind_boxed_1075_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(size_t v_sz_1077_, size_t v_i_1078_, lean_object* v_bs_1079_){
_start:
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_usize_dec_lt(v_i_1078_, v_sz_1077_);
if (v___x_1080_ == 0)
{
return v_bs_1079_;
}
else
{
lean_object* v_v_1081_; lean_object* v_fst_1082_; lean_object* v_snd_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1099_; 
v_v_1081_ = lean_array_uget(v_bs_1079_, v_i_1078_);
v_fst_1082_ = lean_ctor_get(v_v_1081_, 0);
v_snd_1083_ = lean_ctor_get(v_v_1081_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_v_1081_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1085_ = v_v_1081_;
v_isShared_1086_ = v_isSharedCheck_1099_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_snd_1083_);
lean_inc(v_fst_1082_);
lean_dec(v_v_1081_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1099_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v_bs_x27_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1087_ = lean_unsigned_to_nat(0u);
v_bs_x27_1088_ = lean_array_uset(v_bs_1079_, v_i_1078_, v___x_1087_);
v___x_1089_ = 0;
v___x_1090_ = lean_box(v___x_1089_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1090_);
v___x_1092_ = v___x_1085_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_snd_1083_);
v___x_1092_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_fst_1082_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = ((size_t)1ULL);
v___x_1095_ = lean_usize_add(v_i_1078_, v___x_1094_);
v___x_1096_ = lean_array_uset(v_bs_x27_1088_, v_i_1078_, v___x_1093_);
v_i_1078_ = v___x_1095_;
v_bs_1079_ = v___x_1096_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(lean_object* v_sz_1100_, lean_object* v_i_1101_, lean_object* v_bs_1102_){
_start:
{
size_t v_sz_boxed_1103_; size_t v_i_boxed_1104_; lean_object* v_res_1105_; 
v_sz_boxed_1103_ = lean_unbox_usize(v_sz_1100_);
lean_dec(v_sz_1100_);
v_i_boxed_1104_ = lean_unbox_usize(v_i_1101_);
lean_dec(v_i_1101_);
v_res_1105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_boxed_1103_, v_i_boxed_1104_, v_bs_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(lean_object* v_inst_1106_, lean_object* v_declInfos_1107_, lean_object* v_k_1108_, uint8_t v_kind_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
size_t v_sz_1116_; size_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_sz_1116_ = lean_array_size(v_declInfos_1107_);
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_1116_, v___x_1117_, v_declInfos_1107_);
v___x_1119_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(v_inst_1106_, v___x_1118_, v_k_1108_, v_kind_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg___boxed(lean_object* v_inst_1120_, lean_object* v_declInfos_1121_, lean_object* v_k_1122_, lean_object* v_kind_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v_kind_boxed_1130_; lean_object* v_res_1131_; 
v_kind_boxed_1130_ = lean_unbox(v_kind_1123_);
v_res_1131_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(v_inst_1120_, v_declInfos_1121_, v_k_1122_, v_kind_boxed_1130_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(lean_object* v_inst_1132_, lean_object* v_declInfos_1133_, lean_object* v_k_1134_, uint8_t v_kind_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
size_t v_sz_1142_; size_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_sz_1142_ = lean_array_size(v_declInfos_1133_);
v___x_1143_ = ((size_t)0ULL);
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_1142_, v___x_1143_, v_declInfos_1133_);
v___x_1145_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(v_inst_1132_, v___x_1144_, v_k_1134_, v_kind_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg___boxed(lean_object* v_inst_1146_, lean_object* v_declInfos_1147_, lean_object* v_k_1148_, lean_object* v_kind_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v_kind_boxed_1156_; lean_object* v_res_1157_; 
v_kind_boxed_1156_ = lean_unbox(v_kind_1149_);
v_res_1157_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(v_inst_1146_, v_declInfos_1147_, v_k_1148_, v_kind_boxed_1156_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(lean_object* v___x_1161_, lean_object* v_z_1162_, lean_object* v___y_1163_, size_t v___x_1164_, lean_object* v___x_1165_, lean_object* v___f_1166_, lean_object* v___x_1167_, uint8_t v___x_1168_, lean_object* v_other_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; size_t v_sz_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1));
v___x_1177_ = l_Lean_mkConst(v___x_1176_, v___x_1161_);
lean_inc_ref(v_z_1162_);
v___x_1178_ = l_Lean_Expr_app___override(v___x_1177_, v_z_1162_);
v_sz_1179_ = lean_array_size(v___y_1163_);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_1178_, v_sz_1179_, v___x_1164_, v___y_1163_);
v___x_1181_ = 0;
v___x_1182_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(v___x_1165_, v___x_1180_, v___f_1166_, v___x_1181_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1182_);
lean_inc_ref(v_z_1162_);
v___x_1184_ = l_Lean_Expr_replaceFVar(v_a_1183_, v_z_1162_, v___x_1167_);
v___x_1185_ = lean_unsigned_to_nat(2u);
v___x_1186_ = lean_mk_empty_array_with_capacity(v___x_1185_);
v___x_1187_ = lean_array_push(v___x_1186_, v_z_1162_);
v___x_1188_ = lean_array_push(v___x_1187_, v_other_1169_);
v___x_1189_ = 0;
v___x_1190_ = 1;
v___x_1191_ = l_Lean_Meta_mkLambdaFVars(v___x_1188_, v_a_1183_, v___x_1189_, v___x_1168_, v___x_1189_, v___x_1168_, v___x_1190_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec_ref(v___x_1188_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_a_1192_);
lean_ctor_set(v___x_1196_, 1, v___x_1184_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v___x_1184_);
v_a_1201_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1191_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1191_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_other_1169_);
lean_dec_ref(v_z_1162_);
v_a_1209_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1182_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1182_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(lean_object* v___x_1217_, lean_object* v_z_1218_, lean_object* v___y_1219_, lean_object* v___x_1220_, lean_object* v___x_1221_, lean_object* v___f_1222_, lean_object* v___x_1223_, lean_object* v___x_1224_, lean_object* v_other_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
size_t v___x_21822__boxed_1232_; uint8_t v___x_21826__boxed_1233_; lean_object* v_res_1234_; 
v___x_21822__boxed_1232_ = lean_unbox_usize(v___x_1220_);
lean_dec(v___x_1220_);
v___x_21826__boxed_1233_ = lean_unbox(v___x_1224_);
v_res_1234_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2(v___x_1217_, v_z_1218_, v___y_1219_, v___x_21822__boxed_1232_, v___x_1221_, v___f_1222_, v___x_1223_, v___x_21826__boxed_1233_, v_other_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___x_1223_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(lean_object* v_k_1235_, lean_object* v___y_1236_, lean_object* v_b_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1243_; 
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1236_);
v___x_1243_ = lean_apply_7(v_k_1235_, v_b_1237_, v___y_1236_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, lean_box(0));
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(lean_object* v_k_1244_, lean_object* v___y_1245_, lean_object* v_b_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(v_k_1244_, v___y_1245_, v_b_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1245_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(lean_object* v_name_1253_, uint8_t v_bi_1254_, lean_object* v_type_1255_, lean_object* v_k_1256_, uint8_t v_kind_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___f_1264_; lean_object* v___x_1265_; 
lean_inc(v___y_1258_);
v___f_1264_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1264_, 0, v_k_1256_);
lean_closure_set(v___f_1264_, 1, v___y_1258_);
v___x_1265_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1253_, v_bi_1254_, v_type_1255_, v___f_1264_, v_kind_1257_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1265_) == 0)
{
return v___x_1265_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___boxed(lean_object* v_name_1274_, lean_object* v_bi_1275_, lean_object* v_type_1276_, lean_object* v_k_1277_, lean_object* v_kind_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v_bi_boxed_1285_; uint8_t v_kind_boxed_1286_; lean_object* v_res_1287_; 
v_bi_boxed_1285_ = lean_unbox(v_bi_1275_);
v_kind_boxed_1286_ = lean_unbox(v_kind_1278_);
v_res_1287_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_1274_, v_bi_boxed_1285_, v_type_1276_, v_k_1277_, v_kind_boxed_1286_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(lean_object* v_name_1288_, lean_object* v_type_1289_, lean_object* v_k_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
uint8_t v___x_1297_; uint8_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = 0;
v___x_1298_ = 0;
v___x_1299_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_1288_, v___x_1297_, v_type_1289_, v_k_1290_, v___x_1298_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(lean_object* v_name_1300_, lean_object* v_type_1301_, lean_object* v_k_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_1300_, v_type_1301_, v_k_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(lean_object* v___x_1313_, lean_object* v___y_1314_, size_t v___x_1315_, lean_object* v_a_1316_, uint8_t v___x_1317_, lean_object* v_fst_1318_, lean_object* v___x_1319_, lean_object* v___x_1320_, lean_object* v_z_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___f_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2));
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_box_usize(v___x_1315_);
v___x_1331_ = lean_box(v___x_1317_);
lean_inc_ref(v___y_1314_);
lean_inc_ref(v_z_1321_);
lean_inc(v___x_1313_);
v___f_1332_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1332_, 0, v___x_1329_);
lean_closure_set(v___f_1332_, 1, v___x_1313_);
lean_closure_set(v___f_1332_, 2, v_z_1321_);
lean_closure_set(v___f_1332_, 3, v___y_1314_);
lean_closure_set(v___f_1332_, 4, v___x_1330_);
lean_closure_set(v___f_1332_, 5, v_a_1316_);
lean_closure_set(v___f_1332_, 6, v___x_1331_);
v___x_1333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
lean_inc(v___x_1313_);
v___x_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1313_);
v___x_1335_ = l_Lean_mkConst(v___x_1328_, v___x_1334_);
v___x_1336_ = l_Lean_mkNatLit(v_fst_1318_);
v___x_1337_ = lean_box_usize(v___x_1315_);
v___x_1338_ = lean_box(v___x_1317_);
lean_inc_ref(v___x_1336_);
lean_inc_ref(v_z_1321_);
v___f_1339_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__2___boxed), 15, 8);
lean_closure_set(v___f_1339_, 0, v___x_1313_);
lean_closure_set(v___f_1339_, 1, v_z_1321_);
lean_closure_set(v___f_1339_, 2, v___y_1314_);
lean_closure_set(v___f_1339_, 3, v___x_1337_);
lean_closure_set(v___f_1339_, 4, v___x_1319_);
lean_closure_set(v___f_1339_, 5, v___f_1332_);
lean_closure_set(v___f_1339_, 6, v___x_1336_);
lean_closure_set(v___f_1339_, 7, v___x_1338_);
v___x_1340_ = l_Lean_mkApp3(v___x_1335_, v___x_1320_, v___x_1336_, v_z_1321_);
v___x_1341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1));
v___x_1342_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_1341_, v___x_1340_, v___f_1339_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(lean_object* v___x_1343_, lean_object* v___y_1344_, lean_object* v___x_1345_, lean_object* v_a_1346_, lean_object* v___x_1347_, lean_object* v_fst_1348_, lean_object* v___x_1349_, lean_object* v___x_1350_, lean_object* v_z_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
size_t v___x_22038__boxed_1358_; uint8_t v___x_22040__boxed_1359_; lean_object* v_res_1360_; 
v___x_22038__boxed_1358_ = lean_unbox_usize(v___x_1345_);
lean_dec(v___x_1345_);
v___x_22040__boxed_1359_ = lean_unbox(v___x_1347_);
v_res_1360_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3(v___x_1343_, v___y_1344_, v___x_22038__boxed_1358_, v_a_1346_, v___x_22040__boxed_1359_, v_fst_1348_, v___x_1349_, v___x_1350_, v_z_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__10(lean_object* v_x_1361_, lean_object* v_x_1362_){
_start:
{
if (lean_obj_tag(v_x_1362_) == 0)
{
return v_x_1361_;
}
else
{
lean_object* v_key_1363_; lean_object* v_tail_1364_; lean_object* v___x_1365_; 
v_key_1363_ = lean_ctor_get(v_x_1362_, 0);
lean_inc(v_key_1363_);
v_tail_1364_ = lean_ctor_get(v_x_1362_, 2);
lean_inc(v_tail_1364_);
lean_dec_ref(v_x_1362_);
v___x_1365_ = lean_array_push(v_x_1361_, v_key_1363_);
v_x_1361_ = v___x_1365_;
v_x_1362_ = v_tail_1364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(lean_object* v_as_1367_, size_t v_i_1368_, size_t v_stop_1369_, lean_object* v_b_1370_){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_usize_dec_eq(v_i_1368_, v_stop_1369_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; 
v___x_1372_ = lean_array_uget_borrowed(v_as_1367_, v_i_1368_);
lean_inc(v___x_1372_);
v___x_1373_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__10(v_b_1370_, v___x_1372_);
v___x_1374_ = ((size_t)1ULL);
v___x_1375_ = lean_usize_add(v_i_1368_, v___x_1374_);
v_i_1368_ = v___x_1375_;
v_b_1370_ = v___x_1373_;
goto _start;
}
else
{
return v_b_1370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11___boxed(lean_object* v_as_1377_, lean_object* v_i_1378_, lean_object* v_stop_1379_, lean_object* v_b_1380_){
_start:
{
size_t v_i_boxed_1381_; size_t v_stop_boxed_1382_; lean_object* v_res_1383_; 
v_i_boxed_1381_ = lean_unbox_usize(v_i_1378_);
lean_dec(v_i_1378_);
v_stop_boxed_1382_ = lean_unbox_usize(v_stop_1379_);
lean_dec(v_stop_1379_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_as_1377_, v_i_boxed_1381_, v_stop_boxed_1382_, v_b_1380_);
lean_dec_ref(v_as_1377_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(size_t v_sz_1384_, size_t v_i_1385_, lean_object* v_bs_1386_){
_start:
{
uint8_t v___x_1387_; 
v___x_1387_ = lean_usize_dec_lt(v_i_1385_, v_sz_1384_);
if (v___x_1387_ == 0)
{
return v_bs_1386_;
}
else
{
lean_object* v_v_1388_; lean_object* v___x_1389_; lean_object* v_bs_x27_1390_; lean_object* v___x_1391_; size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; 
v_v_1388_ = lean_array_uget(v_bs_1386_, v_i_1385_);
v___x_1389_ = lean_unsigned_to_nat(0u);
v_bs_x27_1390_ = lean_array_uset(v_bs_1386_, v_i_1385_, v___x_1389_);
v___x_1391_ = l_Lean_Expr_fvarId_x21(v_v_1388_);
lean_dec(v_v_1388_);
v___x_1392_ = ((size_t)1ULL);
v___x_1393_ = lean_usize_add(v_i_1385_, v___x_1392_);
v___x_1394_ = lean_array_uset(v_bs_x27_1390_, v_i_1385_, v___x_1391_);
v_i_1385_ = v___x_1393_;
v_bs_1386_ = v___x_1394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8___boxed(lean_object* v_sz_1396_, lean_object* v_i_1397_, lean_object* v_bs_1398_){
_start:
{
size_t v_sz_boxed_1399_; size_t v_i_boxed_1400_; lean_object* v_res_1401_; 
v_sz_boxed_1399_ = lean_unbox_usize(v_sz_1396_);
lean_dec(v_sz_1396_);
v_i_boxed_1400_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_res_1401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_boxed_1399_, v_i_boxed_1400_, v_bs_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__12(lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 0)
{
return v_x_1402_;
}
else
{
lean_object* v_key_1404_; lean_object* v_tail_1405_; lean_object* v___x_1406_; 
v_key_1404_ = lean_ctor_get(v_x_1403_, 0);
lean_inc(v_key_1404_);
v_tail_1405_ = lean_ctor_get(v_x_1403_, 2);
lean_inc(v_tail_1405_);
lean_dec_ref(v_x_1403_);
v___x_1406_ = lean_array_push(v_x_1402_, v_key_1404_);
v_x_1402_ = v___x_1406_;
v_x_1403_ = v_tail_1405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(lean_object* v_as_1408_, size_t v_i_1409_, size_t v_stop_1410_, lean_object* v_b_1411_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_usize_dec_eq(v_i_1409_, v_stop_1410_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; 
v___x_1413_ = lean_array_uget_borrowed(v_as_1408_, v_i_1409_);
lean_inc(v___x_1413_);
v___x_1414_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__12(v_b_1411_, v___x_1413_);
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1409_, v___x_1415_);
v_i_1409_ = v___x_1416_;
v_b_1411_ = v___x_1414_;
goto _start;
}
else
{
return v_b_1411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13___boxed(lean_object* v_as_1418_, lean_object* v_i_1419_, lean_object* v_stop_1420_, lean_object* v_b_1421_){
_start:
{
size_t v_i_boxed_1422_; size_t v_stop_boxed_1423_; lean_object* v_res_1424_; 
v_i_boxed_1422_ = lean_unbox_usize(v_i_1419_);
lean_dec(v_i_1419_);
v_stop_boxed_1423_ = lean_unbox_usize(v_stop_1420_);
lean_dec(v_stop_1420_);
v_res_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_as_1418_, v_i_boxed_1422_, v_stop_boxed_1423_, v_b_1421_);
lean_dec_ref(v_as_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
lean_object* v_ks_1429_; lean_object* v_vs_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1454_; 
v_ks_1429_ = lean_ctor_get(v_x_1425_, 0);
v_vs_1430_ = lean_ctor_get(v_x_1425_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_x_1425_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1432_ = v_x_1425_;
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_vs_1430_);
lean_inc(v_ks_1429_);
lean_dec(v_x_1425_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_array_get_size(v_ks_1429_);
v___x_1435_ = lean_nat_dec_lt(v_x_1426_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_dec(v_x_1426_);
v___x_1436_ = lean_array_push(v_ks_1429_, v_x_1427_);
v___x_1437_ = lean_array_push(v_vs_1430_, v_x_1428_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___x_1437_);
lean_ctor_set(v___x_1432_, 0, v___x_1436_);
v___x_1439_ = v___x_1432_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
else
{
lean_object* v_k_x27_1441_; uint8_t v___x_1442_; 
v_k_x27_1441_ = lean_array_fget_borrowed(v_ks_1429_, v_x_1426_);
v___x_1442_ = l_Lean_instBEqMVarId_beq(v_x_1427_, v_k_x27_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1444_; 
if (v_isShared_1433_ == 0)
{
v___x_1444_ = v___x_1432_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_ks_1429_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_vs_1430_);
v___x_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_add(v_x_1426_, v___x_1445_);
lean_dec(v_x_1426_);
v_x_1425_ = v___x_1444_;
v_x_1426_ = v___x_1446_;
goto _start;
}
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1449_ = lean_array_fset(v_ks_1429_, v_x_1426_, v_x_1427_);
v___x_1450_ = lean_array_fset(v_vs_1430_, v_x_1426_, v_x_1428_);
lean_dec(v_x_1426_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___x_1450_);
lean_ctor_set(v___x_1432_, 0, v___x_1449_);
v___x_1452_ = v___x_1432_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(lean_object* v_n_1455_, lean_object* v_k_1456_, lean_object* v_v_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_n_1455_, v___x_1458_, v_k_1456_, v_v_1457_);
return v___x_1459_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0(void){
_start:
{
size_t v___x_1460_; size_t v___x_1461_; size_t v___x_1462_; 
v___x_1460_ = ((size_t)5ULL);
v___x_1461_ = ((size_t)1ULL);
v___x_1462_ = lean_usize_shift_left(v___x_1461_, v___x_1460_);
return v___x_1462_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1(void){
_start:
{
size_t v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; 
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0);
v___x_1465_ = lean_usize_sub(v___x_1464_, v___x_1463_);
return v___x_1465_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(lean_object* v_x_1467_, size_t v_x_1468_, size_t v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_object* v_es_1472_; size_t v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; size_t v___x_1476_; lean_object* v_j_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_es_1472_ = lean_ctor_get(v_x_1467_, 0);
v___x_1473_ = ((size_t)5ULL);
v___x_1474_ = ((size_t)1ULL);
v___x_1475_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1);
v___x_1476_ = lean_usize_land(v_x_1468_, v___x_1475_);
v_j_1477_ = lean_usize_to_nat(v___x_1476_);
v___x_1478_ = lean_array_get_size(v_es_1472_);
v___x_1479_ = lean_nat_dec_lt(v_j_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec(v_j_1477_);
lean_dec(v_x_1471_);
lean_dec(v_x_1470_);
return v_x_1467_;
}
else
{
lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1516_; 
lean_inc_ref(v_es_1472_);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_x_1467_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_x_1467_, 0);
lean_dec(v_unused_1517_);
v___x_1481_ = v_x_1467_;
v_isShared_1482_ = v_isSharedCheck_1516_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v_x_1467_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1516_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_v_1483_; lean_object* v___x_1484_; lean_object* v_xs_x27_1485_; lean_object* v___y_1487_; 
v_v_1483_ = lean_array_fget(v_es_1472_, v_j_1477_);
v___x_1484_ = lean_box(0);
v_xs_x27_1485_ = lean_array_fset(v_es_1472_, v_j_1477_, v___x_1484_);
switch(lean_obj_tag(v_v_1483_))
{
case 0:
{
lean_object* v_key_1492_; lean_object* v_val_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1503_; 
v_key_1492_ = lean_ctor_get(v_v_1483_, 0);
v_val_1493_ = lean_ctor_get(v_v_1483_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_v_1483_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1495_ = v_v_1483_;
v_isShared_1496_ = v_isSharedCheck_1503_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_val_1493_);
lean_inc(v_key_1492_);
lean_dec(v_v_1483_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1503_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lean_instBEqMVarId_beq(v_x_1470_, v_key_1492_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_del_object(v___x_1495_);
v___x_1498_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1492_, v_val_1493_, v_x_1470_, v_x_1471_);
v___x_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
v___y_1487_ = v___x_1499_;
goto v___jp_1486_;
}
else
{
lean_object* v___x_1501_; 
lean_dec(v_val_1493_);
lean_dec(v_key_1492_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v_x_1471_);
lean_ctor_set(v___x_1495_, 0, v_x_1470_);
v___x_1501_ = v___x_1495_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_x_1470_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_x_1471_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
v___y_1487_ = v___x_1501_;
goto v___jp_1486_;
}
}
}
}
case 1:
{
lean_object* v_node_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1514_; 
v_node_1504_ = lean_ctor_get(v_v_1483_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_v_1483_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1506_ = v_v_1483_;
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_node_1504_);
lean_dec(v_v_1483_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1508_ = lean_usize_shift_right(v_x_1468_, v___x_1473_);
v___x_1509_ = lean_usize_add(v_x_1469_, v___x_1474_);
v___x_1510_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_node_1504_, v___x_1508_, v___x_1509_, v_x_1470_, v_x_1471_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1510_);
v___x_1512_ = v___x_1506_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
v___y_1487_ = v___x_1512_;
goto v___jp_1486_;
}
}
}
default: 
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_x_1470_);
lean_ctor_set(v___x_1515_, 1, v_x_1471_);
v___y_1487_ = v___x_1515_;
goto v___jp_1486_;
}
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = lean_array_fset(v_xs_x27_1485_, v_j_1477_, v___y_1487_);
lean_dec(v_j_1477_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1488_);
v___x_1490_ = v___x_1481_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
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
else
{
lean_object* v_ks_1518_; lean_object* v_vs_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1539_; 
v_ks_1518_ = lean_ctor_get(v_x_1467_, 0);
v_vs_1519_ = lean_ctor_get(v_x_1467_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_x_1467_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1521_ = v_x_1467_;
v_isShared_1522_ = v_isSharedCheck_1539_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_vs_1519_);
lean_inc(v_ks_1518_);
lean_dec(v_x_1467_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1539_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_ks_1518_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_vs_1519_);
v___x_1524_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v_newNode_1525_; uint8_t v___y_1527_; size_t v___x_1533_; uint8_t v___x_1534_; 
v_newNode_1525_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v___x_1524_, v_x_1470_, v_x_1471_);
v___x_1533_ = ((size_t)7ULL);
v___x_1534_ = lean_usize_dec_le(v___x_1533_, v_x_1469_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1525_);
v___x_1536_ = lean_unsigned_to_nat(4u);
v___x_1537_ = lean_nat_dec_lt(v___x_1535_, v___x_1536_);
lean_dec(v___x_1535_);
v___y_1527_ = v___x_1537_;
goto v___jp_1526_;
}
else
{
v___y_1527_ = v___x_1534_;
goto v___jp_1526_;
}
v___jp_1526_:
{
if (v___y_1527_ == 0)
{
lean_object* v_ks_1528_; lean_object* v_vs_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_ks_1528_ = lean_ctor_get(v_newNode_1525_, 0);
lean_inc_ref(v_ks_1528_);
v_vs_1529_ = lean_ctor_get(v_newNode_1525_, 1);
lean_inc_ref(v_vs_1529_);
lean_dec_ref(v_newNode_1525_);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2);
v___x_1532_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_x_1469_, v_ks_1528_, v_vs_1529_, v___x_1530_, v___x_1531_);
lean_dec_ref(v_vs_1529_);
lean_dec_ref(v_ks_1528_);
return v___x_1532_;
}
else
{
return v_newNode_1525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(size_t v_depth_1540_, lean_object* v_keys_1541_, lean_object* v_vals_1542_, lean_object* v_i_1543_, lean_object* v_entries_1544_){
_start:
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = lean_array_get_size(v_keys_1541_);
v___x_1546_ = lean_nat_dec_lt(v_i_1543_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_dec(v_i_1543_);
return v_entries_1544_;
}
else
{
lean_object* v_k_1547_; lean_object* v_v_1548_; uint64_t v___x_1549_; size_t v_h_1550_; size_t v___x_1551_; lean_object* v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; size_t v___x_1555_; size_t v_h_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_k_1547_ = lean_array_fget_borrowed(v_keys_1541_, v_i_1543_);
v_v_1548_ = lean_array_fget_borrowed(v_vals_1542_, v_i_1543_);
v___x_1549_ = l_Lean_instHashableMVarId_hash(v_k_1547_);
v_h_1550_ = lean_uint64_to_usize(v___x_1549_);
v___x_1551_ = ((size_t)5ULL);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = ((size_t)1ULL);
v___x_1554_ = lean_usize_sub(v_depth_1540_, v___x_1553_);
v___x_1555_ = lean_usize_mul(v___x_1551_, v___x_1554_);
v_h_1556_ = lean_usize_shift_right(v_h_1550_, v___x_1555_);
v___x_1557_ = lean_nat_add(v_i_1543_, v___x_1552_);
lean_dec(v_i_1543_);
lean_inc(v_v_1548_);
lean_inc(v_k_1547_);
v___x_1558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_entries_1544_, v_h_1556_, v_depth_1540_, v_k_1547_, v_v_1548_);
v_i_1543_ = v___x_1557_;
v_entries_1544_ = v___x_1558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg___boxed(lean_object* v_depth_1560_, lean_object* v_keys_1561_, lean_object* v_vals_1562_, lean_object* v_i_1563_, lean_object* v_entries_1564_){
_start:
{
size_t v_depth_boxed_1565_; lean_object* v_res_1566_; 
v_depth_boxed_1565_ = lean_unbox_usize(v_depth_1560_);
lean_dec(v_depth_1560_);
v_res_1566_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_boxed_1565_, v_keys_1561_, v_vals_1562_, v_i_1563_, v_entries_1564_);
lean_dec_ref(v_vals_1562_);
lean_dec_ref(v_keys_1561_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_, lean_object* v_x_1571_){
_start:
{
size_t v_x_22264__boxed_1572_; size_t v_x_22265__boxed_1573_; lean_object* v_res_1574_; 
v_x_22264__boxed_1572_ = lean_unbox_usize(v_x_1568_);
lean_dec(v_x_1568_);
v_x_22265__boxed_1573_ = lean_unbox_usize(v_x_1569_);
lean_dec(v_x_1569_);
v_res_1574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_1567_, v_x_22264__boxed_1572_, v_x_22265__boxed_1573_, v_x_1570_, v_x_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_){
_start:
{
uint64_t v___x_1578_; size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1578_ = l_Lean_instHashableMVarId_hash(v_x_1576_);
v___x_1579_ = lean_uint64_to_usize(v___x_1578_);
v___x_1580_ = ((size_t)1ULL);
v___x_1581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_1575_, v___x_1579_, v___x_1580_, v_x_1576_, v_x_1577_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(lean_object* v_mvarId_1582_, lean_object* v_val_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v_mctx_1587_; lean_object* v_cache_1588_; lean_object* v_zetaDeltaFVarIds_1589_; lean_object* v_postponed_1590_; lean_object* v_diag_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1618_; 
v___x_1586_ = lean_st_ref_take(v___y_1584_);
v_mctx_1587_ = lean_ctor_get(v___x_1586_, 0);
v_cache_1588_ = lean_ctor_get(v___x_1586_, 1);
v_zetaDeltaFVarIds_1589_ = lean_ctor_get(v___x_1586_, 2);
v_postponed_1590_ = lean_ctor_get(v___x_1586_, 3);
v_diag_1591_ = lean_ctor_get(v___x_1586_, 4);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1593_ = v___x_1586_;
v_isShared_1594_ = v_isSharedCheck_1618_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_diag_1591_);
lean_inc(v_postponed_1590_);
lean_inc(v_zetaDeltaFVarIds_1589_);
lean_inc(v_cache_1588_);
lean_inc(v_mctx_1587_);
lean_dec(v___x_1586_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1618_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_depth_1595_; lean_object* v_levelAssignDepth_1596_; lean_object* v_mvarCounter_1597_; lean_object* v_lDepth_1598_; lean_object* v_decls_1599_; lean_object* v_userNames_1600_; lean_object* v_lAssignment_1601_; lean_object* v_eAssignment_1602_; lean_object* v_dAssignment_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1617_; 
v_depth_1595_ = lean_ctor_get(v_mctx_1587_, 0);
v_levelAssignDepth_1596_ = lean_ctor_get(v_mctx_1587_, 1);
v_mvarCounter_1597_ = lean_ctor_get(v_mctx_1587_, 2);
v_lDepth_1598_ = lean_ctor_get(v_mctx_1587_, 3);
v_decls_1599_ = lean_ctor_get(v_mctx_1587_, 4);
v_userNames_1600_ = lean_ctor_get(v_mctx_1587_, 5);
v_lAssignment_1601_ = lean_ctor_get(v_mctx_1587_, 6);
v_eAssignment_1602_ = lean_ctor_get(v_mctx_1587_, 7);
v_dAssignment_1603_ = lean_ctor_get(v_mctx_1587_, 8);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_mctx_1587_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1605_ = v_mctx_1587_;
v_isShared_1606_ = v_isSharedCheck_1617_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_dAssignment_1603_);
lean_inc(v_eAssignment_1602_);
lean_inc(v_lAssignment_1601_);
lean_inc(v_userNames_1600_);
lean_inc(v_decls_1599_);
lean_inc(v_lDepth_1598_);
lean_inc(v_mvarCounter_1597_);
lean_inc(v_levelAssignDepth_1596_);
lean_inc(v_depth_1595_);
lean_dec(v_mctx_1587_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1617_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_eAssignment_1602_, v_mvarId_1582_, v_val_1583_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 7, v___x_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_depth_1595_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_levelAssignDepth_1596_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_mvarCounter_1597_);
lean_ctor_set(v_reuseFailAlloc_1616_, 3, v_lDepth_1598_);
lean_ctor_set(v_reuseFailAlloc_1616_, 4, v_decls_1599_);
lean_ctor_set(v_reuseFailAlloc_1616_, 5, v_userNames_1600_);
lean_ctor_set(v_reuseFailAlloc_1616_, 6, v_lAssignment_1601_);
lean_ctor_set(v_reuseFailAlloc_1616_, 7, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1616_, 8, v_dAssignment_1603_);
v___x_1609_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1609_);
v___x_1611_ = v___x_1593_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_cache_1588_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_zetaDeltaFVarIds_1589_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_postponed_1590_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_diag_1591_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_st_ref_set(v___y_1584_, v___x_1611_);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(lean_object* v_mvarId_1619_, lean_object* v_val_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_1619_, v_val_1620_, v___y_1621_);
lean_dec(v___y_1621_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(lean_object* v_msgData_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; lean_object* v_env_1631_; lean_object* v___x_1632_; lean_object* v_mctx_1633_; lean_object* v_lctx_1634_; lean_object* v_options_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1630_ = lean_st_ref_get(v___y_1628_);
v_env_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc_ref(v_env_1631_);
lean_dec(v___x_1630_);
v___x_1632_ = lean_st_ref_get(v___y_1626_);
v_mctx_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_ref(v_mctx_1633_);
lean_dec(v___x_1632_);
v_lctx_1634_ = lean_ctor_get(v___y_1625_, 2);
v_options_1635_ = lean_ctor_get(v___y_1627_, 2);
lean_inc_ref(v_options_1635_);
lean_inc_ref(v_lctx_1634_);
v___x_1636_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1636_, 0, v_env_1631_);
lean_ctor_set(v___x_1636_, 1, v_mctx_1633_);
lean_ctor_set(v___x_1636_, 2, v_lctx_1634_);
lean_ctor_set(v___x_1636_, 3, v_options_1635_);
v___x_1637_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v_msgData_1624_);
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(lean_object* v_msgData_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msgData_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(lean_object* v_msg_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_ref_1652_; lean_object* v___x_1653_; lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1662_; 
v_ref_1652_ = lean_ctor_get(v___y_1649_, 5);
v___x_1653_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msg_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
lean_inc(v_ref_1652_);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v_ref_1652_);
lean_ctor_set(v___x_1658_, 1, v_a_1654_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set_tag(v___x_1656_, 1);
lean_ctor_set(v___x_1656_, 0, v___x_1658_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg___boxed(lean_object* v_msg_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_bs_1672_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1673_ == 0)
{
return v_bs_1672_;
}
else
{
lean_object* v_v_1674_; lean_object* v___x_1675_; lean_object* v_bs_x27_1676_; lean_object* v___x_1677_; size_t v___x_1678_; size_t v___x_1679_; lean_object* v___x_1680_; 
v_v_1674_ = lean_array_uget(v_bs_1672_, v_i_1671_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v_bs_x27_1676_ = lean_array_uset(v_bs_1672_, v_i_1671_, v___x_1675_);
v___x_1677_ = l_Lean_mkFVar(v_v_1674_);
v___x_1678_ = ((size_t)1ULL);
v___x_1679_ = lean_usize_add(v_i_1671_, v___x_1678_);
v___x_1680_ = lean_array_uset(v_bs_x27_1676_, v_i_1671_, v___x_1677_);
v_i_1671_ = v___x_1679_;
v_bs_1672_ = v___x_1680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1___boxed(lean_object* v_sz_1682_, lean_object* v_i_1683_, lean_object* v_bs_1684_){
_start:
{
size_t v_sz_boxed_1685_; size_t v_i_boxed_1686_; lean_object* v_res_1687_; 
v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1682_);
lean_dec(v_sz_1682_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1683_);
lean_dec(v_i_1683_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_boxed_1685_, v_i_boxed_1686_, v_bs_1684_);
return v_res_1687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_box(0);
v___x_1695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3));
v___x_1696_ = l_Lean_mkConst(v___x_1695_, v___x_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = l_Lean_Level_ofNat(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
v___x_1704_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7);
v___x_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v___x_1703_);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8);
v___x_1707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6));
v___x_1708_ = l_Lean_mkConst(v___x_1707_, v___x_1706_);
return v___x_1708_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6));
v___x_1711_ = l_Lean_mkConst(v___x_1710_, v___x_1709_);
return v___x_1711_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_box(0);
v___x_1713_ = lean_unsigned_to_nat(16u);
v___x_1714_ = lean_mk_array(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(lean_object* v_fst_1721_, lean_object* v___x_1722_, lean_object* v_snd_1723_, lean_object* v_goal_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
size_t v___y_1732_; lean_object* v___y_1733_; uint8_t v___y_1734_; size_t v___y_1735_; lean_object* v___y_1736_; lean_object* v_a_1737_; size_t v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___x_1927_; lean_object* v___y_1929_; lean_object* v_relevantHyps_1946_; lean_object* v_size_1947_; lean_object* v_buckets_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1927_ = lean_st_ref_get(v___y_1725_);
v_relevantHyps_1946_ = lean_ctor_get(v___x_1927_, 1);
lean_inc_ref(v_relevantHyps_1946_);
lean_dec(v___x_1927_);
v_size_1947_ = lean_ctor_get(v_relevantHyps_1946_, 0);
lean_inc(v_size_1947_);
v_buckets_1948_ = lean_ctor_get(v_relevantHyps_1946_, 1);
lean_inc_ref(v_buckets_1948_);
lean_dec_ref(v_relevantHyps_1946_);
v___x_1949_ = lean_mk_empty_array_with_capacity(v_size_1947_);
lean_dec(v_size_1947_);
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_1951_ = lean_array_get_size(v_buckets_1948_);
v___x_1952_ = lean_nat_dec_lt(v___x_1950_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_dec_ref(v_buckets_1948_);
v___y_1929_ = v___x_1949_;
goto v___jp_1928_;
}
else
{
uint8_t v___x_1953_; 
v___x_1953_ = lean_nat_dec_le(v___x_1951_, v___x_1951_);
if (v___x_1953_ == 0)
{
if (v___x_1952_ == 0)
{
lean_dec_ref(v_buckets_1948_);
v___y_1929_ = v___x_1949_;
goto v___jp_1928_;
}
else
{
size_t v___x_1954_; size_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = ((size_t)0ULL);
v___x_1955_ = lean_usize_of_nat(v___x_1951_);
v___x_1956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_1948_, v___x_1954_, v___x_1955_, v___x_1949_);
lean_dec_ref(v_buckets_1948_);
v___y_1929_ = v___x_1956_;
goto v___jp_1928_;
}
}
else
{
size_t v___x_1957_; size_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = ((size_t)0ULL);
v___x_1958_ = lean_usize_of_nat(v___x_1951_);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_1948_, v___x_1957_, v___x_1958_, v___x_1949_);
lean_dec_ref(v_buckets_1948_);
v___y_1929_ = v___x_1959_;
goto v___jp_1928_;
}
}
v___jp_1731_:
{
lean_object* v_fst_1738_; lean_object* v_snd_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_fst_1738_ = lean_ctor_get(v_a_1737_, 0);
lean_inc(v_fst_1738_);
v_snd_1739_ = lean_ctor_get(v_a_1737_, 1);
lean_inc(v_snd_1739_);
lean_dec_ref(v_a_1737_);
v___x_1740_ = l_Lean_Expr_getAppFn(v_fst_1738_);
lean_dec(v_fst_1738_);
v___x_1741_ = l_Lean_Expr_mvarId_x21(v___x_1740_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = l_Lean_MVarId_getType(v___x_1741_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1742_);
v___x_1744_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1));
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4);
v___x_1747_ = lean_box_usize(v___y_1732_);
v___x_1748_ = lean_box(v___y_1734_);
lean_inc(v_fst_1721_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__3___boxed), 15, 8);
lean_closure_set(v___f_1749_, 0, v___x_1745_);
lean_closure_set(v___f_1749_, 1, v___y_1733_);
lean_closure_set(v___f_1749_, 2, v___x_1747_);
lean_closure_set(v___f_1749_, 3, v_a_1743_);
lean_closure_set(v___f_1749_, 4, v___x_1748_);
lean_closure_set(v___f_1749_, 5, v_fst_1721_);
lean_closure_set(v___f_1749_, 6, v___x_1722_);
lean_closure_set(v___f_1749_, 7, v___x_1746_);
v___x_1750_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_1744_, v___x_1746_, v___f_1749_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v_fst_1752_ = lean_ctor_get(v_a_1751_, 0);
lean_inc(v_fst_1752_);
v_snd_1753_ = lean_ctor_get(v_a_1751_, 1);
lean_inc(v_snd_1753_);
lean_dec(v_a_1751_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_snd_1753_);
v___x_1755_ = 0;
v___x_1756_ = lean_box(0);
v___x_1757_ = l_Lean_Meta_mkFreshExprMVar(v___x_1754_, v___x_1755_, v___x_1756_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; size_t v_sz_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = l_Lean_Expr_mvarId_x21(v_a_1758_);
lean_dec(v_a_1758_);
v___x_1760_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9);
v___x_1761_ = l_Lean_mkNatLit(v_fst_1721_);
v___x_1762_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10);
lean_inc(v___x_1759_);
v___x_1763_ = l_Lean_mkMVar(v___x_1759_);
v___x_1764_ = l_Lean_mkApp6(v___x_1760_, v___x_1746_, v___x_1761_, v_fst_1752_, v___x_1762_, v_snd_1723_, v___x_1763_);
lean_inc_ref(v___y_1736_);
v___x_1765_ = l_Array_append___redArg(v___y_1736_, v_snd_1739_);
v___x_1766_ = l_Lean_mkAppN(v___x_1764_, v___x_1765_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_goal_1724_, v___x_1766_, v___y_1727_);
lean_dec_ref(v___x_1767_);
v_sz_1768_ = lean_array_size(v_snd_1739_);
lean_inc(v_snd_1739_);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_1768_, v___y_1735_, v_snd_1739_);
v___x_1770_ = l_Lean_MVarId_tryClearMany_x27(v___x_1759_, v___x_1769_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_fst_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v_fst_1772_ = lean_ctor_get(v_a_1771_, 0);
lean_inc(v_fst_1772_);
lean_dec(v_a_1771_);
v___x_1773_ = lean_array_get_size(v___y_1736_);
lean_dec_ref(v___y_1736_);
v___x_1774_ = lean_array_get_size(v_snd_1739_);
lean_dec(v_snd_1739_);
v___x_1775_ = lean_nat_add(v___x_1773_, v___x_1774_);
v___x_1776_ = 0;
v___x_1777_ = l_Lean_Meta_introNCore(v_fst_1772_, v___x_1775_, v___x_1745_, v___x_1776_, v___x_1776_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1786_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_snd_1782_; lean_object* v___x_1784_; 
v_snd_1782_ = lean_ctor_get(v_a_1778_, 1);
lean_inc(v_snd_1782_);
lean_dec(v_a_1778_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_snd_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_snd_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_a_1787_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1777_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1777_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_snd_1739_);
lean_dec_ref(v___y_1736_);
v_a_1795_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1770_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1770_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_fst_1752_);
lean_dec(v_snd_1739_);
lean_dec_ref(v___y_1736_);
lean_dec(v_goal_1724_);
lean_dec_ref(v_snd_1723_);
lean_dec(v_fst_1721_);
v_a_1803_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1757_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1757_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_snd_1739_);
lean_dec_ref(v___y_1736_);
lean_dec(v_goal_1724_);
lean_dec_ref(v_snd_1723_);
lean_dec(v_fst_1721_);
v_a_1811_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1750_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1750_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_snd_1739_);
lean_dec_ref(v___y_1736_);
lean_dec_ref(v___y_1733_);
lean_dec(v_goal_1724_);
lean_dec_ref(v_snd_1723_);
lean_dec_ref(v___x_1722_);
lean_dec(v_fst_1721_);
v_a_1819_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1742_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1742_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
v___jp_1827_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_lctx_1834_; lean_object* v_mctx_1835_; lean_object* v_ngen_1836_; lean_object* v_quotContext_1837_; lean_object* v_nextMacroScope_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1831_ = lean_st_ref_get(v___y_1727_);
v___x_1832_ = lean_st_ref_get(v___y_1729_);
v___x_1833_ = lean_st_ref_get(v___y_1729_);
v_lctx_1834_ = lean_ctor_get(v___y_1726_, 2);
v_mctx_1835_ = lean_ctor_get(v___x_1831_, 0);
lean_inc_ref(v_mctx_1835_);
lean_dec(v___x_1831_);
v_ngen_1836_ = lean_ctor_get(v___x_1832_, 2);
lean_inc_ref(v_ngen_1836_);
lean_dec(v___x_1832_);
v_quotContext_1837_ = lean_ctor_get(v___y_1728_, 10);
v_nextMacroScope_1838_ = lean_ctor_get(v___x_1833_, 1);
lean_inc(v_nextMacroScope_1838_);
lean_dec(v___x_1833_);
v___x_1839_ = 1;
lean_inc_ref(v_lctx_1834_);
lean_inc(v_quotContext_1837_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_quotContext_1837_);
lean_ctor_set(v___x_1840_, 1, v_lctx_1834_);
v___x_1841_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
v___x_1842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1842_, 0, v_mctx_1835_);
lean_ctor_set(v___x_1842_, 1, v_nextMacroScope_1838_);
lean_ctor_set(v___x_1842_, 2, v_ngen_1836_);
lean_ctor_set(v___x_1842_, 3, v___x_1841_);
lean_inc(v_goal_1724_);
v___x_1843_ = l_Lean_MetavarContext_revert(v___y_1829_, v_goal_1724_, v___x_1839_, v___x_1840_, v___x_1842_);
lean_dec_ref(v___x_1840_);
lean_dec_ref(v___y_1829_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v_a_1845_; lean_object* v___x_1846_; lean_object* v_mctx_1847_; lean_object* v_nextMacroScope_1848_; lean_object* v_ngen_1849_; lean_object* v_cache_1850_; lean_object* v_zetaDeltaFVarIds_1851_; lean_object* v_postponed_1852_; lean_object* v_diag_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1879_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
v_a_1845_ = lean_ctor_get(v___x_1843_, 1);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1843_);
v___x_1846_ = lean_st_ref_take(v___y_1727_);
v_mctx_1847_ = lean_ctor_get(v_a_1845_, 0);
lean_inc_ref(v_mctx_1847_);
v_nextMacroScope_1848_ = lean_ctor_get(v_a_1845_, 1);
lean_inc(v_nextMacroScope_1848_);
v_ngen_1849_ = lean_ctor_get(v_a_1845_, 2);
lean_inc_ref(v_ngen_1849_);
lean_dec(v_a_1845_);
v_cache_1850_ = lean_ctor_get(v___x_1846_, 1);
v_zetaDeltaFVarIds_1851_ = lean_ctor_get(v___x_1846_, 2);
v_postponed_1852_ = lean_ctor_get(v___x_1846_, 3);
v_diag_1853_ = lean_ctor_get(v___x_1846_, 4);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; 
v_unused_1880_ = lean_ctor_get(v___x_1846_, 0);
lean_dec(v_unused_1880_);
v___x_1855_ = v___x_1846_;
v_isShared_1856_ = v_isSharedCheck_1879_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_diag_1853_);
lean_inc(v_postponed_1852_);
lean_inc(v_zetaDeltaFVarIds_1851_);
lean_inc(v_cache_1850_);
lean_dec(v___x_1846_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1879_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_mctx_1847_);
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_mctx_1847_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_cache_1850_);
lean_ctor_set(v_reuseFailAlloc_1878_, 2, v_zetaDeltaFVarIds_1851_);
lean_ctor_set(v_reuseFailAlloc_1878_, 3, v_postponed_1852_);
lean_ctor_set(v_reuseFailAlloc_1878_, 4, v_diag_1853_);
v___x_1858_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_env_1861_; lean_object* v_auxDeclNGen_1862_; lean_object* v_traceState_1863_; lean_object* v_cache_1864_; lean_object* v_messages_1865_; lean_object* v_infoState_1866_; lean_object* v_snapshotTasks_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1875_; 
v___x_1859_ = lean_st_ref_set(v___y_1727_, v___x_1858_);
v___x_1860_ = lean_st_ref_take(v___y_1729_);
v_env_1861_ = lean_ctor_get(v___x_1860_, 0);
v_auxDeclNGen_1862_ = lean_ctor_get(v___x_1860_, 3);
v_traceState_1863_ = lean_ctor_get(v___x_1860_, 4);
v_cache_1864_ = lean_ctor_get(v___x_1860_, 5);
v_messages_1865_ = lean_ctor_get(v___x_1860_, 6);
v_infoState_1866_ = lean_ctor_get(v___x_1860_, 7);
v_snapshotTasks_1867_ = lean_ctor_get(v___x_1860_, 8);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; lean_object* v_unused_1877_; 
v_unused_1876_ = lean_ctor_get(v___x_1860_, 2);
lean_dec(v_unused_1876_);
v_unused_1877_ = lean_ctor_get(v___x_1860_, 1);
lean_dec(v_unused_1877_);
v___x_1869_ = v___x_1860_;
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snapshotTasks_1867_);
lean_inc(v_infoState_1866_);
lean_inc(v_messages_1865_);
lean_inc(v_cache_1864_);
lean_inc(v_traceState_1863_);
lean_inc(v_auxDeclNGen_1862_);
lean_inc(v_env_1861_);
lean_dec(v___x_1860_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1875_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 2, v_ngen_1849_);
lean_ctor_set(v___x_1869_, 1, v_nextMacroScope_1848_);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_env_1861_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_nextMacroScope_1848_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_ngen_1849_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_auxDeclNGen_1862_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_traceState_1863_);
lean_ctor_set(v_reuseFailAlloc_1874_, 5, v_cache_1864_);
lean_ctor_set(v_reuseFailAlloc_1874_, 6, v_messages_1865_);
lean_ctor_set(v_reuseFailAlloc_1874_, 7, v_infoState_1866_);
lean_ctor_set(v_reuseFailAlloc_1874_, 8, v_snapshotTasks_1867_);
v___x_1872_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_st_ref_set(v___y_1729_, v___x_1872_);
lean_inc_ref(v___y_1830_);
v___y_1732_ = v___y_1828_;
v___y_1733_ = v___y_1830_;
v___y_1734_ = v___x_1839_;
v___y_1735_ = v___y_1828_;
v___y_1736_ = v___y_1830_;
v_a_1737_ = v_a_1844_;
goto v___jp_1731_;
}
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v_mctx_1883_; lean_object* v_nextMacroScope_1884_; lean_object* v_ngen_1885_; lean_object* v_cache_1886_; lean_object* v_zetaDeltaFVarIds_1887_; lean_object* v_postponed_1888_; lean_object* v_diag_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref(v___y_1830_);
lean_dec(v_goal_1724_);
lean_dec_ref(v_snd_1723_);
lean_dec_ref(v___x_1722_);
lean_dec(v_fst_1721_);
v_a_1881_ = lean_ctor_get(v___x_1843_, 1);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1843_);
v___x_1882_ = lean_st_ref_take(v___y_1727_);
v_mctx_1883_ = lean_ctor_get(v_a_1881_, 0);
lean_inc_ref(v_mctx_1883_);
v_nextMacroScope_1884_ = lean_ctor_get(v_a_1881_, 1);
lean_inc(v_nextMacroScope_1884_);
v_ngen_1885_ = lean_ctor_get(v_a_1881_, 2);
lean_inc_ref(v_ngen_1885_);
lean_dec(v_a_1881_);
v_cache_1886_ = lean_ctor_get(v___x_1882_, 1);
v_zetaDeltaFVarIds_1887_ = lean_ctor_get(v___x_1882_, 2);
v_postponed_1888_ = lean_ctor_get(v___x_1882_, 3);
v_diag_1889_ = lean_ctor_get(v___x_1882_, 4);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v___x_1882_, 0);
lean_dec(v_unused_1926_);
v___x_1891_ = v___x_1882_;
v_isShared_1892_ = v_isSharedCheck_1925_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_diag_1889_);
lean_inc(v_postponed_1888_);
lean_inc(v_zetaDeltaFVarIds_1887_);
lean_inc(v_cache_1886_);
lean_dec(v___x_1882_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1925_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_mctx_1883_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_mctx_1883_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_cache_1886_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_zetaDeltaFVarIds_1887_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_postponed_1888_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v_diag_1889_);
v___x_1894_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_env_1897_; lean_object* v_auxDeclNGen_1898_; lean_object* v_traceState_1899_; lean_object* v_cache_1900_; lean_object* v_messages_1901_; lean_object* v_infoState_1902_; lean_object* v_snapshotTasks_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1921_; 
v___x_1895_ = lean_st_ref_set(v___y_1727_, v___x_1894_);
v___x_1896_ = lean_st_ref_take(v___y_1729_);
v_env_1897_ = lean_ctor_get(v___x_1896_, 0);
v_auxDeclNGen_1898_ = lean_ctor_get(v___x_1896_, 3);
v_traceState_1899_ = lean_ctor_get(v___x_1896_, 4);
v_cache_1900_ = lean_ctor_get(v___x_1896_, 5);
v_messages_1901_ = lean_ctor_get(v___x_1896_, 6);
v_infoState_1902_ = lean_ctor_get(v___x_1896_, 7);
v_snapshotTasks_1903_ = lean_ctor_get(v___x_1896_, 8);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; lean_object* v_unused_1923_; 
v_unused_1922_ = lean_ctor_get(v___x_1896_, 2);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v___x_1896_, 1);
lean_dec(v_unused_1923_);
v___x_1905_ = v___x_1896_;
v_isShared_1906_ = v_isSharedCheck_1921_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_snapshotTasks_1903_);
lean_inc(v_infoState_1902_);
lean_inc(v_messages_1901_);
lean_inc(v_cache_1900_);
lean_inc(v_traceState_1899_);
lean_inc(v_auxDeclNGen_1898_);
lean_inc(v_env_1897_);
lean_dec(v___x_1896_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1921_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 2, v_ngen_1885_);
lean_ctor_set(v___x_1905_, 1, v_nextMacroScope_1884_);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_env_1897_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_nextMacroScope_1884_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_ngen_1885_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_auxDeclNGen_1898_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_traceState_1899_);
lean_ctor_set(v_reuseFailAlloc_1920_, 5, v_cache_1900_);
lean_ctor_set(v_reuseFailAlloc_1920_, 6, v_messages_1901_);
lean_ctor_set(v_reuseFailAlloc_1920_, 7, v_infoState_1902_);
lean_ctor_set(v_reuseFailAlloc_1920_, 8, v_snapshotTasks_1903_);
v___x_1908_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v___x_1909_ = lean_st_ref_set(v___y_1729_, v___x_1908_);
v___x_1910_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14);
v___x_1911_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v___x_1910_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
}
}
v___jp_1928_:
{
lean_object* v___x_1930_; lean_object* v_relevantTerms_1931_; lean_object* v_size_1932_; lean_object* v_buckets_1933_; size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1930_ = lean_st_ref_get(v___y_1725_);
v_relevantTerms_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc_ref(v_relevantTerms_1931_);
lean_dec(v___x_1930_);
v_size_1932_ = lean_ctor_get(v_relevantTerms_1931_, 0);
lean_inc(v_size_1932_);
v_buckets_1933_ = lean_ctor_get(v_relevantTerms_1931_, 1);
lean_inc_ref(v_buckets_1933_);
lean_dec_ref(v_relevantTerms_1931_);
v_sz_1934_ = lean_array_size(v___y_1929_);
v___x_1935_ = ((size_t)0ULL);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_1934_, v___x_1935_, v___y_1929_);
v___x_1937_ = lean_mk_empty_array_with_capacity(v_size_1932_);
lean_dec(v_size_1932_);
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = lean_array_get_size(v_buckets_1933_);
v___x_1940_ = lean_nat_dec_lt(v___x_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_dec_ref(v_buckets_1933_);
v___y_1828_ = v___x_1935_;
v___y_1829_ = v___x_1936_;
v___y_1830_ = v___x_1937_;
goto v___jp_1827_;
}
else
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_nat_dec_le(v___x_1939_, v___x_1939_);
if (v___x_1941_ == 0)
{
if (v___x_1940_ == 0)
{
lean_dec_ref(v_buckets_1933_);
v___y_1828_ = v___x_1935_;
v___y_1829_ = v___x_1936_;
v___y_1830_ = v___x_1937_;
goto v___jp_1827_;
}
else
{
size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_usize_of_nat(v___x_1939_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_1933_, v___x_1935_, v___x_1942_, v___x_1937_);
lean_dec_ref(v_buckets_1933_);
v___y_1828_ = v___x_1935_;
v___y_1829_ = v___x_1936_;
v___y_1830_ = v___x_1943_;
goto v___jp_1827_;
}
}
else
{
size_t v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_usize_of_nat(v___x_1939_);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_1933_, v___x_1935_, v___x_1944_, v___x_1937_);
lean_dec_ref(v_buckets_1933_);
v___y_1828_ = v___x_1935_;
v___y_1829_ = v___x_1936_;
v___y_1830_ = v___x_1945_;
goto v___jp_1827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(lean_object* v_fst_1960_, lean_object* v___x_1961_, lean_object* v_snd_1962_, lean_object* v_goal_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4(v_fst_1960_, v___x_1961_, v_snd_1962_, v_goal_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
return v_res_1970_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(lean_object* v_opts_1971_, lean_object* v_opt_1972_){
_start:
{
lean_object* v_name_1973_; lean_object* v_defValue_1974_; lean_object* v_map_1975_; lean_object* v___x_1976_; 
v_name_1973_ = lean_ctor_get(v_opt_1972_, 0);
v_defValue_1974_ = lean_ctor_get(v_opt_1972_, 1);
v_map_1975_ = lean_ctor_get(v_opts_1971_, 0);
v___x_1976_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1975_, v_name_1973_);
if (lean_obj_tag(v___x_1976_) == 0)
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_unbox(v_defValue_1974_);
return v___x_1977_;
}
else
{
lean_object* v_val_1978_; 
v_val_1978_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_val_1978_);
lean_dec_ref(v___x_1976_);
if (lean_obj_tag(v_val_1978_) == 1)
{
uint8_t v_v_1979_; 
v_v_1979_ = lean_ctor_get_uint8(v_val_1978_, 0);
lean_dec_ref(v_val_1978_);
return v_v_1979_;
}
else
{
uint8_t v___x_1980_; 
lean_dec(v_val_1978_);
v___x_1980_ = lean_unbox(v_defValue_1974_);
return v___x_1980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(lean_object* v_opts_1981_, lean_object* v_opt_1982_){
_start:
{
uint8_t v_res_1983_; lean_object* v_r_1984_; 
v_res_1983_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_opts_1981_, v_opt_1982_);
lean_dec_ref(v_opt_1982_);
lean_dec_ref(v_opts_1981_);
v_r_1984_ = lean_box(v_res_1983_);
return v_r_1984_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(uint8_t v___y_1993_, uint8_t v_suppressElabErrors_1994_, lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 1)
{
lean_object* v_pre_1996_; 
v_pre_1996_ = lean_ctor_get(v_x_1995_, 0);
switch(lean_obj_tag(v_pre_1996_))
{
case 1:
{
lean_object* v_pre_1997_; 
v_pre_1997_ = lean_ctor_get(v_pre_1996_, 0);
switch(lean_obj_tag(v_pre_1997_))
{
case 0:
{
lean_object* v_str_1998_; lean_object* v_str_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_str_1998_ = lean_ctor_get(v_x_1995_, 1);
v_str_1999_ = lean_ctor_get(v_pre_1996_, 1);
v___x_2000_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0));
v___x_2001_ = lean_string_dec_eq(v_str_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1));
v___x_2003_ = lean_string_dec_eq(v_str_1999_, v___x_2002_);
if (v___x_2003_ == 0)
{
return v___y_1993_;
}
else
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2));
v___x_2005_ = lean_string_dec_eq(v_str_1998_, v___x_2004_);
if (v___x_2005_ == 0)
{
return v___y_1993_;
}
else
{
return v_suppressElabErrors_1994_;
}
}
}
else
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3));
v___x_2007_ = lean_string_dec_eq(v_str_1998_, v___x_2006_);
if (v___x_2007_ == 0)
{
return v___y_1993_;
}
else
{
return v_suppressElabErrors_1994_;
}
}
}
case 1:
{
lean_object* v_pre_2008_; 
v_pre_2008_ = lean_ctor_get(v_pre_1997_, 0);
if (lean_obj_tag(v_pre_2008_) == 0)
{
lean_object* v_str_2009_; lean_object* v_str_2010_; lean_object* v_str_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v_str_2009_ = lean_ctor_get(v_x_1995_, 1);
v_str_2010_ = lean_ctor_get(v_pre_1996_, 1);
v_str_2011_ = lean_ctor_get(v_pre_1997_, 1);
v___x_2012_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4));
v___x_2013_ = lean_string_dec_eq(v_str_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
return v___y_1993_;
}
else
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5));
v___x_2015_ = lean_string_dec_eq(v_str_2010_, v___x_2014_);
if (v___x_2015_ == 0)
{
return v___y_1993_;
}
else
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6));
v___x_2017_ = lean_string_dec_eq(v_str_2009_, v___x_2016_);
if (v___x_2017_ == 0)
{
return v___y_1993_;
}
else
{
return v_suppressElabErrors_1994_;
}
}
}
}
else
{
return v___y_1993_;
}
}
default: 
{
return v___y_1993_;
}
}
}
case 0:
{
lean_object* v_str_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_str_2018_ = lean_ctor_get(v_x_1995_, 1);
v___x_2019_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7));
v___x_2020_ = lean_string_dec_eq(v_str_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
return v___y_1993_;
}
else
{
return v_suppressElabErrors_1994_;
}
}
default: 
{
return v___y_1993_;
}
}
}
else
{
return v___y_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed(lean_object* v___y_2021_, lean_object* v_suppressElabErrors_2022_, lean_object* v_x_2023_){
_start:
{
uint8_t v___y_23109__boxed_2024_; uint8_t v_suppressElabErrors_boxed_2025_; uint8_t v_res_2026_; lean_object* v_r_2027_; 
v___y_23109__boxed_2024_ = lean_unbox(v___y_2021_);
v_suppressElabErrors_boxed_2025_ = lean_unbox(v_suppressElabErrors_2022_);
v_res_2026_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(v___y_23109__boxed_2024_, v_suppressElabErrors_boxed_2025_, v_x_2023_);
lean_dec(v_x_2023_);
v_r_2027_ = lean_box(v_res_2026_);
return v_r_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(lean_object* v_ref_2029_, lean_object* v_msgData_2030_, uint8_t v_severity_2031_, uint8_t v_isSilent_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
uint8_t v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; uint8_t v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2075_; uint8_t v___y_2076_; uint8_t v___y_2077_; lean_object* v___y_2078_; uint8_t v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2102_; uint8_t v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2111_; lean_object* v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2114_; uint8_t v___y_2115_; lean_object* v___y_2116_; uint8_t v___y_2117_; uint8_t v___x_2122_; lean_object* v___y_2124_; uint8_t v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; uint8_t v___y_2129_; uint8_t v___y_2130_; uint8_t v___y_2132_; uint8_t v___x_2147_; 
v___x_2122_ = 2;
v___x_2147_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2031_, v___x_2122_);
if (v___x_2147_ == 0)
{
v___y_2132_ = v___x_2147_;
goto v___jp_2131_;
}
else
{
uint8_t v___x_2148_; 
lean_inc_ref(v_msgData_2030_);
v___x_2148_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2030_);
v___y_2132_ = v___x_2148_;
goto v___jp_2131_;
}
v___jp_2038_:
{
lean_object* v___x_2048_; lean_object* v_currNamespace_2049_; lean_object* v_openDecls_2050_; lean_object* v_env_2051_; lean_object* v_nextMacroScope_2052_; lean_object* v_ngen_2053_; lean_object* v_auxDeclNGen_2054_; lean_object* v_traceState_2055_; lean_object* v_cache_2056_; lean_object* v_messages_2057_; lean_object* v_infoState_2058_; lean_object* v_snapshotTasks_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2073_; 
v___x_2048_ = lean_st_ref_take(v___y_2047_);
v_currNamespace_2049_ = lean_ctor_get(v___y_2046_, 6);
v_openDecls_2050_ = lean_ctor_get(v___y_2046_, 7);
v_env_2051_ = lean_ctor_get(v___x_2048_, 0);
v_nextMacroScope_2052_ = lean_ctor_get(v___x_2048_, 1);
v_ngen_2053_ = lean_ctor_get(v___x_2048_, 2);
v_auxDeclNGen_2054_ = lean_ctor_get(v___x_2048_, 3);
v_traceState_2055_ = lean_ctor_get(v___x_2048_, 4);
v_cache_2056_ = lean_ctor_get(v___x_2048_, 5);
v_messages_2057_ = lean_ctor_get(v___x_2048_, 6);
v_infoState_2058_ = lean_ctor_get(v___x_2048_, 7);
v_snapshotTasks_2059_ = lean_ctor_get(v___x_2048_, 8);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2061_ = v___x_2048_;
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_snapshotTasks_2059_);
lean_inc(v_infoState_2058_);
lean_inc(v_messages_2057_);
lean_inc(v_cache_2056_);
lean_inc(v_traceState_2055_);
lean_inc(v_auxDeclNGen_2054_);
lean_inc(v_ngen_2053_);
lean_inc(v_nextMacroScope_2052_);
lean_inc(v_env_2051_);
lean_dec(v___x_2048_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
lean_inc(v_openDecls_2050_);
lean_inc(v_currNamespace_2049_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v_currNamespace_2049_);
lean_ctor_set(v___x_2063_, 1, v_openDecls_2050_);
v___x_2064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___y_2043_);
lean_inc_ref(v___y_2044_);
lean_inc_ref(v___y_2045_);
v___x_2065_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2065_, 0, v___y_2045_);
lean_ctor_set(v___x_2065_, 1, v___y_2040_);
lean_ctor_set(v___x_2065_, 2, v___y_2041_);
lean_ctor_set(v___x_2065_, 3, v___y_2044_);
lean_ctor_set(v___x_2065_, 4, v___x_2064_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*5, v___y_2042_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*5 + 1, v___y_2039_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*5 + 2, v_isSilent_2032_);
v___x_2066_ = l_Lean_MessageLog_add(v___x_2065_, v_messages_2057_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 6, v___x_2066_);
v___x_2068_ = v___x_2061_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_env_2051_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_nextMacroScope_2052_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_ngen_2053_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v_auxDeclNGen_2054_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v_traceState_2055_);
lean_ctor_set(v_reuseFailAlloc_2072_, 5, v_cache_2056_);
lean_ctor_set(v_reuseFailAlloc_2072_, 6, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2072_, 7, v_infoState_2058_);
lean_ctor_set(v_reuseFailAlloc_2072_, 8, v_snapshotTasks_2059_);
v___x_2068_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = lean_st_ref_set(v___y_2047_, v___x_2068_);
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
v___jp_2074_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2098_; 
v___x_2083_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2030_);
v___x_2084_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v___x_2083_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2098_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2098_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_inc_ref(v___y_2078_);
v___x_2089_ = l_Lean_FileMap_toPosition(v___y_2078_, v___y_2080_);
lean_dec(v___y_2080_);
lean_inc_ref(v___y_2078_);
v___x_2090_ = l_Lean_FileMap_toPosition(v___y_2078_, v___y_2082_);
lean_dec(v___y_2082_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___x_2092_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0));
if (v___y_2076_ == 0)
{
lean_del_object(v___x_2087_);
lean_dec_ref(v___y_2075_);
v___y_2039_ = v___y_2077_;
v___y_2040_ = v___x_2089_;
v___y_2041_ = v___x_2091_;
v___y_2042_ = v___y_2079_;
v___y_2043_ = v_a_2085_;
v___y_2044_ = v___x_2092_;
v___y_2045_ = v___y_2081_;
v___y_2046_ = v___y_2035_;
v___y_2047_ = v___y_2036_;
goto v___jp_2038_;
}
else
{
uint8_t v___x_2093_; 
lean_inc(v_a_2085_);
v___x_2093_ = l_Lean_MessageData_hasTag(v___y_2075_, v_a_2085_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
lean_dec_ref(v___x_2091_);
lean_dec_ref(v___x_2089_);
lean_dec(v_a_2085_);
v___x_2094_ = lean_box(0);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2094_);
v___x_2096_ = v___x_2087_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
else
{
lean_del_object(v___x_2087_);
v___y_2039_ = v___y_2077_;
v___y_2040_ = v___x_2089_;
v___y_2041_ = v___x_2091_;
v___y_2042_ = v___y_2079_;
v___y_2043_ = v_a_2085_;
v___y_2044_ = v___x_2092_;
v___y_2045_ = v___y_2081_;
v___y_2046_ = v___y_2035_;
v___y_2047_ = v___y_2036_;
goto v___jp_2038_;
}
}
}
}
v___jp_2099_:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Syntax_getTailPos_x3f(v___y_2101_, v___y_2105_);
lean_dec(v___y_2101_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_inc(v___y_2107_);
v___y_2075_ = v___y_2100_;
v___y_2076_ = v___y_2102_;
v___y_2077_ = v___y_2103_;
v___y_2078_ = v___y_2104_;
v___y_2079_ = v___y_2105_;
v___y_2080_ = v___y_2107_;
v___y_2081_ = v___y_2106_;
v___y_2082_ = v___y_2107_;
goto v___jp_2074_;
}
else
{
lean_object* v_val_2109_; 
v_val_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_val_2109_);
lean_dec_ref(v___x_2108_);
v___y_2075_ = v___y_2100_;
v___y_2076_ = v___y_2102_;
v___y_2077_ = v___y_2103_;
v___y_2078_ = v___y_2104_;
v___y_2079_ = v___y_2105_;
v___y_2080_ = v___y_2107_;
v___y_2081_ = v___y_2106_;
v___y_2082_ = v_val_2109_;
goto v___jp_2074_;
}
}
v___jp_2110_:
{
lean_object* v_ref_2118_; lean_object* v___x_2119_; 
v_ref_2118_ = l_Lean_replaceRef(v_ref_2029_, v___y_2112_);
v___x_2119_ = l_Lean_Syntax_getPos_x3f(v_ref_2118_, v___y_2115_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
v___y_2100_ = v___y_2111_;
v___y_2101_ = v_ref_2118_;
v___y_2102_ = v___y_2113_;
v___y_2103_ = v___y_2117_;
v___y_2104_ = v___y_2114_;
v___y_2105_ = v___y_2115_;
v___y_2106_ = v___y_2116_;
v___y_2107_ = v___x_2120_;
goto v___jp_2099_;
}
else
{
lean_object* v_val_2121_; 
v_val_2121_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_val_2121_);
lean_dec_ref(v___x_2119_);
v___y_2100_ = v___y_2111_;
v___y_2101_ = v_ref_2118_;
v___y_2102_ = v___y_2113_;
v___y_2103_ = v___y_2117_;
v___y_2104_ = v___y_2114_;
v___y_2105_ = v___y_2115_;
v___y_2106_ = v___y_2116_;
v___y_2107_ = v_val_2121_;
goto v___jp_2099_;
}
}
v___jp_2123_:
{
if (v___y_2130_ == 0)
{
v___y_2111_ = v___y_2127_;
v___y_2112_ = v___y_2124_;
v___y_2113_ = v___y_2125_;
v___y_2114_ = v___y_2126_;
v___y_2115_ = v___y_2129_;
v___y_2116_ = v___y_2128_;
v___y_2117_ = v_severity_2031_;
goto v___jp_2110_;
}
else
{
v___y_2111_ = v___y_2127_;
v___y_2112_ = v___y_2124_;
v___y_2113_ = v___y_2125_;
v___y_2114_ = v___y_2126_;
v___y_2115_ = v___y_2129_;
v___y_2116_ = v___y_2128_;
v___y_2117_ = v___x_2122_;
goto v___jp_2110_;
}
}
v___jp_2131_:
{
if (v___y_2132_ == 0)
{
lean_object* v_fileName_2133_; lean_object* v_fileMap_2134_; lean_object* v_options_2135_; lean_object* v_ref_2136_; uint8_t v_suppressElabErrors_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___f_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; 
v_fileName_2133_ = lean_ctor_get(v___y_2035_, 0);
v_fileMap_2134_ = lean_ctor_get(v___y_2035_, 1);
v_options_2135_ = lean_ctor_get(v___y_2035_, 2);
v_ref_2136_ = lean_ctor_get(v___y_2035_, 5);
v_suppressElabErrors_2137_ = lean_ctor_get_uint8(v___y_2035_, sizeof(void*)*14 + 1);
v___x_2138_ = lean_box(v___y_2132_);
v___x_2139_ = lean_box(v_suppressElabErrors_2137_);
v___f_2140_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2140_, 0, v___x_2138_);
lean_closure_set(v___f_2140_, 1, v___x_2139_);
v___x_2141_ = 1;
v___x_2142_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2031_, v___x_2141_);
if (v___x_2142_ == 0)
{
v___y_2124_ = v_ref_2136_;
v___y_2125_ = v_suppressElabErrors_2137_;
v___y_2126_ = v_fileMap_2134_;
v___y_2127_ = v___f_2140_;
v___y_2128_ = v_fileName_2133_;
v___y_2129_ = v___y_2132_;
v___y_2130_ = v___x_2142_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = l_Lean_warningAsError;
v___x_2144_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_options_2135_, v___x_2143_);
v___y_2124_ = v_ref_2136_;
v___y_2125_ = v_suppressElabErrors_2137_;
v___y_2126_ = v_fileMap_2134_;
v___y_2127_ = v___f_2140_;
v___y_2128_ = v_fileName_2133_;
v___y_2129_ = v___y_2132_;
v___y_2130_ = v___x_2144_;
goto v___jp_2123_;
}
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v_msgData_2030_);
v___x_2145_ = lean_box(0);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(lean_object* v_ref_2149_, lean_object* v_msgData_2150_, lean_object* v_severity_2151_, lean_object* v_isSilent_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
uint8_t v_severity_boxed_2158_; uint8_t v_isSilent_boxed_2159_; lean_object* v_res_2160_; 
v_severity_boxed_2158_ = lean_unbox(v_severity_2151_);
v_isSilent_boxed_2159_ = lean_unbox(v_isSilent_2152_);
v_res_2160_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2149_, v_msgData_2150_, v_severity_boxed_2158_, v_isSilent_boxed_2159_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v_ref_2149_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(lean_object* v_msgData_2161_, uint8_t v_severity_2162_, uint8_t v_isSilent_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_ref_2170_; lean_object* v___x_2171_; 
v_ref_2170_ = lean_ctor_get(v___y_2167_, 5);
v___x_2171_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2170_, v_msgData_2161_, v_severity_2162_, v_isSilent_2163_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(lean_object* v_msgData_2172_, lean_object* v_severity_2173_, lean_object* v_isSilent_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v_severity_boxed_2181_; uint8_t v_isSilent_boxed_2182_; lean_object* v_res_2183_; 
v_severity_boxed_2181_ = lean_unbox(v_severity_2173_);
v_isSilent_boxed_2182_ = lean_unbox(v_isSilent_2174_);
v_res_2183_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_2172_, v_severity_boxed_2181_, v_isSilent_boxed_2182_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(lean_object* v_msgData_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = 1;
v___x_2192_ = 0;
v___x_2193_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_2184_, v___x_2191_, v___x_2192_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(lean_object* v_msgData_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(v_msgData_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
return v_res_2201_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__0));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__3));
v___x_2212_ = l_Lean_mkConst(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__4);
v___x_2214_ = l_Lean_MessageData_ofExpr(v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__5);
v___x_2216_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__1);
v___x_2217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(lean_object* v_goal_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v___x_2225_; 
lean_inc(v_goal_2218_);
v___x_2225_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_findNumBitsEq(v_goal_2218_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref(v___x_2225_);
if (lean_obj_tag(v_a_2226_) == 1)
{
lean_object* v_val_2227_; lean_object* v_fst_2228_; lean_object* v_snd_2229_; lean_object* v___x_2230_; lean_object* v___f_2231_; lean_object* v___x_2232_; 
v_val_2227_ = lean_ctor_get(v_a_2226_, 0);
lean_inc(v_val_2227_);
lean_dec_ref(v_a_2226_);
v_fst_2228_ = lean_ctor_get(v_val_2227_, 0);
lean_inc(v_fst_2228_);
v_snd_2229_ = lean_ctor_get(v_val_2227_, 1);
lean_inc(v_snd_2229_);
lean_dec(v_val_2227_);
v___x_2230_ = l_Lean_instInhabitedExpr;
lean_inc(v_goal_2218_);
v___f_2231_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___boxed), 10, 4);
lean_closure_set(v___f_2231_, 0, v_fst_2228_);
lean_closure_set(v___f_2231_, 1, v___x_2230_);
lean_closure_set(v___f_2231_, 2, v_snd_2229_);
lean_closure_set(v___f_2231_, 3, v_goal_2218_);
v___x_2232_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_2218_, v___f_2231_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_dec(v_a_2226_);
v___x_2233_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___closed__6);
v___x_2234_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15(v___x_2233_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v___x_2234_, 0);
lean_dec(v_unused_2242_);
v___x_2236_ = v___x_2234_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_dec(v___x_2234_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v_goal_2218_);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_goal_2218_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_goal_2218_);
v_a_2243_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2234_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2234_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_goal_2218_);
v_a_2251_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2225_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2225_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___boxed(lean_object* v_goal_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(v_goal_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0(lean_object* v_00_u03b2_2267_, lean_object* v_m_2268_, lean_object* v_a_2269_, lean_object* v_b_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_m_2268_, v_a_2269_, v_b_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2(lean_object* v_as_2272_, size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_b_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_2272_, v_sz_2273_, v_i_2274_, v_b_2275_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(lean_object* v_as_2283_, lean_object* v_sz_2284_, lean_object* v_i_2285_, lean_object* v_b_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2284_);
lean_dec(v_sz_2284_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2285_);
lean_dec(v_i_2285_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__2(v_as_2283_, v_sz_boxed_2293_, v_i_boxed_2294_, v_b_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v_as_2283_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3(lean_object* v_00_u03b2_2296_, lean_object* v_m_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_2297_, v_a_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(lean_object* v_00_u03b2_2300_, lean_object* v_m_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3(v_00_u03b2_2300_, v_m_2301_, v_a_2302_);
lean_dec_ref(v_a_2302_);
lean_dec_ref(v_m_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(lean_object* v_00_u03b1_2304_, lean_object* v_inst_2305_, lean_object* v_declInfos_2306_, lean_object* v_k_2307_, uint8_t v_kind_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___redArg(v_inst_2305_, v_declInfos_2306_, v_k_2307_, v_kind_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(lean_object* v_00_u03b1_2316_, lean_object* v_inst_2317_, lean_object* v_declInfos_2318_, lean_object* v_k_2319_, lean_object* v_kind_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v_kind_boxed_2327_; lean_object* v_res_2328_; 
v_kind_boxed_2327_ = lean_unbox(v_kind_2320_);
v_res_2328_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5(v_00_u03b1_2316_, v_inst_2317_, v_declInfos_2318_, v_k_2319_, v_kind_boxed_2327_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(lean_object* v_00_u03b1_2329_, lean_object* v_name_2330_, uint8_t v_bi_2331_, lean_object* v_type_2332_, lean_object* v_k_2333_, uint8_t v_kind_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_2330_, v_bi_2331_, v_type_2332_, v_k_2333_, v_kind_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(lean_object* v_00_u03b1_2342_, lean_object* v_name_2343_, lean_object* v_bi_2344_, lean_object* v_type_2345_, lean_object* v_k_2346_, lean_object* v_kind_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v_bi_boxed_2354_; uint8_t v_kind_boxed_2355_; lean_object* v_res_2356_; 
v_bi_boxed_2354_ = lean_unbox(v_bi_2344_);
v_kind_boxed_2355_ = lean_unbox(v_kind_2347_);
v_res_2356_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(v_00_u03b1_2342_, v_name_2343_, v_bi_boxed_2354_, v_type_2345_, v_k_2346_, v_kind_boxed_2355_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6(lean_object* v_00_u03b1_2357_, lean_object* v_name_2358_, lean_object* v_type_2359_, lean_object* v_k_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_2358_, v_type_2359_, v_k_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(lean_object* v_00_u03b1_2368_, lean_object* v_name_2369_, lean_object* v_type_2370_, lean_object* v_k_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6(v_00_u03b1_2368_, v_name_2369_, v_type_2370_, v_k_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7(lean_object* v_mvarId_2379_, lean_object* v_val_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_2379_, v_val_2380_, v___y_2383_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(lean_object* v_mvarId_2388_, lean_object* v_val_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7(v_mvarId_2388_, v_val_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9(lean_object* v_00_u03b1_2397_, lean_object* v_msg_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_msg_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__9(v_00_u03b1_2405_, v_msg_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(lean_object* v_00_u03b2_2413_, lean_object* v_a_2414_, lean_object* v_x_2415_){
_start:
{
uint8_t v___x_2416_; 
v___x_2416_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2414_, v_x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2417_, lean_object* v_a_2418_, lean_object* v_x_2419_){
_start:
{
uint8_t v_res_2420_; lean_object* v_r_2421_; 
v_res_2420_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(v_00_u03b2_2417_, v_a_2418_, v_x_2419_);
lean_dec(v_x_2419_);
lean_dec_ref(v_a_2418_);
v_r_2421_ = lean_box(v_res_2420_);
return v_r_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(lean_object* v_00_u03b2_2422_, lean_object* v_data_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_data_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(lean_object* v_00_u03b2_2425_, lean_object* v_a_2426_, lean_object* v_b_2427_, lean_object* v_x_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_2426_, v_b_2427_, v_x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(lean_object* v_00_u03b2_2430_, lean_object* v_a_2431_, lean_object* v_x_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_2431_, v_x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2434_, lean_object* v_a_2435_, lean_object* v_x_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(v_00_u03b2_2434_, v_a_2435_, v_x_2436_);
lean_dec(v_x_2436_);
lean_dec_ref(v_a_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(lean_object* v_00_u03b1_2438_, lean_object* v_inst_2439_, lean_object* v_declInfos_2440_, lean_object* v_k_2441_, uint8_t v_kind_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___redArg(v_inst_2439_, v_declInfos_2440_, v_k_2441_, v_kind_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(lean_object* v_00_u03b1_2450_, lean_object* v_inst_2451_, lean_object* v_declInfos_2452_, lean_object* v_k_2453_, lean_object* v_kind_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v_kind_boxed_2461_; lean_object* v_res_2462_; 
v_kind_boxed_2461_ = lean_unbox(v_kind_2454_);
v_res_2462_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v_00_u03b1_2450_, v_inst_2451_, v_declInfos_2452_, v_k_2453_, v_kind_boxed_2461_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(lean_object* v_00_u03b2_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_, lean_object* v_x_2466_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_x_2464_, v_x_2465_, v_x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2468_, lean_object* v_i_2469_, lean_object* v_source_2470_, lean_object* v_target_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v_i_2469_, v_source_2470_, v_target_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(lean_object* v_00_u03b1_2473_, lean_object* v_inst_2474_, lean_object* v_declInfos_2475_, lean_object* v_k_2476_, uint8_t v_kind_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___redArg(v_inst_2474_, v_declInfos_2475_, v_k_2476_, v_kind_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2485_, lean_object* v_inst_2486_, lean_object* v_declInfos_2487_, lean_object* v_k_2488_, lean_object* v_kind_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
uint8_t v_kind_boxed_2496_; lean_object* v_res_2497_; 
v_kind_boxed_2496_ = lean_unbox(v_kind_2489_);
v_res_2497_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v_00_u03b1_2485_, v_inst_2486_, v_declInfos_2487_, v_k_2488_, v_kind_boxed_2496_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(lean_object* v_00_u03b2_2498_, lean_object* v_x_2499_, size_t v_x_2500_, size_t v_x_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_2499_, v_x_2500_, v_x_2501_, v_x_2502_, v_x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(lean_object* v_00_u03b2_2505_, lean_object* v_x_2506_, lean_object* v_x_2507_, lean_object* v_x_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_){
_start:
{
size_t v_x_23751__boxed_2511_; size_t v_x_23752__boxed_2512_; lean_object* v_res_2513_; 
v_x_23751__boxed_2511_ = lean_unbox_usize(v_x_2507_);
lean_dec(v_x_2507_);
v_x_23752__boxed_2512_ = lean_unbox_usize(v_x_2508_);
lean_dec(v_x_2508_);
v_res_2513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(v_00_u03b2_2505_, v_x_2506_, v_x_23751__boxed_2511_, v_x_23752__boxed_2512_, v_x_2509_, v_x_2510_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(lean_object* v_ref_2514_, lean_object* v_msgData_2515_, uint8_t v_severity_2516_, uint8_t v_isSilent_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_2514_, v_msgData_2515_, v_severity_2516_, v_isSilent_2517_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(lean_object* v_ref_2525_, lean_object* v_msgData_2526_, lean_object* v_severity_2527_, lean_object* v_isSilent_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
uint8_t v_severity_boxed_2535_; uint8_t v_isSilent_boxed_2536_; lean_object* v_res_2537_; 
v_severity_boxed_2535_ = lean_unbox(v_severity_2527_);
v_isSilent_boxed_2536_ = lean_unbox(v_isSilent_2528_);
v_res_2537_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(v_ref_2525_, v_msgData_2526_, v_severity_boxed_2535_, v_isSilent_boxed_2536_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec(v_ref_2525_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(lean_object* v_00_u03b2_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_x_2539_, v_x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(lean_object* v_00_u03b2_2542_, lean_object* v_n_2543_, lean_object* v_k_2544_, lean_object* v_v_2545_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v_n_2543_, v_k_2544_, v_v_2545_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(lean_object* v_00_u03b2_2547_, size_t v_depth_2548_, lean_object* v_keys_2549_, lean_object* v_vals_2550_, lean_object* v_heq_2551_, lean_object* v_i_2552_, lean_object* v_entries_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_2548_, v_keys_2549_, v_vals_2550_, v_i_2552_, v_entries_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(lean_object* v_00_u03b2_2555_, lean_object* v_depth_2556_, lean_object* v_keys_2557_, lean_object* v_vals_2558_, lean_object* v_heq_2559_, lean_object* v_i_2560_, lean_object* v_entries_2561_){
_start:
{
size_t v_depth_boxed_2562_; lean_object* v_res_2563_; 
v_depth_boxed_2562_ = lean_unbox_usize(v_depth_2556_);
lean_dec(v_depth_2556_);
v_res_2563_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(v_00_u03b2_2555_, v_depth_boxed_2562_, v_keys_2557_, v_vals_2558_, v_heq_2559_, v_i_2560_, v_entries_2561_);
lean_dec_ref(v_vals_2558_);
lean_dec_ref(v_keys_2557_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(lean_object* v_00_u03b1_2564_, lean_object* v_acc_2565_, lean_object* v_declInfos_2566_, lean_object* v_k_2567_, uint8_t v_kind_2568_, lean_object* v_inst_2569_, lean_object* v_name_2570_, uint8_t v_bi_2571_, lean_object* v_type_2572_, uint8_t v_kind_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___redArg(v_acc_2565_, v_declInfos_2566_, v_k_2567_, v_kind_2568_, v_inst_2569_, v_name_2570_, v_bi_2571_, v_type_2572_, v_kind_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(lean_object* v_00_u03b1_2581_, lean_object* v_acc_2582_, lean_object* v_declInfos_2583_, lean_object* v_k_2584_, lean_object* v_kind_2585_, lean_object* v_inst_2586_, lean_object* v_name_2587_, lean_object* v_bi_2588_, lean_object* v_type_2589_, lean_object* v_kind_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
uint8_t v_kind_boxed_2597_; uint8_t v_bi_boxed_2598_; uint8_t v_kind_boxed_2599_; lean_object* v_res_2600_; 
v_kind_boxed_2597_ = lean_unbox(v_kind_2585_);
v_bi_boxed_2598_ = lean_unbox(v_bi_2588_);
v_kind_boxed_2599_ = lean_unbox(v_kind_2590_);
v_res_2600_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_00_u03b1_2581_, v_acc_2582_, v_declInfos_2583_, v_k_2584_, v_kind_boxed_2597_, v_inst_2586_, v_name_2587_, v_bi_boxed_2598_, v_type_2589_, v_kind_boxed_2599_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(lean_object* v_00_u03b1_2601_, lean_object* v_declInfos_2602_, lean_object* v_k_2603_, uint8_t v_kind_2604_, lean_object* v_inst_2605_, lean_object* v_acc_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___redArg(v_declInfos_2602_, v_k_2603_, v_kind_2604_, v_inst_2605_, v_acc_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(lean_object* v_00_u03b1_2614_, lean_object* v_declInfos_2615_, lean_object* v_k_2616_, lean_object* v_kind_2617_, lean_object* v_inst_2618_, lean_object* v_acc_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
uint8_t v_kind_boxed_2626_; lean_object* v_res_2627_; 
v_kind_boxed_2626_ = lean_unbox(v_kind_2617_);
v_res_2627_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_00_u03b1_2614_, v_declInfos_2615_, v_k_2616_, v_kind_boxed_2626_, v_inst_2618_, v_acc_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(lean_object* v_00_u03b2_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_x_2629_, v_x_2630_, v_x_2631_, v_x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(lean_object* v_e_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v___x_2637_; 
v___x_2637_ = l_Lean_Expr_hasMVar(v_e_2634_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_e_2634_);
return v___x_2638_;
}
else
{
lean_object* v___x_2639_; lean_object* v_mctx_2640_; lean_object* v___x_2641_; lean_object* v_fst_2642_; lean_object* v_snd_2643_; lean_object* v___x_2644_; lean_object* v_cache_2645_; lean_object* v_zetaDeltaFVarIds_2646_; lean_object* v_postponed_2647_; lean_object* v_diag_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2657_; 
v___x_2639_ = lean_st_ref_get(v___y_2635_);
v_mctx_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc_ref(v_mctx_2640_);
lean_dec(v___x_2639_);
v___x_2641_ = l_Lean_instantiateMVarsCore(v_mctx_2640_, v_e_2634_);
v_fst_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_fst_2642_);
v_snd_2643_ = lean_ctor_get(v___x_2641_, 1);
lean_inc(v_snd_2643_);
lean_dec_ref(v___x_2641_);
v___x_2644_ = lean_st_ref_take(v___y_2635_);
v_cache_2645_ = lean_ctor_get(v___x_2644_, 1);
v_zetaDeltaFVarIds_2646_ = lean_ctor_get(v___x_2644_, 2);
v_postponed_2647_ = lean_ctor_get(v___x_2644_, 3);
v_diag_2648_ = lean_ctor_get(v___x_2644_, 4);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v___x_2644_, 0);
lean_dec(v_unused_2658_);
v___x_2650_ = v___x_2644_;
v_isShared_2651_ = v_isSharedCheck_2657_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_diag_2648_);
lean_inc(v_postponed_2647_);
lean_inc(v_zetaDeltaFVarIds_2646_);
lean_inc(v_cache_2645_);
lean_dec(v___x_2644_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2657_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v_snd_2643_);
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_snd_2643_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_cache_2645_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_zetaDeltaFVarIds_2646_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_postponed_2647_);
lean_ctor_set(v_reuseFailAlloc_2656_, 4, v_diag_2648_);
v___x_2653_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_st_ref_set(v___y_2635_, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v_fst_2642_);
return v___x_2655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(lean_object* v_e_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_2659_, v___y_2660_);
lean_dec(v___y_2660_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2(lean_object* v_e_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_2663_, v___y_2666_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___boxed(lean_object* v_e_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2(v_e_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
return v_res_2678_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(lean_object* v_m_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_buckets_2681_; lean_object* v___x_2682_; uint64_t v___x_2683_; uint64_t v___x_2684_; uint64_t v___x_2685_; uint64_t v_fold_2686_; uint64_t v___x_2687_; uint64_t v___x_2688_; uint64_t v___x_2689_; size_t v___x_2690_; size_t v___x_2691_; size_t v___x_2692_; size_t v___x_2693_; size_t v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v_buckets_2681_ = lean_ctor_get(v_m_2679_, 1);
v___x_2682_ = lean_array_get_size(v_buckets_2681_);
v___x_2683_ = l_Lean_Expr_hash(v_a_2680_);
v___x_2684_ = 32ULL;
v___x_2685_ = lean_uint64_shift_right(v___x_2683_, v___x_2684_);
v_fold_2686_ = lean_uint64_xor(v___x_2683_, v___x_2685_);
v___x_2687_ = 16ULL;
v___x_2688_ = lean_uint64_shift_right(v_fold_2686_, v___x_2687_);
v___x_2689_ = lean_uint64_xor(v_fold_2686_, v___x_2688_);
v___x_2690_ = lean_uint64_to_usize(v___x_2689_);
v___x_2691_ = lean_usize_of_nat(v___x_2682_);
v___x_2692_ = ((size_t)1ULL);
v___x_2693_ = lean_usize_sub(v___x_2691_, v___x_2692_);
v___x_2694_ = lean_usize_land(v___x_2690_, v___x_2693_);
v___x_2695_ = lean_array_uget_borrowed(v_buckets_2681_, v___x_2694_);
v___x_2696_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2680_, v___x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg___boxed(lean_object* v_m_2697_, lean_object* v_a_2698_){
_start:
{
uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_res_2699_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_2697_, v_a_2698_);
lean_dec_ref(v_a_2698_);
lean_dec_ref(v_m_2697_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(lean_object* v_m_2701_, lean_object* v_a_2702_, lean_object* v_b_2703_){
_start:
{
lean_object* v_size_2704_; lean_object* v_buckets_2705_; lean_object* v___x_2706_; uint64_t v___x_2707_; uint64_t v___x_2708_; uint64_t v___x_2709_; uint64_t v_fold_2710_; uint64_t v___x_2711_; uint64_t v___x_2712_; uint64_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; lean_object* v_bkt_2719_; uint8_t v___x_2720_; 
v_size_2704_ = lean_ctor_get(v_m_2701_, 0);
v_buckets_2705_ = lean_ctor_get(v_m_2701_, 1);
v___x_2706_ = lean_array_get_size(v_buckets_2705_);
v___x_2707_ = l_Lean_Expr_hash(v_a_2702_);
v___x_2708_ = 32ULL;
v___x_2709_ = lean_uint64_shift_right(v___x_2707_, v___x_2708_);
v_fold_2710_ = lean_uint64_xor(v___x_2707_, v___x_2709_);
v___x_2711_ = 16ULL;
v___x_2712_ = lean_uint64_shift_right(v_fold_2710_, v___x_2711_);
v___x_2713_ = lean_uint64_xor(v_fold_2710_, v___x_2712_);
v___x_2714_ = lean_uint64_to_usize(v___x_2713_);
v___x_2715_ = lean_usize_of_nat(v___x_2706_);
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_sub(v___x_2715_, v___x_2716_);
v___x_2718_ = lean_usize_land(v___x_2714_, v___x_2717_);
v_bkt_2719_ = lean_array_uget_borrowed(v_buckets_2705_, v___x_2718_);
v___x_2720_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_2702_, v_bkt_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2741_; 
lean_inc_ref(v_buckets_2705_);
lean_inc(v_size_2704_);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_m_2701_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; lean_object* v_unused_2743_; 
v_unused_2742_ = lean_ctor_get(v_m_2701_, 1);
lean_dec(v_unused_2742_);
v_unused_2743_ = lean_ctor_get(v_m_2701_, 0);
lean_dec(v_unused_2743_);
v___x_2722_ = v_m_2701_;
v_isShared_2723_ = v_isSharedCheck_2741_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v_m_2701_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2741_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v_size_x27_2725_; lean_object* v___x_2726_; lean_object* v_buckets_x27_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2724_ = lean_unsigned_to_nat(1u);
v_size_x27_2725_ = lean_nat_add(v_size_2704_, v___x_2724_);
lean_dec(v_size_2704_);
lean_inc(v_bkt_2719_);
v___x_2726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2726_, 0, v_a_2702_);
lean_ctor_set(v___x_2726_, 1, v_b_2703_);
lean_ctor_set(v___x_2726_, 2, v_bkt_2719_);
v_buckets_x27_2727_ = lean_array_uset(v_buckets_2705_, v___x_2718_, v___x_2726_);
v___x_2728_ = lean_unsigned_to_nat(4u);
v___x_2729_ = lean_nat_mul(v_size_x27_2725_, v___x_2728_);
v___x_2730_ = lean_unsigned_to_nat(3u);
v___x_2731_ = lean_nat_div(v___x_2729_, v___x_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_array_get_size(v_buckets_x27_2727_);
v___x_2733_ = lean_nat_dec_le(v___x_2731_, v___x_2732_);
lean_dec(v___x_2731_);
if (v___x_2733_ == 0)
{
lean_object* v_val_2734_; lean_object* v___x_2736_; 
v_val_2734_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_2727_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 1, v_val_2734_);
lean_ctor_set(v___x_2722_, 0, v_size_x27_2725_);
v___x_2736_ = v___x_2722_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_size_x27_2725_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_val_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
else
{
lean_object* v___x_2739_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 1, v_buckets_x27_2727_);
lean_ctor_set(v___x_2722_, 0, v_size_x27_2725_);
v___x_2739_ = v___x_2722_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_size_x27_2725_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_buckets_x27_2727_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_dec(v_b_2703_);
lean_dec_ref(v_a_2702_);
return v_m_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(lean_object* v_e_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v_checked_2748_; uint8_t v___x_2749_; 
v___x_2747_ = lean_st_ref_get(v_a_2745_);
v_checked_2748_ = lean_ctor_get(v___x_2747_, 1);
lean_inc_ref(v_checked_2748_);
lean_dec(v___x_2747_);
v___x_2749_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_checked_2748_, v_e_2744_);
lean_dec_ref(v_checked_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v_visited_2751_; lean_object* v_checked_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2764_; 
v___x_2750_ = lean_st_ref_take(v_a_2745_);
v_visited_2751_ = lean_ctor_get(v___x_2750_, 0);
v_checked_2752_ = lean_ctor_get(v___x_2750_, 1);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2754_ = v___x_2750_;
v_isShared_2755_ = v_isSharedCheck_2764_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_checked_2752_);
lean_inc(v_visited_2751_);
lean_dec(v___x_2750_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2764_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2756_ = lean_box(0);
v___x_2757_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_checked_2752_, v_e_2744_, v___x_2756_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 1, v___x_2757_);
v___x_2759_ = v___x_2754_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_visited_2751_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = lean_st_ref_set(v_a_2745_, v___x_2759_);
v___x_2761_ = lean_box(v___x_2749_);
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
return v___x_2762_;
}
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec_ref(v_e_2744_);
v___x_2765_ = lean_box(v___x_2749_);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
return v___x_2766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_e_2767_, lean_object* v_a_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_2767_, v_a_2768_);
lean_dec(v_a_2768_);
return v_res_2770_;
}
}
static size_t _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
size_t v___x_2771_; size_t v___x_2772_; size_t v___x_2773_; 
v___x_2771_ = ((size_t)1ULL);
v___x_2772_ = ((size_t)8192ULL);
v___x_2773_ = lean_usize_sub(v___x_2772_, v___x_2771_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(lean_object* v_e_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v___x_2777_; lean_object* v_visited_2778_; size_t v___x_2779_; size_t v___x_2780_; size_t v___x_2781_; lean_object* v___x_2782_; size_t v___x_2783_; uint8_t v___x_2784_; 
v___x_2777_ = lean_st_ref_get(v_a_2775_);
v_visited_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_visited_2778_);
lean_dec(v___x_2777_);
v___x_2779_ = lean_ptr_addr(v_e_2774_);
v___x_2780_ = lean_usize_once(&l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_2781_ = lean_usize_mod(v___x_2779_, v___x_2780_);
v___x_2782_ = lean_array_uget(v_visited_2778_, v___x_2781_);
lean_dec_ref(v_visited_2778_);
v___x_2783_ = lean_ptr_addr(v___x_2782_);
lean_dec(v___x_2782_);
v___x_2784_ = lean_usize_dec_eq(v___x_2783_, v___x_2779_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v_visited_2786_; lean_object* v_checked_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2798_; 
v___x_2785_ = lean_st_ref_take(v_a_2775_);
v_visited_2786_ = lean_ctor_get(v___x_2785_, 0);
v_checked_2787_ = lean_ctor_get(v___x_2785_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2789_ = v___x_2785_;
v_isShared_2790_ = v_isSharedCheck_2798_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_checked_2787_);
lean_inc(v_visited_2786_);
lean_dec(v___x_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2798_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2791_ = lean_array_uset(v_visited_2786_, v___x_2781_, v_e_2774_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v___x_2791_);
v___x_2793_ = v___x_2789_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_checked_2787_);
v___x_2793_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2794_ = lean_st_ref_set(v_a_2775_, v___x_2793_);
v___x_2795_ = lean_box(v___x_2784_);
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
return v___x_2796_;
}
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec_ref(v_e_2774_);
v___x_2799_ = lean_box(v___x_2784_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_e_2801_, lean_object* v_a_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_2801_, v_a_2802_);
lean_dec(v_a_2802_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(lean_object* v_p_2805_, lean_object* v_f_2806_, uint8_t v_stopWhenVisited_2807_, lean_object* v_e_2808_, lean_object* v_a_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v_d_2822_; lean_object* v_b_2823_; lean_object* v___y_2824_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___x_2854_; 
lean_inc_ref(v_e_2808_);
v___x_2854_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_2808_, v_a_2809_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2887_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2887_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2887_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
uint8_t v___x_2859_; 
v___x_2859_ = lean_unbox(v_a_2855_);
lean_dec(v_a_2855_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; uint8_t v___x_2861_; 
lean_del_object(v___x_2857_);
lean_inc_ref(v_p_2805_);
lean_inc_ref(v_e_2808_);
v___x_2860_ = lean_apply_1(v_p_2805_, v_e_2808_);
v___x_2861_ = lean_unbox(v___x_2860_);
if (v___x_2861_ == 0)
{
v___y_2828_ = v_a_2809_;
v___y_2829_ = v___y_2810_;
v___y_2830_ = v___y_2811_;
v___y_2831_ = v___y_2812_;
v___y_2832_ = v___y_2813_;
v___y_2833_ = v___y_2814_;
goto v___jp_2827_;
}
else
{
lean_object* v___x_2862_; 
lean_inc_ref(v_e_2808_);
v___x_2862_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_2808_, v_a_2809_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; uint8_t v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2862_);
v___x_2864_ = lean_unbox(v_a_2863_);
lean_dec(v_a_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; 
lean_inc_ref(v_f_2806_);
lean_inc(v___y_2814_);
lean_inc_ref(v___y_2813_);
lean_inc(v___y_2812_);
lean_inc_ref(v___y_2811_);
lean_inc(v___y_2810_);
lean_inc_ref(v_e_2808_);
v___x_2865_ = lean_apply_7(v_f_2806_, v_e_2808_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, lean_box(0));
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2873_; 
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v___x_2865_, 0);
lean_dec(v_unused_2874_);
v___x_2867_ = v___x_2865_;
v_isShared_2868_ = v_isSharedCheck_2873_;
goto v_resetjp_2866_;
}
else
{
lean_dec(v___x_2865_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2873_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
if (v_stopWhenVisited_2807_ == 0)
{
lean_del_object(v___x_2867_);
v___y_2828_ = v_a_2809_;
v___y_2829_ = v___y_2810_;
v___y_2830_ = v___y_2811_;
v___y_2831_ = v___y_2812_;
v___y_2832_ = v___y_2813_;
v___y_2833_ = v___y_2814_;
goto v___jp_2827_;
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2871_; 
lean_dec_ref(v_e_2808_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
v___x_2869_ = lean_box(0);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2869_);
v___x_2871_ = v___x_2867_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_dec_ref(v_e_2808_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
return v___x_2865_;
}
}
else
{
v___y_2828_ = v_a_2809_;
v___y_2829_ = v___y_2810_;
v___y_2830_ = v___y_2811_;
v___y_2831_ = v___y_2812_;
v___y_2832_ = v___y_2813_;
v___y_2833_ = v___y_2814_;
goto v___jp_2827_;
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec_ref(v_e_2808_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
v_a_2875_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2862_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2862_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_dec_ref(v_e_2808_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
v___x_2883_ = lean_box(0);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2883_);
v___x_2885_ = v___x_2857_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v_e_2808_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
v_a_2888_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2854_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2854_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
v___jp_2816_:
{
lean_object* v___x_2825_; 
lean_inc_ref(v_f_2806_);
lean_inc_ref(v_p_2805_);
v___x_2825_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2805_, v_f_2806_, v_stopWhenVisited_2807_, v_d_2822_, v___y_2824_, v___y_2817_, v___y_2820_, v___y_2819_, v___y_2821_, v___y_2818_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_dec_ref(v___x_2825_);
v_e_2808_ = v_b_2823_;
v_a_2809_ = v___y_2824_;
v___y_2810_ = v___y_2817_;
v___y_2811_ = v___y_2820_;
v___y_2812_ = v___y_2819_;
v___y_2813_ = v___y_2821_;
v___y_2814_ = v___y_2818_;
goto _start;
}
else
{
lean_dec_ref(v_b_2823_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
return v___x_2825_;
}
}
v___jp_2827_:
{
switch(lean_obj_tag(v_e_2808_))
{
case 7:
{
lean_object* v_binderType_2834_; lean_object* v_body_2835_; 
v_binderType_2834_ = lean_ctor_get(v_e_2808_, 1);
lean_inc_ref(v_binderType_2834_);
v_body_2835_ = lean_ctor_get(v_e_2808_, 2);
lean_inc_ref(v_body_2835_);
lean_dec_ref(v_e_2808_);
v___y_2817_ = v___y_2829_;
v___y_2818_ = v___y_2833_;
v___y_2819_ = v___y_2831_;
v___y_2820_ = v___y_2830_;
v___y_2821_ = v___y_2832_;
v_d_2822_ = v_binderType_2834_;
v_b_2823_ = v_body_2835_;
v___y_2824_ = v___y_2828_;
goto v___jp_2816_;
}
case 6:
{
lean_object* v_binderType_2836_; lean_object* v_body_2837_; 
v_binderType_2836_ = lean_ctor_get(v_e_2808_, 1);
lean_inc_ref(v_binderType_2836_);
v_body_2837_ = lean_ctor_get(v_e_2808_, 2);
lean_inc_ref(v_body_2837_);
lean_dec_ref(v_e_2808_);
v___y_2817_ = v___y_2829_;
v___y_2818_ = v___y_2833_;
v___y_2819_ = v___y_2831_;
v___y_2820_ = v___y_2830_;
v___y_2821_ = v___y_2832_;
v_d_2822_ = v_binderType_2836_;
v_b_2823_ = v_body_2837_;
v___y_2824_ = v___y_2828_;
goto v___jp_2816_;
}
case 8:
{
lean_object* v_type_2838_; lean_object* v_value_2839_; lean_object* v_body_2840_; lean_object* v___x_2841_; 
v_type_2838_ = lean_ctor_get(v_e_2808_, 1);
lean_inc_ref(v_type_2838_);
v_value_2839_ = lean_ctor_get(v_e_2808_, 2);
lean_inc_ref(v_value_2839_);
v_body_2840_ = lean_ctor_get(v_e_2808_, 3);
lean_inc_ref(v_body_2840_);
lean_dec_ref(v_e_2808_);
lean_inc_ref(v_f_2806_);
lean_inc_ref(v_p_2805_);
v___x_2841_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2805_, v_f_2806_, v_stopWhenVisited_2807_, v_type_2838_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2842_; 
lean_dec_ref(v___x_2841_);
lean_inc_ref(v_f_2806_);
lean_inc_ref(v_p_2805_);
v___x_2842_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2805_, v_f_2806_, v_stopWhenVisited_2807_, v_value_2839_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_dec_ref(v___x_2842_);
v_e_2808_ = v_body_2840_;
v_a_2809_ = v___y_2828_;
v___y_2810_ = v___y_2829_;
v___y_2811_ = v___y_2830_;
v___y_2812_ = v___y_2831_;
v___y_2813_ = v___y_2832_;
v___y_2814_ = v___y_2833_;
goto _start;
}
else
{
lean_dec_ref(v_body_2840_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
return v___x_2842_;
}
}
else
{
lean_dec_ref(v_body_2840_);
lean_dec_ref(v_value_2839_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
return v___x_2841_;
}
}
case 5:
{
lean_object* v_fn_2844_; lean_object* v_arg_2845_; lean_object* v___x_2846_; 
v_fn_2844_ = lean_ctor_get(v_e_2808_, 0);
lean_inc_ref(v_fn_2844_);
v_arg_2845_ = lean_ctor_get(v_e_2808_, 1);
lean_inc_ref(v_arg_2845_);
lean_dec_ref(v_e_2808_);
lean_inc_ref(v_f_2806_);
lean_inc_ref(v_p_2805_);
v___x_2846_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2805_, v_f_2806_, v_stopWhenVisited_2807_, v_fn_2844_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_dec_ref(v___x_2846_);
v_e_2808_ = v_arg_2845_;
v_a_2809_ = v___y_2828_;
v___y_2810_ = v___y_2829_;
v___y_2811_ = v___y_2830_;
v___y_2812_ = v___y_2831_;
v___y_2813_ = v___y_2832_;
v___y_2814_ = v___y_2833_;
goto _start;
}
else
{
lean_dec_ref(v_arg_2845_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
return v___x_2846_;
}
}
case 10:
{
lean_object* v_expr_2848_; 
v_expr_2848_ = lean_ctor_get(v_e_2808_, 1);
lean_inc_ref(v_expr_2848_);
lean_dec_ref(v_e_2808_);
v_e_2808_ = v_expr_2848_;
v_a_2809_ = v___y_2828_;
v___y_2810_ = v___y_2829_;
v___y_2811_ = v___y_2830_;
v___y_2812_ = v___y_2831_;
v___y_2813_ = v___y_2832_;
v___y_2814_ = v___y_2833_;
goto _start;
}
case 11:
{
lean_object* v_struct_2850_; 
v_struct_2850_ = lean_ctor_get(v_e_2808_, 2);
lean_inc_ref(v_struct_2850_);
lean_dec_ref(v_e_2808_);
v_e_2808_ = v_struct_2850_;
v_a_2809_ = v___y_2828_;
v___y_2810_ = v___y_2829_;
v___y_2811_ = v___y_2830_;
v___y_2812_ = v___y_2831_;
v___y_2813_ = v___y_2832_;
v___y_2814_ = v___y_2833_;
goto _start;
}
default: 
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v_e_2808_);
lean_dec_ref(v_f_2806_);
lean_dec_ref(v_p_2805_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5___boxed(lean_object* v_p_2896_, lean_object* v_f_2897_, lean_object* v_stopWhenVisited_2898_, lean_object* v_e_2899_, lean_object* v_a_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2907_; lean_object* v_res_2908_; 
v_stopWhenVisited_boxed_2907_ = lean_unbox(v_stopWhenVisited_2898_);
v_res_2908_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2896_, v_f_2897_, v_stopWhenVisited_boxed_2907_, v_e_2899_, v_a_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec(v_a_2900_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(lean_object* v_p_2909_, lean_object* v_f_2910_, lean_object* v_e_2911_, uint8_t v_stopWhenVisited_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = l_Lean_ForEachExprWhere_initCache;
v___x_2920_ = lean_st_mk_ref(v___x_2919_);
v___x_2921_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_2909_, v_f_2910_, v_stopWhenVisited_2912_, v_e_2911_, v___x_2920_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2930_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2924_ = v___x_2921_;
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = lean_st_ref_get(v___x_2920_);
lean_dec(v___x_2920_);
lean_dec(v___x_2926_);
if (v_isShared_2925_ == 0)
{
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2922_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
else
{
lean_dec(v___x_2920_);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3___boxed(lean_object* v_p_2931_, lean_object* v_f_2932_, lean_object* v_e_2933_, lean_object* v_stopWhenVisited_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
uint8_t v_stopWhenVisited_boxed_2941_; lean_object* v_res_2942_; 
v_stopWhenVisited_boxed_2941_ = lean_unbox(v_stopWhenVisited_2934_);
v_res_2942_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(v_p_2931_, v_f_2932_, v_e_2933_, v_stopWhenVisited_boxed_2941_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
return v_res_2942_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(lean_object* v_a_2943_, lean_object* v_x_2944_){
_start:
{
if (lean_obj_tag(v_x_2944_) == 0)
{
uint8_t v___x_2945_; 
v___x_2945_ = 0;
return v___x_2945_;
}
else
{
lean_object* v_key_2946_; lean_object* v_tail_2947_; uint8_t v___x_2948_; 
v_key_2946_ = lean_ctor_get(v_x_2944_, 0);
v_tail_2947_ = lean_ctor_get(v_x_2944_, 2);
v___x_2948_ = l_Lean_instBEqFVarId_beq(v_key_2946_, v_a_2943_);
if (v___x_2948_ == 0)
{
v_x_2944_ = v_tail_2947_;
goto _start;
}
else
{
return v___x_2948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg___boxed(lean_object* v_a_2950_, lean_object* v_x_2951_){
_start:
{
uint8_t v_res_2952_; lean_object* v_r_2953_; 
v_res_2952_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_2950_, v_x_2951_);
lean_dec(v_x_2951_);
lean_dec(v_a_2950_);
v_r_2953_ = lean_box(v_res_2952_);
return v_r_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
if (lean_obj_tag(v_x_2955_) == 0)
{
return v_x_2954_;
}
else
{
lean_object* v_key_2956_; lean_object* v_value_2957_; lean_object* v_tail_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2981_; 
v_key_2956_ = lean_ctor_get(v_x_2955_, 0);
v_value_2957_ = lean_ctor_get(v_x_2955_, 1);
v_tail_2958_ = lean_ctor_get(v_x_2955_, 2);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_x_2955_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2960_ = v_x_2955_;
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_tail_2958_);
lean_inc(v_value_2957_);
lean_inc(v_key_2956_);
lean_dec(v_x_2955_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; uint64_t v___x_2963_; uint64_t v___x_2964_; uint64_t v___x_2965_; uint64_t v_fold_2966_; uint64_t v___x_2967_; uint64_t v___x_2968_; uint64_t v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2962_ = lean_array_get_size(v_x_2954_);
v___x_2963_ = l_Lean_instHashableFVarId_hash(v_key_2956_);
v___x_2964_ = 32ULL;
v___x_2965_ = lean_uint64_shift_right(v___x_2963_, v___x_2964_);
v_fold_2966_ = lean_uint64_xor(v___x_2963_, v___x_2965_);
v___x_2967_ = 16ULL;
v___x_2968_ = lean_uint64_shift_right(v_fold_2966_, v___x_2967_);
v___x_2969_ = lean_uint64_xor(v_fold_2966_, v___x_2968_);
v___x_2970_ = lean_uint64_to_usize(v___x_2969_);
v___x_2971_ = lean_usize_of_nat(v___x_2962_);
v___x_2972_ = ((size_t)1ULL);
v___x_2973_ = lean_usize_sub(v___x_2971_, v___x_2972_);
v___x_2974_ = lean_usize_land(v___x_2970_, v___x_2973_);
v___x_2975_ = lean_array_uget_borrowed(v_x_2954_, v___x_2974_);
lean_inc(v___x_2975_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 2, v___x_2975_);
v___x_2977_ = v___x_2960_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_key_2956_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_value_2957_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_array_uset(v_x_2954_, v___x_2974_, v___x_2977_);
v_x_2954_ = v___x_2978_;
v_x_2955_ = v_tail_2958_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(lean_object* v_i_2982_, lean_object* v_source_2983_, lean_object* v_target_2984_){
_start:
{
lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = lean_array_get_size(v_source_2983_);
v___x_2986_ = lean_nat_dec_lt(v_i_2982_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_dec_ref(v_source_2983_);
lean_dec(v_i_2982_);
return v_target_2984_;
}
else
{
lean_object* v_es_2987_; lean_object* v___x_2988_; lean_object* v_source_2989_; lean_object* v_target_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_es_2987_ = lean_array_fget(v_source_2983_, v_i_2982_);
v___x_2988_ = lean_box(0);
v_source_2989_ = lean_array_fset(v_source_2983_, v_i_2982_, v___x_2988_);
v_target_2990_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_target_2984_, v_es_2987_);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_i_2982_, v___x_2991_);
lean_dec(v_i_2982_);
v_i_2982_ = v___x_2992_;
v_source_2983_ = v_source_2989_;
v_target_2984_ = v_target_2990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(lean_object* v_data_2994_){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v_nbuckets_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2995_ = lean_array_get_size(v_data_2994_);
v___x_2996_ = lean_unsigned_to_nat(2u);
v_nbuckets_2997_ = lean_nat_mul(v___x_2995_, v___x_2996_);
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_2999_ = lean_box(0);
v___x_3000_ = lean_mk_array(v_nbuckets_2997_, v___x_2999_);
v___x_3001_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v___x_2998_, v_data_2994_, v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(lean_object* v_m_3002_, lean_object* v_a_3003_, lean_object* v_b_3004_){
_start:
{
lean_object* v_size_3005_; lean_object* v_buckets_3006_; lean_object* v___x_3007_; uint64_t v___x_3008_; uint64_t v___x_3009_; uint64_t v___x_3010_; uint64_t v_fold_3011_; uint64_t v___x_3012_; uint64_t v___x_3013_; uint64_t v___x_3014_; size_t v___x_3015_; size_t v___x_3016_; size_t v___x_3017_; size_t v___x_3018_; size_t v___x_3019_; lean_object* v_bkt_3020_; uint8_t v___x_3021_; 
v_size_3005_ = lean_ctor_get(v_m_3002_, 0);
v_buckets_3006_ = lean_ctor_get(v_m_3002_, 1);
v___x_3007_ = lean_array_get_size(v_buckets_3006_);
v___x_3008_ = l_Lean_instHashableFVarId_hash(v_a_3003_);
v___x_3009_ = 32ULL;
v___x_3010_ = lean_uint64_shift_right(v___x_3008_, v___x_3009_);
v_fold_3011_ = lean_uint64_xor(v___x_3008_, v___x_3010_);
v___x_3012_ = 16ULL;
v___x_3013_ = lean_uint64_shift_right(v_fold_3011_, v___x_3012_);
v___x_3014_ = lean_uint64_xor(v_fold_3011_, v___x_3013_);
v___x_3015_ = lean_uint64_to_usize(v___x_3014_);
v___x_3016_ = lean_usize_of_nat(v___x_3007_);
v___x_3017_ = ((size_t)1ULL);
v___x_3018_ = lean_usize_sub(v___x_3016_, v___x_3017_);
v___x_3019_ = lean_usize_land(v___x_3015_, v___x_3018_);
v_bkt_3020_ = lean_array_uget_borrowed(v_buckets_3006_, v___x_3019_);
v___x_3021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_3003_, v_bkt_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3042_; 
lean_inc_ref(v_buckets_3006_);
lean_inc(v_size_3005_);
v_isSharedCheck_3042_ = !lean_is_exclusive(v_m_3002_);
if (v_isSharedCheck_3042_ == 0)
{
lean_object* v_unused_3043_; lean_object* v_unused_3044_; 
v_unused_3043_ = lean_ctor_get(v_m_3002_, 1);
lean_dec(v_unused_3043_);
v_unused_3044_ = lean_ctor_get(v_m_3002_, 0);
lean_dec(v_unused_3044_);
v___x_3023_ = v_m_3002_;
v_isShared_3024_ = v_isSharedCheck_3042_;
goto v_resetjp_3022_;
}
else
{
lean_dec(v_m_3002_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3042_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; lean_object* v_size_x27_3026_; lean_object* v___x_3027_; lean_object* v_buckets_x27_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3025_ = lean_unsigned_to_nat(1u);
v_size_x27_3026_ = lean_nat_add(v_size_3005_, v___x_3025_);
lean_dec(v_size_3005_);
lean_inc(v_bkt_3020_);
v___x_3027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3027_, 0, v_a_3003_);
lean_ctor_set(v___x_3027_, 1, v_b_3004_);
lean_ctor_set(v___x_3027_, 2, v_bkt_3020_);
v_buckets_x27_3028_ = lean_array_uset(v_buckets_3006_, v___x_3019_, v___x_3027_);
v___x_3029_ = lean_unsigned_to_nat(4u);
v___x_3030_ = lean_nat_mul(v_size_x27_3026_, v___x_3029_);
v___x_3031_ = lean_unsigned_to_nat(3u);
v___x_3032_ = lean_nat_div(v___x_3030_, v___x_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_array_get_size(v_buckets_x27_3028_);
v___x_3034_ = lean_nat_dec_le(v___x_3032_, v___x_3033_);
lean_dec(v___x_3032_);
if (v___x_3034_ == 0)
{
lean_object* v_val_3035_; lean_object* v___x_3037_; 
v_val_3035_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_buckets_x27_3028_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v_val_3035_);
lean_ctor_set(v___x_3023_, 0, v_size_x27_3026_);
v___x_3037_ = v___x_3023_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_size_x27_3026_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_val_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
else
{
lean_object* v___x_3040_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v_buckets_x27_3028_);
lean_ctor_set(v___x_3023_, 0, v_size_x27_3026_);
v___x_3040_ = v___x_3023_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_size_x27_3026_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_buckets_x27_3028_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_dec(v_b_3004_);
lean_dec(v_a_3003_);
return v_m_3002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(lean_object* v___x_3045_, lean_object* v_a_3046_, lean_object* v_e_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3054_; lean_object* v_relevantTerms_3055_; lean_object* v_relevantHyps_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3078_; 
v___x_3054_ = lean_st_ref_take(v___y_3048_);
v_relevantTerms_3055_ = lean_ctor_get(v___x_3054_, 0);
v_relevantHyps_3056_ = lean_ctor_get(v___x_3054_, 1);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3058_ = v___x_3054_;
v_isShared_3059_ = v_isSharedCheck_3078_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_relevantHyps_3056_);
lean_inc(v_relevantTerms_3055_);
lean_dec(v___x_3054_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3078_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_relevantTerms_3055_, v_e_3047_, v___x_3045_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_relevantHyps_3056_);
v___x_3062_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v_relevantTerms_3065_; lean_object* v_relevantHyps_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3076_; 
v___x_3063_ = lean_st_ref_set(v___y_3048_, v___x_3062_);
v___x_3064_ = lean_st_ref_take(v___y_3048_);
v_relevantTerms_3065_ = lean_ctor_get(v___x_3064_, 0);
v_relevantHyps_3066_ = lean_ctor_get(v___x_3064_, 1);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3068_ = v___x_3064_;
v_isShared_3069_ = v_isSharedCheck_3076_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_relevantHyps_3066_);
lean_inc(v_relevantTerms_3065_);
lean_dec(v___x_3064_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3076_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3070_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_relevantHyps_3066_, v_a_3046_, v___x_3045_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 1, v___x_3070_);
v___x_3072_ = v___x_3068_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_relevantTerms_3065_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_st_ref_set(v___y_3048_, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3045_);
return v___x_3074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(lean_object* v___x_3079_, lean_object* v_a_3080_, lean_object* v_e_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(v___x_3079_, v_a_3080_, v_e_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
return v_res_3088_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(lean_object* v_e_3098_){
_start:
{
uint8_t v___y_3100_; lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2));
v___x_3104_ = lean_unsigned_to_nat(1u);
v___x_3105_ = l_Lean_Expr_isAppOfArity(v_e_3098_, v___x_3103_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4));
v___x_3107_ = l_Lean_Expr_isAppOfArity(v_e_3098_, v___x_3106_, v___x_3104_);
v___y_3100_ = v___x_3107_;
goto v___jp_3099_;
}
else
{
v___y_3100_ = v___x_3105_;
goto v___jp_3099_;
}
v___jp_3099_:
{
if (v___y_3100_ == 0)
{
return v___y_3100_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = l_Lean_Expr_hasLooseBVars(v_e_3098_);
if (v___x_3101_ == 0)
{
return v___y_3100_;
}
else
{
uint8_t v___x_3102_; 
v___x_3102_ = 0;
return v___x_3102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed(lean_object* v_e_3108_){
_start:
{
uint8_t v_res_3109_; lean_object* v_r_3110_; 
v_res_3109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(v_e_3108_);
lean_dec_ref(v_e_3108_);
v_r_3110_ = lean_box(v_res_3109_);
return v_r_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(lean_object* v_as_3112_, size_t v_sz_3113_, size_t v_i_3114_, lean_object* v_b_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_usize_dec_lt(v_i_3114_, v_sz_3113_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3123_, 0, v_b_3115_);
return v___x_3123_;
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3125_; 
v_a_3124_ = lean_array_uget_borrowed(v_as_3112_, v_i_3114_);
lean_inc(v_a_3124_);
v___x_3125_ = l_Lean_FVarId_getType___redArg(v_a_3124_, v___y_3117_, v___y_3119_, v___y_3120_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3127_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref(v___x_3125_);
v___x_3127_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_a_3126_, v___y_3118_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___f_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref(v___x_3127_);
v___f_3129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___closed__0));
v___x_3130_ = lean_box(0);
lean_inc(v_a_3124_);
v___f_3131_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed), 9, 2);
lean_closure_set(v___f_3131_, 0, v___x_3130_);
lean_closure_set(v___f_3131_, 1, v_a_3124_);
v___x_3132_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3(v___f_3129_, v___f_3131_, v_a_3128_, v___x_3122_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
if (lean_obj_tag(v___x_3132_) == 0)
{
size_t v___x_3133_; size_t v___x_3134_; 
lean_dec_ref(v___x_3132_);
v___x_3133_ = ((size_t)1ULL);
v___x_3134_ = lean_usize_add(v_i_3114_, v___x_3133_);
v_i_3114_ = v___x_3134_;
v_b_3115_ = v___x_3130_;
goto _start;
}
else
{
return v___x_3132_;
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
v_a_3136_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3127_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3127_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_a_3144_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3125_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3125_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4___boxed(lean_object* v_as_3152_, lean_object* v_sz_3153_, lean_object* v_i_3154_, lean_object* v_b_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
size_t v_sz_boxed_3162_; size_t v_i_boxed_3163_; lean_object* v_res_3164_; 
v_sz_boxed_3162_ = lean_unbox_usize(v_sz_3153_);
lean_dec(v_sz_3153_);
v_i_boxed_3163_ = lean_unbox_usize(v_i_3154_);
lean_dec(v_i_3154_);
v_res_3164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(v_as_3152_, v_sz_boxed_3162_, v_i_boxed_3163_, v_b_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v_as_3152_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0(lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_Meta_getPropHyps(v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; size_t v_sz_3174_; size_t v___x_3175_; lean_object* v___x_3176_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = lean_box(0);
v_sz_3174_ = lean_array_size(v_a_3172_);
v___x_3175_ = ((size_t)0ULL);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__4(v_a_3172_, v_sz_3174_, v___x_3175_, v___x_3173_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v_a_3172_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3195_; 
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; 
v_unused_3196_ = lean_ctor_get(v___x_3176_, 0);
lean_dec(v_unused_3196_);
v___x_3178_ = v___x_3176_;
v_isShared_3179_ = v_isSharedCheck_3195_;
goto v_resetjp_3177_;
}
else
{
lean_dec(v___x_3176_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3195_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v_relevantTerms_3181_; lean_object* v_size_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3180_ = lean_st_ref_get(v___y_3165_);
v_relevantTerms_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc_ref(v_relevantTerms_3181_);
lean_dec(v___x_3180_);
v_size_3182_ = lean_ctor_get(v_relevantTerms_3181_, 0);
lean_inc(v_size_3182_);
lean_dec_ref(v_relevantTerms_3181_);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = lean_nat_dec_eq(v_size_3182_, v___x_3183_);
lean_dec(v_size_3182_);
if (v___x_3184_ == 0)
{
uint8_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3188_; 
v___x_3185_ = 1;
v___x_3186_ = lean_box(v___x_3185_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3186_);
v___x_3188_ = v___x_3178_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3186_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
else
{
uint8_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3190_ = 0;
v___x_3191_ = lean_box(v___x_3190_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3191_);
v___x_3193_ = v___x_3178_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
v_a_3197_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3176_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3176_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
v_a_3205_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3171_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3171_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0___boxed(lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___lam__0(v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(lean_object* v_goal_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v___f_3228_; lean_object* v___x_3229_; 
v___f_3228_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___closed__0));
v___x_3229_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_3221_, v___f_3228_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize___boxed(lean_object* v_goal_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(v_goal_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0(lean_object* v_00_u03b2_3238_, lean_object* v_m_3239_, lean_object* v_a_3240_, lean_object* v_b_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_m_3239_, v_a_3240_, v_b_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1(lean_object* v_00_u03b2_3243_, lean_object* v_m_3244_, lean_object* v_a_3245_, lean_object* v_b_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_m_3244_, v_a_3245_, v_b_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(lean_object* v_00_u03b2_3248_, lean_object* v_a_3249_, lean_object* v_x_3250_){
_start:
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_3249_, v_x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(lean_object* v_00_u03b2_3252_, lean_object* v_a_3253_, lean_object* v_x_3254_){
_start:
{
uint8_t v_res_3255_; lean_object* v_r_3256_; 
v_res_3255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(v_00_u03b2_3252_, v_a_3253_, v_x_3254_);
lean_dec(v_x_3254_);
lean_dec(v_a_3253_);
v_r_3256_ = lean_box(v_res_3255_);
return v_r_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(lean_object* v_00_u03b2_3257_, lean_object* v_data_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_data_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(lean_object* v_e_3260_, lean_object* v_a_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_3260_, v_a_3261_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(lean_object* v_e_3269_, lean_object* v_a_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(v_e_3269_, v_a_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v_a_3270_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3278_, lean_object* v_i_3279_, lean_object* v_source_3280_, lean_object* v_target_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v_i_3279_, v_source_3280_, v_target_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(lean_object* v_e_3283_, lean_object* v_a_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_3283_, v_a_3284_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(lean_object* v_e_3292_, lean_object* v_a_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(v_e_3292_, v_a_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v_a_3293_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_3301_, lean_object* v_x_3302_, lean_object* v_x_3303_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_x_3302_, v_x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(lean_object* v_00_u03b2_3305_, lean_object* v_m_3306_, lean_object* v_a_3307_){
_start:
{
uint8_t v___x_3308_; 
v___x_3308_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_3306_, v_a_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(lean_object* v_00_u03b2_3309_, lean_object* v_m_3310_, lean_object* v_a_3311_){
_start:
{
uint8_t v_res_3312_; lean_object* v_r_3313_; 
v_res_3312_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_3309_, v_m_3310_, v_a_3311_);
lean_dec_ref(v_a_3311_);
lean_dec_ref(v_m_3310_);
v_r_3313_ = lean_box(v_res_3312_);
return v_r_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(lean_object* v_goal_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3321_; 
lean_inc(v_goal_3314_);
v___x_3321_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_detectSize(v_goal_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3331_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3331_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3331_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
uint8_t v___x_3326_; 
v___x_3326_ = lean_unbox(v_a_3322_);
lean_dec(v_a_3322_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3328_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v_goal_3314_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_goal_3314_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
else
{
lean_object* v___x_3330_; 
lean_del_object(v___x_3324_);
v___x_3330_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize(v_goal_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
return v___x_3330_;
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec(v_goal_3314_);
v_a_3332_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3321_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3321_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize___boxed(lean_object* v_goal_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(v_goal_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
return v_res_3347_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3350_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__1);
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
return v___x_3352_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v___x_3353_);
return v___x_3355_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = lean_unsigned_to_nat(32u);
v___x_3357_ = lean_mk_empty_array_with_capacity(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5(void){
_start:
{
size_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3359_ = ((size_t)5ULL);
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = lean_unsigned_to_nat(32u);
v___x_3362_ = lean_mk_empty_array_with_capacity(v___x_3361_);
v___x_3363_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__4);
v___x_3364_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___x_3362_);
lean_ctor_set(v___x_3364_, 2, v___x_3360_);
lean_ctor_set(v___x_3364_, 3, v___x_3360_);
lean_ctor_set_usize(v___x_3364_, 4, v___x_3359_);
return v___x_3364_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3365_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__5);
v___x_3366_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__2);
v___x_3367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
lean_ctor_set(v___x_3367_, 2, v___x_3366_);
lean_ctor_set(v___x_3367_, 3, v___x_3365_);
return v___x_3367_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__6);
v___x_3369_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__3);
v___x_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
lean_ctor_set(v___x_3370_, 1, v___x_3368_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
v___x_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0(lean_object* v_goal_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt;
v___x_3382_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_3381_, v___y_3379_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_3379_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v_maxSteps_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; uint8_t v___x_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v___x_3384_);
v_maxSteps_3386_ = lean_ctor_get(v___y_3374_, 1);
v___x_3387_ = lean_unsigned_to_nat(2u);
v___x_3388_ = 0;
v___x_3389_ = 1;
v___x_3390_ = 0;
v___x_3391_ = lean_box(0);
lean_inc(v_maxSteps_3386_);
v___x_3392_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3392_, 0, v_maxSteps_3386_);
lean_ctor_set(v___x_3392_, 1, v___x_3387_);
lean_ctor_set(v___x_3392_, 2, v___x_3391_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 1, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 2, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 3, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 4, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 5, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 6, v___x_3390_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 7, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 8, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 9, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 10, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 11, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 12, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 13, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 14, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 15, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 16, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 17, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 18, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 19, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 20, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 21, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 22, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 23, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 24, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 25, v___x_3389_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 26, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 27, v___x_3388_);
lean_ctor_set_uint8(v___x_3392_, sizeof(void*)*3 + 28, v___x_3389_);
v___x_3393_ = lean_unsigned_to_nat(1u);
v___x_3394_ = lean_mk_empty_array_with_capacity(v___x_3393_);
v___x_3395_ = lean_array_push(v___x_3394_, v_a_3383_);
v___x_3396_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_3392_, v___x_3395_, v_a_3385_, v___y_3376_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___x_3396_);
lean_inc(v_goal_3373_);
v___x_3398_ = l_Lean_MVarId_getNondepPropHyps(v_goal_3373_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__0));
v___x_3401_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__7);
v___x_3402_ = l_Lean_Meta_simpGoal(v_goal_3373_, v_a_3397_, v___x_3400_, v___x_3391_, v___x_3389_, v_a_3399_, v___x_3401_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3440_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3440_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3440_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v_fst_3407_; 
v_fst_3407_ = lean_ctor_get(v_a_3403_, 0);
lean_inc(v_fst_3407_);
lean_dec(v_a_3403_);
if (lean_obj_tag(v_fst_3407_) == 1)
{
lean_object* v_val_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3436_; 
lean_del_object(v___x_3405_);
v_val_3408_ = lean_ctor_get(v_fst_3407_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_fst_3407_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3410_ = v_fst_3407_;
v_isShared_3411_ = v_isSharedCheck_3436_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_val_3408_);
lean_dec(v_fst_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3436_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_snd_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v_snd_3412_ = lean_ctor_get(v_val_3408_, 1);
lean_inc(v_snd_3412_);
lean_dec(v_val_3408_);
v___x_3413_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___closed__8);
v___x_3414_ = lean_st_mk_ref(v___x_3413_);
v___x_3415_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec_0__Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass_handleSize(v_snd_3412_, v___x_3414_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3427_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3427_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3427_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3420_ = lean_st_ref_get(v___x_3414_);
lean_dec(v___x_3414_);
lean_dec(v___x_3420_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v_a_3416_);
v___x_3422_ = v___x_3410_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3416_);
v___x_3422_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3424_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3422_);
v___x_3424_ = v___x_3418_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v___x_3414_);
lean_del_object(v___x_3410_);
v_a_3428_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3415_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3415_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
else
{
lean_object* v___x_3438_; 
lean_dec(v_fst_3407_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v___x_3391_);
v___x_3438_ = v___x_3405_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3391_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
v_a_3441_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3402_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3402_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v_a_3397_);
lean_dec(v_goal_3373_);
v_a_3449_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3398_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3398_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_goal_3373_);
v_a_3457_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3396_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3396_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v_a_3383_);
lean_dec(v_goal_3373_);
v_a_3465_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3384_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3384_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec(v_goal_3373_);
v_a_3473_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3382_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3382_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0___boxed(lean_object* v_goal_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_intToBitVecPass___lam__0(v_goal_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
return v_res_3489_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_IntToBitVec(builtin);
}
#ifdef __cplusplus
}
#endif
