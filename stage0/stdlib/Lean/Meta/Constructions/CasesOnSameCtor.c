// Lean compiler output
// Module: Lean.Meta.Constructions.CasesOnSameCtor
// Imports: public import Lean.Meta.Basic import Lean.Meta.CompletionName import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Constructions.CtorElim import Lean.Elab.App import Lean.Meta.SameCtorUtils
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
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkCtorIdxName(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabAsElim;
lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Meta_markMatcherLike(lean_object*, lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object**);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object**);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object**);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 10, 150, 230, 97, 79, 179, 234)}};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object**);
static const lean_ctor_object l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Constructions.CasesOnSameCtor"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__0_value;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.mkCasesOnSameCtorHet"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__1_value;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpected universe levels on `casesOn`"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__2 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__2_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtorHet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtorHet___closed__3;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__4 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__4_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtorHet___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtorHet___closed__5;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "could not apply "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " to close\n"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unifyEqns\? unexpectedly closed goal"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object**);
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object**);
static const lean_string_object l_Lean_mkCasesOnSameCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "het"};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__0_value;
static const lean_ctor_object l_Lean_mkCasesOnSameCtor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOnSameCtor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 194, 63, 63, 137, 239, 65, 92)}};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__1_value;
static const lean_string_object l_Lean_mkCasesOnSameCtor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.mkCasesOnSameCtor"};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__2 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__2_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___closed__3;
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___f_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_27_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_27_, 0, v_k_20_);
v___x_28_ = 0;
v___x_29_ = lean_box(0);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_28_, v___x_29_, v_type_19_, v___f_27_, v_cleanupAnnotations_21_, v___x_28_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___boxed(lean_object* v_type_47_, lean_object* v_k_48_, lean_object* v_cleanupAnnotations_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; lean_object* v_res_56_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_49_);
v_res_56_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_47_, v_k_48_, v_cleanupAnnotations_boxed_55_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(lean_object* v_00_u03b1_57_, lean_object* v_type_58_, lean_object* v_k_59_, uint8_t v_cleanupAnnotations_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_58_, v_k_59_, v_cleanupAnnotations_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___boxed(lean_object* v_00_u03b1_67_, lean_object* v_type_68_, lean_object* v_k_69_, lean_object* v_cleanupAnnotations_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_76_; lean_object* v_res_77_; 
v_cleanupAnnotations_boxed_76_ = lean_unbox(v_cleanupAnnotations_70_);
v_res_77_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(v_00_u03b1_67_, v_type_68_, v_k_69_, v_cleanupAnnotations_boxed_76_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(lean_object* v_k_78_, lean_object* v_b_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
v___x_85_ = lean_apply_6(v_k_78_, v_b_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(lean_object* v_k_86_, lean_object* v_b_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(v_k_86_, v_b_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(lean_object* v_name_94_, uint8_t v_bi_95_, lean_object* v_type_96_, lean_object* v_k_97_, uint8_t v_kind_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; 
v___f_104_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_104_, 0, v_k_97_);
v___x_105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_94_, v_bi_95_, v_type_96_, v___f_104_, v_kind_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_105_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_105_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___boxed(lean_object* v_name_122_, lean_object* v_bi_123_, lean_object* v_type_124_, lean_object* v_k_125_, lean_object* v_kind_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
uint8_t v_bi_boxed_132_; uint8_t v_kind_boxed_133_; lean_object* v_res_134_; 
v_bi_boxed_132_ = lean_unbox(v_bi_123_);
v_kind_boxed_133_ = lean_unbox(v_kind_126_);
v_res_134_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_122_, v_bi_boxed_132_, v_type_124_, v_k_125_, v_kind_boxed_133_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(lean_object* v_00_u03b1_135_, lean_object* v_name_136_, uint8_t v_bi_137_, lean_object* v_type_138_, lean_object* v_k_139_, uint8_t v_kind_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_136_, v_bi_137_, v_type_138_, v_k_139_, v_kind_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___boxed(lean_object* v_00_u03b1_147_, lean_object* v_name_148_, lean_object* v_bi_149_, lean_object* v_type_150_, lean_object* v_k_151_, lean_object* v_kind_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v_bi_boxed_158_; uint8_t v_kind_boxed_159_; lean_object* v_res_160_; 
v_bi_boxed_158_ = lean_unbox(v_bi_149_);
v_kind_boxed_159_ = lean_unbox(v_kind_152_);
v_res_160_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(v_00_u03b1_147_, v_name_148_, v_bi_boxed_158_, v_type_150_, v_k_151_, v_kind_boxed_159_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(lean_object* v_type_161_, lean_object* v_maxFVars_x3f_162_, lean_object* v_k_163_, uint8_t v_cleanupAnnotations_164_, uint8_t v_whnfType_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___f_171_; lean_object* v___x_172_; 
v___f_171_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_171_, 0, v_k_163_);
v___x_172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_161_, v_maxFVars_x3f_162_, v___f_171_, v_cleanupAnnotations_164_, v_whnfType_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_172_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_172_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg___boxed(lean_object* v_type_189_, lean_object* v_maxFVars_x3f_190_, lean_object* v_k_191_, lean_object* v_cleanupAnnotations_192_, lean_object* v_whnfType_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_199_; uint8_t v_whnfType_boxed_200_; lean_object* v_res_201_; 
v_cleanupAnnotations_boxed_199_ = lean_unbox(v_cleanupAnnotations_192_);
v_whnfType_boxed_200_ = lean_unbox(v_whnfType_193_);
v_res_201_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_189_, v_maxFVars_x3f_190_, v_k_191_, v_cleanupAnnotations_boxed_199_, v_whnfType_boxed_200_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(lean_object* v_00_u03b1_202_, lean_object* v_type_203_, lean_object* v_maxFVars_x3f_204_, lean_object* v_k_205_, uint8_t v_cleanupAnnotations_206_, uint8_t v_whnfType_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_203_, v_maxFVars_x3f_204_, v_k_205_, v_cleanupAnnotations_206_, v_whnfType_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___boxed(lean_object* v_00_u03b1_214_, lean_object* v_type_215_, lean_object* v_maxFVars_x3f_216_, lean_object* v_k_217_, lean_object* v_cleanupAnnotations_218_, lean_object* v_whnfType_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_225_; uint8_t v_whnfType_boxed_226_; lean_object* v_res_227_; 
v_cleanupAnnotations_boxed_225_ = lean_unbox(v_cleanupAnnotations_218_);
v_whnfType_boxed_226_ = lean_unbox(v_whnfType_219_);
v_res_227_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(v_00_u03b1_214_, v_type_215_, v_maxFVars_x3f_216_, v_k_217_, v_cleanupAnnotations_boxed_225_, v_whnfType_boxed_226_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(lean_object* v_name_228_, lean_object* v_levelParams_229_, lean_object* v_type_230_, lean_object* v_value_231_, lean_object* v_hints_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; uint8_t v___y_237_; uint8_t v___y_244_; lean_object* v_env_247_; uint8_t v___x_248_; 
v___x_235_ = lean_st_ref_get(v___y_233_);
v_env_247_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref(v_env_247_);
lean_dec(v___x_235_);
lean_inc_ref(v_env_247_);
v___x_248_ = l_Lean_Environment_hasUnsafe(v_env_247_, v_type_230_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_Environment_hasUnsafe(v_env_247_, v_value_231_);
v___y_244_ = v___x_249_;
goto v___jp_243_;
}
else
{
lean_dec_ref(v_env_247_);
v___y_244_ = v___x_248_;
goto v___jp_243_;
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc(v_name_228_);
v___x_238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_238_, 0, v_name_228_);
lean_ctor_set(v___x_238_, 1, v_levelParams_229_);
lean_ctor_set(v___x_238_, 2, v_type_230_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v_name_228_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v_value_231_);
lean_ctor_set(v___x_241_, 2, v_hints_232_);
lean_ctor_set(v___x_241_, 3, v___x_240_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*4, v___y_237_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
v___jp_243_:
{
if (v___y_244_ == 0)
{
uint8_t v___x_245_; 
v___x_245_ = 1;
v___y_237_ = v___x_245_;
goto v___jp_236_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 0;
v___y_237_ = v___x_246_;
goto v___jp_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object* v_name_250_, lean_object* v_levelParams_251_, lean_object* v_type_252_, lean_object* v_value_253_, lean_object* v_hints_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_250_, v_levelParams_251_, v_type_252_, v_value_253_, v_hints_254_, v___y_255_);
lean_dec(v___y_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object* v_name_258_, lean_object* v_levelParams_259_, lean_object* v_type_260_, lean_object* v_value_261_, lean_object* v_hints_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_258_, v_levelParams_259_, v_type_260_, v_value_261_, v_hints_262_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object* v_name_269_, lean_object* v_levelParams_270_, lean_object* v_type_271_, lean_object* v_value_272_, lean_object* v_hints_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(v_name_269_, v_levelParams_270_, v_type_271_, v_value_272_, v_hints_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object* v___y_280_, uint8_t v_isExporting_281_, lean_object* v___x_282_, lean_object* v___y_283_, lean_object* v___x_284_, lean_object* v_a_x3f_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v_nextMacroScope_289_; lean_object* v_ngen_290_; lean_object* v_auxDeclNGen_291_; lean_object* v_traceState_292_; lean_object* v_messages_293_; lean_object* v_infoState_294_; lean_object* v_snapshotTasks_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_320_; 
v___x_287_ = lean_st_ref_take(v___y_280_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_289_ = lean_ctor_get(v___x_287_, 1);
v_ngen_290_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_291_ = lean_ctor_get(v___x_287_, 3);
v_traceState_292_ = lean_ctor_get(v___x_287_, 4);
v_messages_293_ = lean_ctor_get(v___x_287_, 6);
v_infoState_294_ = lean_ctor_get(v___x_287_, 7);
v_snapshotTasks_295_ = lean_ctor_get(v___x_287_, 8);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_287_, 5);
lean_dec(v_unused_321_);
v___x_297_ = v___x_287_;
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snapshotTasks_295_);
lean_inc(v_infoState_294_);
lean_inc(v_messages_293_);
lean_inc(v_traceState_292_);
lean_inc(v_auxDeclNGen_291_);
lean_inc(v_ngen_290_);
lean_inc(v_nextMacroScope_289_);
lean_inc(v_env_288_);
lean_dec(v___x_287_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_Environment_setExporting(v_env_288_, v_isExporting_281_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 5, v___x_282_);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_nextMacroScope_289_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_ngen_290_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_auxDeclNGen_291_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_319_, 5, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_319_, 6, v_messages_293_);
lean_ctor_set(v_reuseFailAlloc_319_, 7, v_infoState_294_);
lean_ctor_set(v_reuseFailAlloc_319_, 8, v_snapshotTasks_295_);
v___x_301_ = v_reuseFailAlloc_319_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_mctx_304_; lean_object* v_zetaDeltaFVarIds_305_; lean_object* v_postponed_306_; lean_object* v_diag_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v___x_302_ = lean_st_ref_set(v___y_280_, v___x_301_);
v___x_303_ = lean_st_ref_take(v___y_283_);
v_mctx_304_ = lean_ctor_get(v___x_303_, 0);
v_zetaDeltaFVarIds_305_ = lean_ctor_get(v___x_303_, 2);
v_postponed_306_ = lean_ctor_get(v___x_303_, 3);
v_diag_307_ = lean_ctor_get(v___x_303_, 4);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_303_, 1);
lean_dec(v_unused_318_);
v___x_309_ = v___x_303_;
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_diag_307_);
lean_inc(v_postponed_306_);
lean_inc(v_zetaDeltaFVarIds_305_);
lean_inc(v_mctx_304_);
lean_dec(v___x_303_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_284_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_mctx_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_zetaDeltaFVarIds_305_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_postponed_306_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_diag_307_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_st_ref_set(v___y_283_, v___x_312_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_322_, lean_object* v_isExporting_323_, lean_object* v___x_324_, lean_object* v___y_325_, lean_object* v___x_326_, lean_object* v_a_x3f_327_, lean_object* v___y_328_){
_start:
{
uint8_t v_isExporting_boxed_329_; lean_object* v_res_330_; 
v_isExporting_boxed_329_ = lean_unbox(v_isExporting_323_);
v_res_330_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_322_, v_isExporting_boxed_329_, v___x_324_, v___y_325_, v___x_326_, v_a_x3f_327_);
lean_dec(v_a_x3f_327_);
lean_dec(v___y_325_);
lean_dec(v___y_322_);
return v_res_330_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_331_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v___x_336_);
lean_ctor_set(v___x_337_, 5, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_338_, uint8_t v_isExporting_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v_env_346_; uint8_t v_isExporting_347_; lean_object* v___x_348_; lean_object* v_env_349_; lean_object* v_nextMacroScope_350_; lean_object* v_ngen_351_; lean_object* v_auxDeclNGen_352_; lean_object* v_traceState_353_; lean_object* v_messages_354_; lean_object* v_infoState_355_; lean_object* v_snapshotTasks_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_410_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v_isExporting_347_ = lean_ctor_get_uint8(v_env_346_, sizeof(void*)*8);
lean_dec_ref(v_env_346_);
v___x_348_ = lean_st_ref_take(v___y_343_);
v_env_349_ = lean_ctor_get(v___x_348_, 0);
v_nextMacroScope_350_ = lean_ctor_get(v___x_348_, 1);
v_ngen_351_ = lean_ctor_get(v___x_348_, 2);
v_auxDeclNGen_352_ = lean_ctor_get(v___x_348_, 3);
v_traceState_353_ = lean_ctor_get(v___x_348_, 4);
v_messages_354_ = lean_ctor_get(v___x_348_, 6);
v_infoState_355_ = lean_ctor_get(v___x_348_, 7);
v_snapshotTasks_356_ = lean_ctor_get(v___x_348_, 8);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_348_, 5);
lean_dec(v_unused_411_);
v___x_358_ = v___x_348_;
v_isShared_359_ = v_isSharedCheck_410_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snapshotTasks_356_);
lean_inc(v_infoState_355_);
lean_inc(v_messages_354_);
lean_inc(v_traceState_353_);
lean_inc(v_auxDeclNGen_352_);
lean_inc(v_ngen_351_);
lean_inc(v_nextMacroScope_350_);
lean_inc(v_env_349_);
lean_dec(v___x_348_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_410_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = l_Lean_Environment_setExporting(v_env_349_, v_isExporting_339_);
v___x_361_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 5, v___x_361_);
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_nextMacroScope_350_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_ngen_351_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_auxDeclNGen_352_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_traceState_353_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_messages_354_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_infoState_355_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v_snapshotTasks_356_);
v___x_363_ = v_reuseFailAlloc_409_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_mctx_366_; lean_object* v_zetaDeltaFVarIds_367_; lean_object* v_postponed_368_; lean_object* v_diag_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_407_; 
v___x_364_ = lean_st_ref_set(v___y_343_, v___x_363_);
v___x_365_ = lean_st_ref_take(v___y_341_);
v_mctx_366_ = lean_ctor_get(v___x_365_, 0);
v_zetaDeltaFVarIds_367_ = lean_ctor_get(v___x_365_, 2);
v_postponed_368_ = lean_ctor_get(v___x_365_, 3);
v_diag_369_ = lean_ctor_get(v___x_365_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v___x_365_, 1);
lean_dec(v_unused_408_);
v___x_371_ = v___x_365_;
v_isShared_372_ = v_isSharedCheck_407_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_diag_369_);
lean_inc(v_postponed_368_);
lean_inc(v_zetaDeltaFVarIds_367_);
lean_inc(v_mctx_366_);
lean_dec(v___x_365_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_407_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_mctx_366_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_367_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_368_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_369_);
v___x_375_ = v_reuseFailAlloc_406_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v_r_377_; 
v___x_376_ = lean_st_ref_set(v___y_341_, v___x_375_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v_r_377_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
if (lean_obj_tag(v_r_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_394_; 
v_a_378_ = lean_ctor_get(v_r_377_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_r_377_);
if (v_isSharedCheck_394_ == 0)
{
v___x_380_ = v_r_377_;
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v_r_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
lean_inc(v_a_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_393_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v___x_384_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_347_, v___x_361_, v___y_341_, v___x_373_, v___x_383_);
lean_dec_ref(v___x_383_);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_384_, 0);
lean_dec(v_unused_392_);
v___x_386_ = v___x_384_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_dec(v___x_384_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v_a_378_);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_378_);
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
else
{
lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_395_ = lean_ctor_get(v_r_377_, 0);
lean_inc(v_a_395_);
lean_dec_ref(v_r_377_);
v___x_396_ = lean_box(0);
v___x_397_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_347_, v___x_361_, v___y_341_, v___x_373_, v___x_396_);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v___x_397_, 0);
lean_dec(v_unused_405_);
v___x_399_ = v___x_397_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_dec(v___x_397_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 1);
lean_ctor_set(v___x_399_, 0, v_a_395_);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_395_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_412_, lean_object* v_isExporting_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v_isExporting_boxed_419_; lean_object* v_res_420_; 
v_isExporting_boxed_419_ = lean_unbox(v_isExporting_413_);
v_res_420_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_412_, v_isExporting_boxed_419_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_421_, lean_object* v_x_422_, uint8_t v_isExporting_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_422_, v_isExporting_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_430_, lean_object* v_x_431_, lean_object* v_isExporting_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v_isExporting_boxed_438_; lean_object* v_res_439_; 
v_isExporting_boxed_438_ = lean_unbox(v_isExporting_432_);
v_res_439_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_430_, v_x_431_, v_isExporting_boxed_438_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___f_447_; lean_object* v___x_15693__overap_448_; lean_object* v___x_449_; 
v___f_447_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15693__overap_448_ = lean_panic_fn_borrowed(v___f_447_, v_msg_441_);
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
v___x_449_ = lean_apply_5(v___x_15693__overap_448_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, lean_box(0));
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_457_, lean_object* v_type_458_, lean_object* v_k_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
uint8_t v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; 
v___x_465_ = 0;
v___x_466_ = 0;
v___x_467_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_457_, v___x_465_, v_type_458_, v_k_459_, v___x_466_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_468_, lean_object* v_type_469_, lean_object* v_k_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_468_, v_type_469_, v_k_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_477_, lean_object* v_alts_478_, lean_object* v_j_479_, lean_object* v_zs1_480_, uint8_t v_isZero_481_, uint8_t v___x_482_, uint8_t v___x_483_, lean_object* v_zs2_484_, lean_object* v_x_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_array_get_borrowed(v___x_477_, v_alts_478_, v_j_479_);
v___x_492_ = l_Array_append___redArg(v_zs1_480_, v_zs2_484_);
lean_inc(v___x_491_);
v___x_493_ = l_Lean_mkAppN(v___x_491_, v___x_492_);
lean_dec_ref(v___x_492_);
v___x_494_ = l_Lean_Meta_mkLambdaFVars(v_zs2_484_, v___x_493_, v_isZero_481_, v___x_482_, v_isZero_481_, v___x_482_, v___x_483_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_495_, lean_object* v_alts_496_, lean_object* v_j_497_, lean_object* v_zs1_498_, lean_object* v_isZero_499_, lean_object* v___x_500_, lean_object* v___x_501_, lean_object* v_zs2_502_, lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v_isZero_boxed_509_; uint8_t v___x_20821__boxed_510_; uint8_t v___x_20822__boxed_511_; lean_object* v_res_512_; 
v_isZero_boxed_509_ = lean_unbox(v_isZero_499_);
v___x_20821__boxed_510_ = lean_unbox(v___x_500_);
v___x_20822__boxed_511_ = lean_unbox(v___x_501_);
v_res_512_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_495_, v_alts_496_, v_j_497_, v_zs1_498_, v_isZero_boxed_509_, v___x_20821__boxed_510_, v___x_20822__boxed_511_, v_zs2_502_, v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_x_503_);
lean_dec_ref(v_zs2_502_);
lean_dec(v_j_497_);
lean_dec_ref(v_alts_496_);
lean_dec_ref(v___x_495_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_513_, lean_object* v_ism2_514_, lean_object* v_motive_515_, uint8_t v_isZero_516_, uint8_t v___x_517_, uint8_t v___x_518_, lean_object* v_a_519_, lean_object* v___f_520_, lean_object* v_zs1_521_, lean_object* v_val_522_, lean_object* v___x_523_, lean_object* v_indName_524_, lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v_params_527_, lean_object* v___x_528_, lean_object* v_h_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = l_Array_append___redArg(v___x_513_, v_ism2_514_);
v___x_536_ = l_Lean_mkAppN(v_motive_515_, v___x_535_);
lean_dec_ref(v___x_535_);
v___x_537_ = l_Lean_Meta_mkLambdaFVars(v_ism2_514_, v___x_536_, v_isZero_516_, v___x_517_, v_isZero_516_, v___x_517_, v___x_518_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref(v___x_537_);
v___x_539_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_519_, v___f_520_, v_isZero_516_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___y_542_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_539_);
v___x_545_ = l_Lean_InductiveVal_numCtors(v_val_522_);
v___x_546_ = lean_nat_dec_eq(v___x_545_, v___x_523_);
lean_dec(v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v___x_528_);
v___x_547_ = l_Lean_mkConstructorElimName(v_indName_524_, v___x_525_);
v___x_548_ = l_Lean_mkConst(v___x_547_, v___x_526_);
v___x_549_ = lean_mk_empty_array_with_capacity(v___x_523_);
v___x_550_ = lean_array_push(v___x_549_, v_a_538_);
v___x_551_ = l_Array_append___redArg(v_params_527_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = l_Array_append___redArg(v___x_551_, v_ism2_514_);
v___x_553_ = lean_unsigned_to_nat(2u);
v___x_554_ = lean_mk_empty_array_with_capacity(v___x_553_);
lean_inc_ref(v_h_529_);
v___x_555_ = lean_array_push(v___x_554_, v_h_529_);
v___x_556_ = lean_array_push(v___x_555_, v_a_540_);
v___x_557_ = l_Array_append___redArg(v___x_552_, v___x_556_);
lean_dec_ref(v___x_556_);
v___x_558_ = l_Lean_mkAppN(v___x_548_, v___x_557_);
lean_dec_ref(v___x_557_);
v___y_542_ = v___x_558_;
goto v___jp_541_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_525_);
lean_dec(v_indName_524_);
v___x_559_ = l_Lean_mkConst(v___x_528_, v___x_526_);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_523_);
lean_inc_ref(v___x_560_);
v___x_561_ = lean_array_push(v___x_560_, v_a_538_);
v___x_562_ = l_Array_append___redArg(v_params_527_, v___x_561_);
lean_dec_ref(v___x_561_);
v___x_563_ = l_Array_append___redArg(v___x_562_, v_ism2_514_);
v___x_564_ = lean_array_push(v___x_560_, v_a_540_);
v___x_565_ = l_Array_append___redArg(v___x_563_, v___x_564_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_Lean_mkAppN(v___x_559_, v___x_565_);
lean_dec_ref(v___x_565_);
v___y_542_ = v___x_566_;
goto v___jp_541_;
}
v___jp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_array_push(v_zs1_521_, v_h_529_);
v___x_544_ = l_Lean_Meta_mkLambdaFVars(v___x_543_, v___y_542_, v_isZero_516_, v___x_517_, v_isZero_516_, v___x_517_, v___x_518_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec_ref(v___x_543_);
return v___x_544_;
}
}
else
{
lean_dec(v_a_538_);
lean_dec_ref(v_h_529_);
lean_dec(v___x_528_);
lean_dec_ref(v_params_527_);
lean_dec(v___x_526_);
lean_dec(v___x_525_);
lean_dec(v_indName_524_);
lean_dec_ref(v_zs1_521_);
return v___x_539_;
}
}
else
{
lean_dec_ref(v_h_529_);
lean_dec(v___x_528_);
lean_dec_ref(v_params_527_);
lean_dec(v___x_526_);
lean_dec(v___x_525_);
lean_dec(v_indName_524_);
lean_dec_ref(v_zs1_521_);
lean_dec_ref(v___f_520_);
lean_dec_ref(v_a_519_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_567_ = _args[0];
lean_object* v_ism2_568_ = _args[1];
lean_object* v_motive_569_ = _args[2];
lean_object* v_isZero_570_ = _args[3];
lean_object* v___x_571_ = _args[4];
lean_object* v___x_572_ = _args[5];
lean_object* v_a_573_ = _args[6];
lean_object* v___f_574_ = _args[7];
lean_object* v_zs1_575_ = _args[8];
lean_object* v_val_576_ = _args[9];
lean_object* v___x_577_ = _args[10];
lean_object* v_indName_578_ = _args[11];
lean_object* v___x_579_ = _args[12];
lean_object* v___x_580_ = _args[13];
lean_object* v_params_581_ = _args[14];
lean_object* v___x_582_ = _args[15];
lean_object* v_h_583_ = _args[16];
lean_object* v___y_584_ = _args[17];
lean_object* v___y_585_ = _args[18];
lean_object* v___y_586_ = _args[19];
lean_object* v___y_587_ = _args[20];
lean_object* v___y_588_ = _args[21];
_start:
{
uint8_t v_isZero_boxed_589_; uint8_t v___x_20856__boxed_590_; uint8_t v___x_20857__boxed_591_; lean_object* v_res_592_; 
v_isZero_boxed_589_ = lean_unbox(v_isZero_570_);
v___x_20856__boxed_590_ = lean_unbox(v___x_571_);
v___x_20857__boxed_591_ = lean_unbox(v___x_572_);
v_res_592_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_567_, v_ism2_568_, v_motive_569_, v_isZero_boxed_589_, v___x_20856__boxed_590_, v___x_20857__boxed_591_, v_a_573_, v___f_574_, v_zs1_575_, v_val_576_, v___x_577_, v_indName_578_, v___x_579_, v___x_580_, v_params_581_, v___x_582_, v_h_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___x_577_);
lean_dec_ref(v_val_576_);
lean_dec_ref(v_ism2_568_);
return v_res_592_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_593_; lean_object* v_dummy_594_; 
v___x_593_ = lean_box(0);
v_dummy_594_ = l_Lean_Expr_sort___override(v___x_593_);
return v_dummy_594_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
v___x_602_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_603_ = l_Lean_mkConst(v___x_602_, v___x_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_604_, lean_object* v_alts_605_, lean_object* v_j_606_, uint8_t v_isZero_607_, uint8_t v___x_608_, uint8_t v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_ism2_613_, lean_object* v_motive_614_, lean_object* v_a_615_, lean_object* v_val_616_, lean_object* v_indName_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v_params_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v_zs1_624_, lean_object* v_ctorRet1_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
v___x_631_ = lean_whnf(v_ctorRet1_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v_dummy_638_; lean_object* v_nargs_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = lean_box(v_isZero_607_);
v___x_634_ = lean_box(v___x_608_);
v___x_635_ = lean_box(v___x_609_);
lean_inc_ref(v_zs1_624_);
lean_inc(v_j_606_);
v___f_636_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_636_, 0, v___x_604_);
lean_closure_set(v___f_636_, 1, v_alts_605_);
lean_closure_set(v___f_636_, 2, v_j_606_);
lean_closure_set(v___f_636_, 3, v_zs1_624_);
lean_closure_set(v___f_636_, 4, v___x_633_);
lean_closure_set(v___f_636_, 5, v___x_634_);
lean_closure_set(v___f_636_, 6, v___x_635_);
v___x_637_ = l_Lean_mkAppN(v___x_610_, v_zs1_624_);
v_dummy_638_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_639_ = l_Lean_Expr_getAppNumArgs(v_a_632_);
lean_inc(v_nargs_639_);
v___x_640_ = lean_mk_array(v_nargs_639_, v_dummy_638_);
v___x_641_ = lean_nat_sub(v_nargs_639_, v___x_611_);
lean_dec(v_nargs_639_);
v___x_642_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_632_, v___x_640_, v___x_641_);
v___x_643_ = lean_array_get_size(v___x_642_);
v___x_644_ = l_Array_toSubarray___redArg(v___x_642_, v___x_612_, v___x_643_);
v___x_645_ = l_Subarray_copy___redArg(v___x_644_);
v___x_646_ = lean_array_push(v___x_645_, v___x_637_);
v___x_647_ = lean_box(v_isZero_607_);
v___x_648_ = lean_box(v___x_608_);
v___x_649_ = lean_box(v___x_609_);
lean_inc(v___x_611_);
v___f_650_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_650_, 0, v___x_646_);
lean_closure_set(v___f_650_, 1, v_ism2_613_);
lean_closure_set(v___f_650_, 2, v_motive_614_);
lean_closure_set(v___f_650_, 3, v___x_647_);
lean_closure_set(v___f_650_, 4, v___x_648_);
lean_closure_set(v___f_650_, 5, v___x_649_);
lean_closure_set(v___f_650_, 6, v_a_615_);
lean_closure_set(v___f_650_, 7, v___f_636_);
lean_closure_set(v___f_650_, 8, v_zs1_624_);
lean_closure_set(v___f_650_, 9, v_val_616_);
lean_closure_set(v___f_650_, 10, v___x_611_);
lean_closure_set(v___f_650_, 11, v_indName_617_);
lean_closure_set(v___f_650_, 12, v___x_618_);
lean_closure_set(v___f_650_, 13, v___x_619_);
lean_closure_set(v___f_650_, 14, v_params_620_);
lean_closure_set(v___f_650_, 15, v___x_621_);
v___x_651_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_652_ = l_Lean_Level_ofNat(v___x_611_);
lean_dec(v___x_611_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_mkConst(v___x_651_, v___x_654_);
v___x_656_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_657_ = l_Lean_mkRawNatLit(v_j_606_);
v___x_658_ = l_Lean_mkApp3(v___x_655_, v___x_656_, v___x_622_, v___x_657_);
v___x_659_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_623_, v___x_658_, v___f_650_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
return v___x_659_;
}
else
{
lean_dec_ref(v_zs1_624_);
lean_dec(v___x_623_);
lean_dec_ref(v___x_622_);
lean_dec(v___x_621_);
lean_dec_ref(v_params_620_);
lean_dec(v___x_619_);
lean_dec(v___x_618_);
lean_dec(v_indName_617_);
lean_dec_ref(v_val_616_);
lean_dec_ref(v_a_615_);
lean_dec_ref(v_motive_614_);
lean_dec_ref(v_ism2_613_);
lean_dec(v___x_612_);
lean_dec(v___x_611_);
lean_dec_ref(v___x_610_);
lean_dec(v_j_606_);
lean_dec_ref(v_alts_605_);
lean_dec_ref(v___x_604_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_660_ = _args[0];
lean_object* v_alts_661_ = _args[1];
lean_object* v_j_662_ = _args[2];
lean_object* v_isZero_663_ = _args[3];
lean_object* v___x_664_ = _args[4];
lean_object* v___x_665_ = _args[5];
lean_object* v___x_666_ = _args[6];
lean_object* v___x_667_ = _args[7];
lean_object* v___x_668_ = _args[8];
lean_object* v_ism2_669_ = _args[9];
lean_object* v_motive_670_ = _args[10];
lean_object* v_a_671_ = _args[11];
lean_object* v_val_672_ = _args[12];
lean_object* v_indName_673_ = _args[13];
lean_object* v___x_674_ = _args[14];
lean_object* v___x_675_ = _args[15];
lean_object* v_params_676_ = _args[16];
lean_object* v___x_677_ = _args[17];
lean_object* v___x_678_ = _args[18];
lean_object* v___x_679_ = _args[19];
lean_object* v_zs1_680_ = _args[20];
lean_object* v_ctorRet1_681_ = _args[21];
lean_object* v___y_682_ = _args[22];
lean_object* v___y_683_ = _args[23];
lean_object* v___y_684_ = _args[24];
lean_object* v___y_685_ = _args[25];
lean_object* v___y_686_ = _args[26];
_start:
{
uint8_t v_isZero_boxed_687_; uint8_t v___x_20987__boxed_688_; uint8_t v___x_20988__boxed_689_; lean_object* v_res_690_; 
v_isZero_boxed_687_ = lean_unbox(v_isZero_663_);
v___x_20987__boxed_688_ = lean_unbox(v___x_664_);
v___x_20988__boxed_689_ = lean_unbox(v___x_665_);
v_res_690_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_660_, v_alts_661_, v_j_662_, v_isZero_boxed_687_, v___x_20987__boxed_688_, v___x_20988__boxed_689_, v___x_666_, v___x_667_, v___x_668_, v_ism2_669_, v_motive_670_, v_a_671_, v_val_672_, v_indName_673_, v___x_674_, v___x_675_, v_params_676_, v___x_677_, v___x_678_, v___x_679_, v_zs1_680_, v_ctorRet1_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_694_, lean_object* v_params_695_, lean_object* v_alts_696_, lean_object* v___x_697_, lean_object* v_ism2_698_, lean_object* v_motive_699_, lean_object* v_val_700_, lean_object* v_indName_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v_as_705_, lean_object* v_i_706_, lean_object* v_j_707_, lean_object* v_bs_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_zero_714_; uint8_t v_isZero_715_; 
v_zero_714_ = lean_unsigned_to_nat(0u);
v_isZero_715_ = lean_nat_dec_eq(v_i_706_, v_zero_714_);
if (v_isZero_715_ == 1)
{
lean_object* v___x_716_; 
lean_dec(v_j_707_);
lean_dec(v_i_706_);
lean_dec_ref(v___x_704_);
lean_dec(v___x_703_);
lean_dec(v___x_702_);
lean_dec(v_indName_701_);
lean_dec_ref(v_val_700_);
lean_dec_ref(v_motive_699_);
lean_dec_ref(v_ism2_698_);
lean_dec(v___x_697_);
lean_dec_ref(v_alts_696_);
lean_dec_ref(v_params_695_);
lean_dec(v_tail_694_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_bs_708_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; lean_object* v_n_718_; lean_object* v___y_720_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v_n_718_ = lean_nat_sub(v_i_706_, v___x_717_);
lean_dec(v_i_706_);
v___x_733_ = lean_array_fget_borrowed(v_as_705_, v_j_707_);
lean_inc(v_tail_694_);
lean_inc(v___x_733_);
v___x_734_ = l_Lean_mkConst(v___x_733_, v_tail_694_);
v___x_735_ = l_Lean_mkAppN(v___x_734_, v_params_695_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc_ref(v___x_735_);
v___x_736_ = lean_infer_type(v___x_735_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; uint8_t v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_746_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_736_);
v___x_738_ = l_Lean_instInhabitedExpr;
v___x_739_ = 1;
v___x_740_ = 1;
v___x_741_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_742_ = lean_box(v_isZero_715_);
v___x_743_ = lean_box(v___x_739_);
v___x_744_ = lean_box(v___x_740_);
lean_inc_ref(v___x_704_);
lean_inc(v___x_703_);
lean_inc_ref(v_params_695_);
lean_inc(v___x_702_);
lean_inc(v___x_733_);
lean_inc(v_indName_701_);
lean_inc_ref(v_val_700_);
lean_inc(v_a_737_);
lean_inc_ref(v_motive_699_);
lean_inc_ref(v_ism2_698_);
lean_inc(v___x_697_);
lean_inc(v_j_707_);
lean_inc_ref(v_alts_696_);
v___f_745_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_745_, 0, v___x_738_);
lean_closure_set(v___f_745_, 1, v_alts_696_);
lean_closure_set(v___f_745_, 2, v_j_707_);
lean_closure_set(v___f_745_, 3, v___x_742_);
lean_closure_set(v___f_745_, 4, v___x_743_);
lean_closure_set(v___f_745_, 5, v___x_744_);
lean_closure_set(v___f_745_, 6, v___x_735_);
lean_closure_set(v___f_745_, 7, v___x_717_);
lean_closure_set(v___f_745_, 8, v___x_697_);
lean_closure_set(v___f_745_, 9, v_ism2_698_);
lean_closure_set(v___f_745_, 10, v_motive_699_);
lean_closure_set(v___f_745_, 11, v_a_737_);
lean_closure_set(v___f_745_, 12, v_val_700_);
lean_closure_set(v___f_745_, 13, v_indName_701_);
lean_closure_set(v___f_745_, 14, v___x_733_);
lean_closure_set(v___f_745_, 15, v___x_702_);
lean_closure_set(v___f_745_, 16, v_params_695_);
lean_closure_set(v___f_745_, 17, v___x_703_);
lean_closure_set(v___f_745_, 18, v___x_704_);
lean_closure_set(v___f_745_, 19, v___x_741_);
v___x_746_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_737_, v___f_745_, v_isZero_715_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
v___y_720_ = v___x_746_;
goto v___jp_719_;
}
else
{
lean_dec_ref(v___x_735_);
v___y_720_ = v___x_736_;
goto v___jp_719_;
}
v___jp_719_:
{
if (lean_obj_tag(v___y_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_721_ = lean_ctor_get(v___y_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref(v___y_720_);
v___x_722_ = lean_nat_add(v_j_707_, v___x_717_);
lean_dec(v_j_707_);
v___x_723_ = lean_array_push(v_bs_708_, v_a_721_);
v_i_706_ = v_n_718_;
v_j_707_ = v___x_722_;
v_bs_708_ = v___x_723_;
goto _start;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_n_718_);
lean_dec_ref(v_bs_708_);
lean_dec(v_j_707_);
lean_dec_ref(v___x_704_);
lean_dec(v___x_703_);
lean_dec(v___x_702_);
lean_dec(v_indName_701_);
lean_dec_ref(v_val_700_);
lean_dec_ref(v_motive_699_);
lean_dec_ref(v_ism2_698_);
lean_dec(v___x_697_);
lean_dec_ref(v_alts_696_);
lean_dec_ref(v_params_695_);
lean_dec(v_tail_694_);
v_a_725_ = lean_ctor_get(v___y_720_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___y_720_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___y_720_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___y_720_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_747_ = _args[0];
lean_object* v_params_748_ = _args[1];
lean_object* v_alts_749_ = _args[2];
lean_object* v___x_750_ = _args[3];
lean_object* v_ism2_751_ = _args[4];
lean_object* v_motive_752_ = _args[5];
lean_object* v_val_753_ = _args[6];
lean_object* v_indName_754_ = _args[7];
lean_object* v___x_755_ = _args[8];
lean_object* v___x_756_ = _args[9];
lean_object* v___x_757_ = _args[10];
lean_object* v_as_758_ = _args[11];
lean_object* v_i_759_ = _args[12];
lean_object* v_j_760_ = _args[13];
lean_object* v_bs_761_ = _args[14];
lean_object* v___y_762_ = _args[15];
lean_object* v___y_763_ = _args[16];
lean_object* v___y_764_ = _args[17];
lean_object* v___y_765_ = _args[18];
lean_object* v___y_766_ = _args[19];
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_747_, v_params_748_, v_alts_749_, v___x_750_, v_ism2_751_, v_motive_752_, v_val_753_, v_indName_754_, v___x_755_, v___x_756_, v___x_757_, v_as_758_, v_i_759_, v_j_760_, v_bs_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec_ref(v_as_758_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_768_, lean_object* v___x_769_, lean_object* v_a_770_, lean_object* v_ism1_771_, uint8_t v___x_772_, uint8_t v___x_773_, uint8_t v___x_774_, lean_object* v___x_775_, lean_object* v_tail_776_, lean_object* v_params_777_, lean_object* v_alts_778_, lean_object* v_numParams_779_, lean_object* v_ism2_780_, lean_object* v_val_781_, lean_object* v_indName_782_, lean_object* v___x_783_, lean_object* v___x_784_, lean_object* v___x_785_, lean_object* v_name_786_, lean_object* v___x_787_, lean_object* v_heq_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc_ref(v_motive_768_);
v___x_794_ = l_Lean_mkAppN(v_motive_768_, v___x_769_);
v___x_795_ = l_Lean_mkArrow(v_a_770_, v___x_794_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_795_);
v___x_797_ = l_Lean_Meta_mkLambdaFVars(v_ism1_771_, v_a_796_, v___x_772_, v___x_773_, v___x_772_, v___x_773_, v___x_774_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
v___x_799_ = lean_array_get_size(v___x_775_);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_mk_empty_array_with_capacity(v___x_799_);
lean_inc(v___x_783_);
lean_inc_ref(v_motive_768_);
lean_inc_ref(v_ism2_780_);
lean_inc_ref(v_alts_778_);
lean_inc_ref(v_params_777_);
v___x_802_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_776_, v_params_777_, v_alts_778_, v_numParams_779_, v_ism2_780_, v_motive_768_, v_val_781_, v_indName_782_, v___x_783_, v___x_784_, v___x_785_, v___x_775_, v___x_799_, v___x_800_, v___x_801_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v___x_802_);
lean_inc_ref(v_heq_788_);
v___x_804_ = l_Lean_Meta_mkEqSymm(v_heq_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v___x_804_);
v___x_806_ = l_Lean_mkConst(v_name_786_, v___x_783_);
v___x_807_ = l_Lean_mkAppN(v___x_806_, v_params_777_);
v___x_808_ = l_Lean_Expr_app___override(v___x_807_, v_a_798_);
v___x_809_ = l_Lean_mkAppN(v___x_808_, v_ism1_771_);
v___x_810_ = l_Lean_mkAppN(v___x_809_, v_a_803_);
lean_dec(v_a_803_);
v___x_811_ = l_Lean_Expr_app___override(v___x_810_, v_a_805_);
v___x_812_ = lean_mk_empty_array_with_capacity(v___x_787_);
lean_inc_ref(v___x_812_);
v___x_813_ = lean_array_push(v___x_812_, v_motive_768_);
v___x_814_ = l_Array_append___redArg(v_params_777_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = l_Array_append___redArg(v___x_814_, v_ism1_771_);
v___x_816_ = l_Array_append___redArg(v___x_815_, v_ism2_780_);
lean_dec_ref(v_ism2_780_);
v___x_817_ = lean_array_push(v___x_812_, v_heq_788_);
v___x_818_ = l_Array_append___redArg(v___x_816_, v___x_817_);
lean_dec_ref(v___x_817_);
v___x_819_ = l_Array_append___redArg(v___x_818_, v_alts_778_);
lean_dec_ref(v_alts_778_);
v___x_820_ = l_Lean_Meta_mkLambdaFVars(v___x_819_, v___x_811_, v___x_772_, v___x_773_, v___x_772_, v___x_773_, v___x_774_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec_ref(v___x_819_);
return v___x_820_;
}
else
{
lean_dec(v_a_803_);
lean_dec(v_a_798_);
lean_dec_ref(v_heq_788_);
lean_dec(v_name_786_);
lean_dec(v___x_783_);
lean_dec_ref(v_ism2_780_);
lean_dec_ref(v_alts_778_);
lean_dec_ref(v_params_777_);
lean_dec_ref(v_motive_768_);
return v___x_804_;
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_a_798_);
lean_dec_ref(v_heq_788_);
lean_dec(v_name_786_);
lean_dec(v___x_783_);
lean_dec_ref(v_ism2_780_);
lean_dec_ref(v_alts_778_);
lean_dec_ref(v_params_777_);
lean_dec_ref(v_motive_768_);
v_a_821_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_802_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_802_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
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
else
{
lean_dec_ref(v_heq_788_);
lean_dec(v_name_786_);
lean_dec_ref(v___x_785_);
lean_dec(v___x_784_);
lean_dec(v___x_783_);
lean_dec(v_indName_782_);
lean_dec_ref(v_val_781_);
lean_dec_ref(v_ism2_780_);
lean_dec(v_numParams_779_);
lean_dec_ref(v_alts_778_);
lean_dec_ref(v_params_777_);
lean_dec(v_tail_776_);
lean_dec_ref(v_motive_768_);
return v___x_797_;
}
}
else
{
lean_dec_ref(v_heq_788_);
lean_dec(v_name_786_);
lean_dec_ref(v___x_785_);
lean_dec(v___x_784_);
lean_dec(v___x_783_);
lean_dec(v_indName_782_);
lean_dec_ref(v_val_781_);
lean_dec_ref(v_ism2_780_);
lean_dec(v_numParams_779_);
lean_dec_ref(v_alts_778_);
lean_dec_ref(v_params_777_);
lean_dec(v_tail_776_);
lean_dec_ref(v_motive_768_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_829_ = _args[0];
lean_object* v___x_830_ = _args[1];
lean_object* v_a_831_ = _args[2];
lean_object* v_ism1_832_ = _args[3];
lean_object* v___x_833_ = _args[4];
lean_object* v___x_834_ = _args[5];
lean_object* v___x_835_ = _args[6];
lean_object* v___x_836_ = _args[7];
lean_object* v_tail_837_ = _args[8];
lean_object* v_params_838_ = _args[9];
lean_object* v_alts_839_ = _args[10];
lean_object* v_numParams_840_ = _args[11];
lean_object* v_ism2_841_ = _args[12];
lean_object* v_val_842_ = _args[13];
lean_object* v_indName_843_ = _args[14];
lean_object* v___x_844_ = _args[15];
lean_object* v___x_845_ = _args[16];
lean_object* v___x_846_ = _args[17];
lean_object* v_name_847_ = _args[18];
lean_object* v___x_848_ = _args[19];
lean_object* v_heq_849_ = _args[20];
lean_object* v___y_850_ = _args[21];
lean_object* v___y_851_ = _args[22];
lean_object* v___y_852_ = _args[23];
lean_object* v___y_853_ = _args[24];
lean_object* v___y_854_ = _args[25];
_start:
{
uint8_t v___x_21212__boxed_855_; uint8_t v___x_21213__boxed_856_; uint8_t v___x_21214__boxed_857_; lean_object* v_res_858_; 
v___x_21212__boxed_855_ = lean_unbox(v___x_833_);
v___x_21213__boxed_856_ = lean_unbox(v___x_834_);
v___x_21214__boxed_857_ = lean_unbox(v___x_835_);
v_res_858_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_829_, v___x_830_, v_a_831_, v_ism1_832_, v___x_21212__boxed_855_, v___x_21213__boxed_856_, v___x_21214__boxed_857_, v___x_836_, v_tail_837_, v_params_838_, v_alts_839_, v_numParams_840_, v_ism2_841_, v_val_842_, v_indName_843_, v___x_844_, v___x_845_, v___x_846_, v_name_847_, v___x_848_, v_heq_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_836_);
lean_dec_ref(v_ism1_832_);
lean_dec_ref(v___x_830_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_859_, lean_object* v_tail_860_, lean_object* v_params_861_, lean_object* v_ism1_862_, lean_object* v_ism2_863_, lean_object* v_motive_864_, lean_object* v___x_865_, uint8_t v___x_866_, uint8_t v___x_867_, uint8_t v___x_868_, lean_object* v___x_869_, lean_object* v_numParams_870_, lean_object* v_val_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v_name_874_, lean_object* v___x_875_, lean_object* v_alts_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_inc(v_indName_859_);
v___x_882_ = l_mkCtorIdxName(v_indName_859_);
lean_inc(v_tail_860_);
v___x_883_ = l_Lean_mkConst(v___x_882_, v_tail_860_);
lean_inc_ref(v_params_861_);
v___x_884_ = l_Array_append___redArg(v_params_861_, v_ism1_862_);
lean_inc_ref(v___x_883_);
v___x_885_ = l_Lean_mkAppN(v___x_883_, v___x_884_);
lean_dec_ref(v___x_884_);
lean_inc_ref(v_params_861_);
v___x_886_ = l_Array_append___redArg(v_params_861_, v_ism2_863_);
v___x_887_ = l_Lean_mkAppN(v___x_883_, v___x_886_);
lean_dec_ref(v___x_886_);
lean_inc_ref(v___x_887_);
lean_inc_ref(v___x_885_);
v___x_888_ = l_Lean_Meta_mkEq(v___x_885_, v___x_887_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
lean_inc_ref(v___x_887_);
v___x_890_ = l_Lean_Meta_mkEq(v___x_887_, v___x_885_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
v___x_892_ = lean_box(v___x_866_);
v___x_893_ = lean_box(v___x_867_);
v___x_894_ = lean_box(v___x_868_);
v___f_895_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_895_, 0, v_motive_864_);
lean_closure_set(v___f_895_, 1, v___x_865_);
lean_closure_set(v___f_895_, 2, v_a_891_);
lean_closure_set(v___f_895_, 3, v_ism1_862_);
lean_closure_set(v___f_895_, 4, v___x_892_);
lean_closure_set(v___f_895_, 5, v___x_893_);
lean_closure_set(v___f_895_, 6, v___x_894_);
lean_closure_set(v___f_895_, 7, v___x_869_);
lean_closure_set(v___f_895_, 8, v_tail_860_);
lean_closure_set(v___f_895_, 9, v_params_861_);
lean_closure_set(v___f_895_, 10, v_alts_876_);
lean_closure_set(v___f_895_, 11, v_numParams_870_);
lean_closure_set(v___f_895_, 12, v_ism2_863_);
lean_closure_set(v___f_895_, 13, v_val_871_);
lean_closure_set(v___f_895_, 14, v_indName_859_);
lean_closure_set(v___f_895_, 15, v___x_872_);
lean_closure_set(v___f_895_, 16, v___x_873_);
lean_closure_set(v___f_895_, 17, v___x_887_);
lean_closure_set(v___f_895_, 18, v_name_874_);
lean_closure_set(v___f_895_, 19, v___x_875_);
v___x_896_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_897_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_896_, v_a_889_, v___f_895_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
return v___x_897_;
}
else
{
lean_dec(v_a_889_);
lean_dec_ref(v___x_887_);
lean_dec_ref(v_alts_876_);
lean_dec(v___x_875_);
lean_dec(v_name_874_);
lean_dec(v___x_873_);
lean_dec(v___x_872_);
lean_dec_ref(v_val_871_);
lean_dec(v_numParams_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v_motive_864_);
lean_dec_ref(v_ism2_863_);
lean_dec_ref(v_ism1_862_);
lean_dec_ref(v_params_861_);
lean_dec(v_tail_860_);
lean_dec(v_indName_859_);
return v___x_890_;
}
}
else
{
lean_dec_ref(v___x_887_);
lean_dec_ref(v___x_885_);
lean_dec_ref(v_alts_876_);
lean_dec(v___x_875_);
lean_dec(v_name_874_);
lean_dec(v___x_873_);
lean_dec(v___x_872_);
lean_dec_ref(v_val_871_);
lean_dec(v_numParams_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_865_);
lean_dec_ref(v_motive_864_);
lean_dec_ref(v_ism2_863_);
lean_dec_ref(v_ism1_862_);
lean_dec_ref(v_params_861_);
lean_dec(v_tail_860_);
lean_dec(v_indName_859_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_898_ = _args[0];
lean_object* v_tail_899_ = _args[1];
lean_object* v_params_900_ = _args[2];
lean_object* v_ism1_901_ = _args[3];
lean_object* v_ism2_902_ = _args[4];
lean_object* v_motive_903_ = _args[5];
lean_object* v___x_904_ = _args[6];
lean_object* v___x_905_ = _args[7];
lean_object* v___x_906_ = _args[8];
lean_object* v___x_907_ = _args[9];
lean_object* v___x_908_ = _args[10];
lean_object* v_numParams_909_ = _args[11];
lean_object* v_val_910_ = _args[12];
lean_object* v___x_911_ = _args[13];
lean_object* v___x_912_ = _args[14];
lean_object* v_name_913_ = _args[15];
lean_object* v___x_914_ = _args[16];
lean_object* v_alts_915_ = _args[17];
lean_object* v___y_916_ = _args[18];
lean_object* v___y_917_ = _args[19];
lean_object* v___y_918_ = _args[20];
lean_object* v___y_919_ = _args[21];
lean_object* v___y_920_ = _args[22];
_start:
{
uint8_t v___x_21339__boxed_921_; uint8_t v___x_21340__boxed_922_; uint8_t v___x_21341__boxed_923_; lean_object* v_res_924_; 
v___x_21339__boxed_921_ = lean_unbox(v___x_905_);
v___x_21340__boxed_922_ = lean_unbox(v___x_906_);
v___x_21341__boxed_923_ = lean_unbox(v___x_907_);
v_res_924_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_898_, v_tail_899_, v_params_900_, v_ism1_901_, v_ism2_902_, v_motive_903_, v___x_904_, v___x_21339__boxed_921_, v___x_21340__boxed_922_, v___x_21341__boxed_923_, v___x_908_, v_numParams_909_, v_val_910_, v___x_911_, v___x_912_, v_name_913_, v___x_914_, v_alts_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_926_, lean_object* v_dummy_927_, lean_object* v___x_928_, lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_motive_931_, lean_object* v_zs1_932_, uint8_t v_isZero_933_, uint8_t v___x_934_, uint8_t v___x_935_, lean_object* v___x_936_, lean_object* v_j_937_, lean_object* v_zs2_938_, lean_object* v_ctorRet2_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
lean_inc(v___y_943_);
lean_inc_ref(v___y_942_);
lean_inc(v___y_941_);
lean_inc_ref(v___y_940_);
v___x_945_ = lean_whnf(v_ctorRet2_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; lean_object* v_nargs_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_945_);
v___x_947_ = l_Lean_mkAppN(v___x_926_, v_zs2_938_);
v_nargs_948_ = l_Lean_Expr_getAppNumArgs(v_a_946_);
lean_inc(v_nargs_948_);
v___x_949_ = lean_mk_array(v_nargs_948_, v_dummy_927_);
v___x_950_ = lean_nat_sub(v_nargs_948_, v___x_928_);
lean_dec(v_nargs_948_);
v___x_951_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_946_, v___x_949_, v___x_950_);
v___x_952_ = lean_array_get_size(v___x_951_);
v___x_953_ = l_Array_toSubarray___redArg(v___x_951_, v___x_929_, v___x_952_);
v___x_954_ = l_Subarray_copy___redArg(v___x_953_);
v___x_955_ = lean_array_push(v___x_954_, v___x_947_);
v___x_956_ = l_Array_append___redArg(v___x_930_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = l_Lean_mkAppN(v_motive_931_, v___x_956_);
lean_dec_ref(v___x_956_);
v___x_958_ = l_Array_append___redArg(v_zs1_932_, v_zs2_938_);
v___x_959_ = l_Lean_Meta_mkForallFVars(v___x_958_, v___x_957_, v_isZero_933_, v___x_934_, v___x_934_, v___x_935_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec_ref(v___x_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_979_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_979_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_979_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_979_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___y_965_; 
if (lean_obj_tag(v___x_936_) == 1)
{
lean_object* v_str_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_str_970_ = lean_ctor_get(v___x_936_, 1);
lean_inc_ref(v_str_970_);
lean_dec_ref(v___x_936_);
v___x_971_ = lean_box(0);
v___x_972_ = l_Lean_Name_str___override(v___x_971_, v_str_970_);
v___y_965_ = v___x_972_;
goto v___jp_964_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v___x_936_);
v___x_973_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_974_ = lean_nat_add(v_j_937_, v___x_928_);
v___x_975_ = l_Nat_reprFast(v___x_974_);
v___x_976_ = lean_string_append(v___x_973_, v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = lean_box(0);
v___x_978_ = l_Lean_Name_str___override(v___x_977_, v___x_976_);
v___y_965_ = v___x_978_;
goto v___jp_964_;
}
v___jp_964_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___y_965_);
lean_ctor_set(v___x_966_, 1, v_a_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_966_);
v___x_968_ = v___x_962_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v___x_936_);
v_a_980_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_959_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_959_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
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
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v___x_936_);
lean_dec_ref(v_zs1_932_);
lean_dec_ref(v_motive_931_);
lean_dec_ref(v___x_930_);
lean_dec(v___x_929_);
lean_dec_ref(v_dummy_927_);
lean_dec_ref(v___x_926_);
v_a_988_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_945_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_945_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_996_ = _args[0];
lean_object* v_dummy_997_ = _args[1];
lean_object* v___x_998_ = _args[2];
lean_object* v___x_999_ = _args[3];
lean_object* v___x_1000_ = _args[4];
lean_object* v_motive_1001_ = _args[5];
lean_object* v_zs1_1002_ = _args[6];
lean_object* v_isZero_1003_ = _args[7];
lean_object* v___x_1004_ = _args[8];
lean_object* v___x_1005_ = _args[9];
lean_object* v___x_1006_ = _args[10];
lean_object* v_j_1007_ = _args[11];
lean_object* v_zs2_1008_ = _args[12];
lean_object* v_ctorRet2_1009_ = _args[13];
lean_object* v___y_1010_ = _args[14];
lean_object* v___y_1011_ = _args[15];
lean_object* v___y_1012_ = _args[16];
lean_object* v___y_1013_ = _args[17];
lean_object* v___y_1014_ = _args[18];
_start:
{
uint8_t v_isZero_boxed_1015_; uint8_t v___x_21423__boxed_1016_; uint8_t v___x_21424__boxed_1017_; lean_object* v_res_1018_; 
v_isZero_boxed_1015_ = lean_unbox(v_isZero_1003_);
v___x_21423__boxed_1016_ = lean_unbox(v___x_1004_);
v___x_21424__boxed_1017_ = lean_unbox(v___x_1005_);
v_res_1018_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_996_, v_dummy_997_, v___x_998_, v___x_999_, v___x_1000_, v_motive_1001_, v_zs1_1002_, v_isZero_boxed_1015_, v___x_21423__boxed_1016_, v___x_21424__boxed_1017_, v___x_1006_, v_j_1007_, v_zs2_1008_, v_ctorRet2_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_zs2_1008_);
lean_dec(v_j_1007_);
lean_dec(v___x_998_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1019_, lean_object* v___x_1020_, lean_object* v___x_1021_, lean_object* v_motive_1022_, uint8_t v_isZero_1023_, uint8_t v___x_1024_, uint8_t v___x_1025_, lean_object* v___x_1026_, lean_object* v_j_1027_, lean_object* v_a_1028_, lean_object* v_zs1_1029_, lean_object* v_ctorRet1_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
v___x_1036_ = lean_whnf(v_ctorRet1_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v_dummy_1039_; lean_object* v_nargs_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref(v___x_1036_);
lean_inc_ref(v___x_1019_);
v___x_1038_ = l_Lean_mkAppN(v___x_1019_, v_zs1_1029_);
v_dummy_1039_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1040_ = l_Lean_Expr_getAppNumArgs(v_a_1037_);
lean_inc(v_nargs_1040_);
v___x_1041_ = lean_mk_array(v_nargs_1040_, v_dummy_1039_);
v___x_1042_ = lean_nat_sub(v_nargs_1040_, v___x_1020_);
lean_dec(v_nargs_1040_);
v___x_1043_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1037_, v___x_1041_, v___x_1042_);
v___x_1044_ = lean_array_get_size(v___x_1043_);
lean_inc(v___x_1021_);
v___x_1045_ = l_Array_toSubarray___redArg(v___x_1043_, v___x_1021_, v___x_1044_);
v___x_1046_ = l_Subarray_copy___redArg(v___x_1045_);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_1038_);
v___x_1048_ = lean_box(v_isZero_1023_);
v___x_1049_ = lean_box(v___x_1024_);
v___x_1050_ = lean_box(v___x_1025_);
v___f_1051_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1051_, 0, v___x_1019_);
lean_closure_set(v___f_1051_, 1, v_dummy_1039_);
lean_closure_set(v___f_1051_, 2, v___x_1020_);
lean_closure_set(v___f_1051_, 3, v___x_1021_);
lean_closure_set(v___f_1051_, 4, v___x_1047_);
lean_closure_set(v___f_1051_, 5, v_motive_1022_);
lean_closure_set(v___f_1051_, 6, v_zs1_1029_);
lean_closure_set(v___f_1051_, 7, v___x_1048_);
lean_closure_set(v___f_1051_, 8, v___x_1049_);
lean_closure_set(v___f_1051_, 9, v___x_1050_);
lean_closure_set(v___f_1051_, 10, v___x_1026_);
lean_closure_set(v___f_1051_, 11, v_j_1027_);
v___x_1052_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1028_, v___f_1051_, v_isZero_1023_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v___x_1052_;
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_zs1_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_j_1027_);
lean_dec(v___x_1026_);
lean_dec_ref(v_motive_1022_);
lean_dec(v___x_1021_);
lean_dec(v___x_1020_);
lean_dec_ref(v___x_1019_);
v_a_1053_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1036_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1036_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1061_ = _args[0];
lean_object* v___x_1062_ = _args[1];
lean_object* v___x_1063_ = _args[2];
lean_object* v_motive_1064_ = _args[3];
lean_object* v_isZero_1065_ = _args[4];
lean_object* v___x_1066_ = _args[5];
lean_object* v___x_1067_ = _args[6];
lean_object* v___x_1068_ = _args[7];
lean_object* v_j_1069_ = _args[8];
lean_object* v_a_1070_ = _args[9];
lean_object* v_zs1_1071_ = _args[10];
lean_object* v_ctorRet1_1072_ = _args[11];
lean_object* v___y_1073_ = _args[12];
lean_object* v___y_1074_ = _args[13];
lean_object* v___y_1075_ = _args[14];
lean_object* v___y_1076_ = _args[15];
lean_object* v___y_1077_ = _args[16];
_start:
{
uint8_t v_isZero_boxed_1078_; uint8_t v___x_21561__boxed_1079_; uint8_t v___x_21562__boxed_1080_; lean_object* v_res_1081_; 
v_isZero_boxed_1078_ = lean_unbox(v_isZero_1065_);
v___x_21561__boxed_1079_ = lean_unbox(v___x_1066_);
v___x_21562__boxed_1080_ = lean_unbox(v___x_1067_);
v_res_1081_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1061_, v___x_1062_, v___x_1063_, v_motive_1064_, v_isZero_boxed_1078_, v___x_21561__boxed_1079_, v___x_21562__boxed_1080_, v___x_1068_, v_j_1069_, v_a_1070_, v_zs1_1071_, v_ctorRet1_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1082_, lean_object* v_params_1083_, lean_object* v___x_1084_, lean_object* v_motive_1085_, lean_object* v_as_1086_, lean_object* v_i_1087_, lean_object* v_j_1088_, lean_object* v_bs_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_zero_1095_; uint8_t v_isZero_1096_; 
v_zero_1095_ = lean_unsigned_to_nat(0u);
v_isZero_1096_ = lean_nat_dec_eq(v_i_1087_, v_zero_1095_);
if (v_isZero_1096_ == 1)
{
lean_object* v___x_1097_; 
lean_dec(v_j_1088_);
lean_dec(v_i_1087_);
lean_dec_ref(v_motive_1085_);
lean_dec(v___x_1084_);
lean_dec(v_tail_1082_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_bs_1089_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = lean_array_fget_borrowed(v_as_1086_, v_j_1088_);
lean_inc(v_tail_1082_);
lean_inc(v___x_1098_);
v___x_1099_ = l_Lean_mkConst(v___x_1098_, v_tail_1082_);
v___x_1100_ = l_Lean_mkAppN(v___x_1099_, v_params_1083_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1090_);
lean_inc_ref(v___x_1100_);
v___x_1101_ = lean_infer_type(v___x_1100_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; uint8_t v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
v___x_1103_ = 1;
v___x_1104_ = 1;
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_box(v_isZero_1096_);
v___x_1107_ = lean_box(v___x_1103_);
v___x_1108_ = lean_box(v___x_1104_);
lean_inc(v_a_1102_);
lean_inc(v_j_1088_);
lean_inc(v___x_1098_);
lean_inc_ref(v_motive_1085_);
lean_inc(v___x_1084_);
v___f_1109_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1109_, 0, v___x_1100_);
lean_closure_set(v___f_1109_, 1, v___x_1105_);
lean_closure_set(v___f_1109_, 2, v___x_1084_);
lean_closure_set(v___f_1109_, 3, v_motive_1085_);
lean_closure_set(v___f_1109_, 4, v___x_1106_);
lean_closure_set(v___f_1109_, 5, v___x_1107_);
lean_closure_set(v___f_1109_, 6, v___x_1108_);
lean_closure_set(v___f_1109_, 7, v___x_1098_);
lean_closure_set(v___f_1109_, 8, v_j_1088_);
lean_closure_set(v___f_1109_, 9, v_a_1102_);
v___x_1110_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1102_, v___f_1109_, v_isZero_1096_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v_n_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v_n_1112_ = lean_nat_sub(v_i_1087_, v___x_1105_);
lean_dec(v_i_1087_);
v___x_1113_ = lean_nat_add(v_j_1088_, v___x_1105_);
lean_dec(v_j_1088_);
v___x_1114_ = lean_array_push(v_bs_1089_, v_a_1111_);
v_i_1087_ = v_n_1112_;
v_j_1088_ = v___x_1113_;
v_bs_1089_ = v___x_1114_;
goto _start;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_bs_1089_);
lean_dec(v_j_1088_);
lean_dec(v_i_1087_);
lean_dec_ref(v_motive_1085_);
lean_dec(v___x_1084_);
lean_dec(v_tail_1082_);
v_a_1116_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1110_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1110_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_bs_1089_);
lean_dec(v_j_1088_);
lean_dec(v_i_1087_);
lean_dec_ref(v_motive_1085_);
lean_dec(v___x_1084_);
lean_dec(v_tail_1082_);
v_a_1124_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1101_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1101_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1132_, lean_object* v_params_1133_, lean_object* v___x_1134_, lean_object* v_motive_1135_, lean_object* v_as_1136_, lean_object* v_i_1137_, lean_object* v_j_1138_, lean_object* v_bs_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1132_, v_params_1133_, v___x_1134_, v_motive_1135_, v_as_1136_, v_i_1137_, v_j_1138_, v_bs_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec_ref(v_as_1136_);
lean_dec_ref(v_params_1133_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0(lean_object* v___x_1146_, lean_object* v_a_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_20242__overap_1154_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_instInhabitedExpr;
v___x_20242__overap_1154_ = l_instInhabitedOfMonad___redArg(v___x_1146_, v___x_1153_);
lean_inc(v___y_1151_);
lean_inc_ref(v___y_1150_);
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
v___x_1155_ = lean_apply_5(v___x_20242__overap_1154_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, lean_box(0));
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0___boxed(lean_object* v___x_1156_, lean_object* v_a_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0(v___x_1156_, v_a_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_instMonadEIO(lean_box(0));
return v___x_1164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__0);
v___x_1166_ = l_StateRefT_x27_instMonad___redArg(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1___boxed(lean_object* v_acc_1171_, lean_object* v_declInfos_1172_, lean_object* v_k_1173_, lean_object* v_kind_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_kind_boxed_1181_; lean_object* v_res_1182_; 
v_kind_boxed_1181_ = lean_unbox(v_kind_1174_);
v_res_1182_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1(v_acc_1171_, v_declInfos_1172_, v_k_1173_, v_kind_boxed_1181_, v_x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(lean_object* v_declInfos_1183_, lean_object* v_k_1184_, uint8_t v_kind_1185_, lean_object* v_acc_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_toApplicative_1193_; lean_object* v_toFunctor_1194_; lean_object* v_toSeq_1195_; lean_object* v_toSeqLeft_1196_; lean_object* v_toSeqRight_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_toApplicative_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1266_; 
v___x_1192_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__1);
v_toApplicative_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_ref(v_toApplicative_1193_);
v_toFunctor_1194_ = lean_ctor_get(v_toApplicative_1193_, 0);
lean_inc_ref(v_toFunctor_1194_);
v_toSeq_1195_ = lean_ctor_get(v_toApplicative_1193_, 2);
lean_inc(v_toSeq_1195_);
v_toSeqLeft_1196_ = lean_ctor_get(v_toApplicative_1193_, 3);
lean_inc(v_toSeqLeft_1196_);
v_toSeqRight_1197_ = lean_ctor_get(v_toApplicative_1193_, 4);
lean_inc(v_toSeqRight_1197_);
lean_dec_ref(v_toApplicative_1193_);
v___f_1198_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__2));
v___f_1199_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__3));
lean_inc_ref(v_toFunctor_1194_);
v___f_1200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1200_, 0, v_toFunctor_1194_);
v___f_1201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1201_, 0, v_toFunctor_1194_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___f_1200_);
lean_ctor_set(v___x_1202_, 1, v___f_1201_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toSeqRight_1197_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toSeqLeft_1196_);
v___f_1205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1205_, 0, v_toSeq_1195_);
v___x_1206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1202_);
lean_ctor_set(v___x_1206_, 1, v___f_1198_);
lean_ctor_set(v___x_1206_, 2, v___f_1205_);
lean_ctor_set(v___x_1206_, 3, v___f_1204_);
lean_ctor_set(v___x_1206_, 4, v___f_1203_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v___f_1199_);
v___x_1208_ = l_StateRefT_x27_instMonad___redArg(v___x_1207_);
v_toApplicative_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1208_, 1);
lean_dec(v_unused_1267_);
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1266_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_toApplicative_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1266_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_toFunctor_1213_; lean_object* v_toSeq_1214_; lean_object* v_toSeqLeft_1215_; lean_object* v_toSeqRight_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1264_; 
v_toFunctor_1213_ = lean_ctor_get(v_toApplicative_1209_, 0);
v_toSeq_1214_ = lean_ctor_get(v_toApplicative_1209_, 2);
v_toSeqLeft_1215_ = lean_ctor_get(v_toApplicative_1209_, 3);
v_toSeqRight_1216_ = lean_ctor_get(v_toApplicative_1209_, 4);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_toApplicative_1209_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v_toApplicative_1209_, 1);
lean_dec(v_unused_1265_);
v___x_1218_ = v_toApplicative_1209_;
v_isShared_1219_ = v_isSharedCheck_1264_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_toSeqRight_1216_);
lean_inc(v_toSeqLeft_1215_);
lean_inc(v_toSeq_1214_);
lean_inc(v_toFunctor_1213_);
lean_dec(v_toApplicative_1209_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1264_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___x_1229_; 
v___f_1220_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__4));
v___f_1221_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___closed__5));
lean_inc_ref(v_toFunctor_1213_);
v___f_1222_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1222_, 0, v_toFunctor_1213_);
v___f_1223_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1223_, 0, v_toFunctor_1213_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___f_1222_);
lean_ctor_set(v___x_1224_, 1, v___f_1223_);
v___f_1225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1225_, 0, v_toSeqRight_1216_);
v___f_1226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1226_, 0, v_toSeqLeft_1215_);
v___f_1227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1227_, 0, v_toSeq_1214_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 4, v___f_1225_);
lean_ctor_set(v___x_1218_, 3, v___f_1226_);
lean_ctor_set(v___x_1218_, 2, v___f_1227_);
lean_ctor_set(v___x_1218_, 1, v___f_1220_);
lean_ctor_set(v___x_1218_, 0, v___x_1224_);
v___x_1229_ = v___x_1218_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___f_1220_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v___f_1227_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v___f_1226_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v___f_1225_);
v___x_1229_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___f_1221_);
lean_ctor_set(v___x_1211_, 0, v___x_1229_);
v___x_1231_ = v___x_1211_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___f_1221_);
v___x_1231_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1232_ = lean_array_get_size(v_acc_1186_);
v___x_1233_ = lean_array_get_size(v_declInfos_1183_);
v___x_1234_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_declInfos_1183_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
v___x_1235_ = lean_apply_6(v_k_1184_, v_acc_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
return v___x_1235_;
}
else
{
lean_object* v___f_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_snd_1244_; lean_object* v_fst_1245_; lean_object* v_fst_1246_; lean_object* v_snd_1247_; lean_object* v___x_1248_; 
v___f_1236_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1236_, 0, v___x_1231_);
v___x_1237_ = lean_box(0);
v___x_1238_ = 0;
v___f_1239_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1239_, 0, v___f_1236_);
v___x_1240_ = lean_box(v___x_1238_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v___f_1239_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1237_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_array_get_borrowed(v___x_1242_, v_declInfos_1183_, v___x_1232_);
lean_dec_ref(v___x_1242_);
v_snd_1244_ = lean_ctor_get(v___x_1243_, 1);
v_fst_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_fst_1245_);
v_fst_1246_ = lean_ctor_get(v_snd_1244_, 0);
lean_inc(v_fst_1246_);
v_snd_1247_ = lean_ctor_get(v_snd_1244_, 1);
lean_inc(v_snd_1247_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc_ref(v_acc_1186_);
v___x_1248_ = lean_apply_6(v_snd_1247_, v_acc_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, lean_box(0));
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v___f_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref(v___x_1248_);
v___x_1250_ = lean_box(v_kind_1185_);
v___f_1251_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1251_, 0, v_acc_1186_);
lean_closure_set(v___f_1251_, 1, v_declInfos_1183_);
lean_closure_set(v___f_1251_, 2, v_k_1184_);
lean_closure_set(v___f_1251_, 3, v___x_1250_);
v___x_1252_ = lean_unbox(v_fst_1246_);
lean_dec(v_fst_1246_);
v___x_1253_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1245_, v___x_1252_, v_a_1249_, v___f_1251_, v_kind_1185_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_fst_1246_);
lean_dec(v_fst_1245_);
lean_dec_ref(v_acc_1186_);
lean_dec_ref(v_k_1184_);
lean_dec_ref(v_declInfos_1183_);
v_a_1254_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1248_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1248_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___lam__1(lean_object* v_acc_1268_, lean_object* v_declInfos_1269_, lean_object* v_k_1270_, uint8_t v_kind_1271_, lean_object* v_x_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_array_push(v_acc_1268_, v_x_1272_);
v___x_1279_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(v_declInfos_1269_, v_k_1270_, v_kind_1271_, v___x_1278_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg___boxed(lean_object* v_declInfos_1280_, lean_object* v_k_1281_, lean_object* v_kind_1282_, lean_object* v_acc_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v_kind_boxed_1289_; lean_object* v_res_1290_; 
v_kind_boxed_1289_ = lean_unbox(v_kind_1282_);
v_res_1290_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(v_declInfos_1280_, v_k_1281_, v_kind_boxed_1289_, v_acc_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(lean_object* v_inst_1293_, lean_object* v_declInfos_1294_, lean_object* v_k_1295_, uint8_t v_kind_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___closed__0));
v___x_1303_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(v_declInfos_1294_, v_k_1295_, v_kind_1296_, v___x_1302_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg___boxed(lean_object* v_inst_1304_, lean_object* v_declInfos_1305_, lean_object* v_k_1306_, lean_object* v_kind_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v_kind_boxed_1313_; lean_object* v_res_1314_; 
v_kind_boxed_1313_ = lean_unbox(v_kind_1307_);
v_res_1314_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(v_inst_1304_, v_declInfos_1305_, v_k_1306_, v_kind_boxed_1313_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v_inst_1304_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_bs_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_lt(v_i_1316_, v_sz_1315_);
if (v___x_1318_ == 0)
{
return v_bs_1317_;
}
else
{
lean_object* v_v_1319_; lean_object* v_fst_1320_; lean_object* v_snd_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1337_; 
v_v_1319_ = lean_array_uget(v_bs_1317_, v_i_1316_);
v_fst_1320_ = lean_ctor_get(v_v_1319_, 0);
v_snd_1321_ = lean_ctor_get(v_v_1319_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_v_1319_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1323_ = v_v_1319_;
v_isShared_1324_ = v_isSharedCheck_1337_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_snd_1321_);
lean_inc(v_fst_1320_);
lean_dec(v_v_1319_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1337_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v_bs_x27_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1325_ = lean_unsigned_to_nat(0u);
v_bs_x27_1326_ = lean_array_uset(v_bs_1317_, v_i_1316_, v___x_1325_);
v___x_1327_ = 0;
v___x_1328_ = lean_box(v___x_1327_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1328_);
v___x_1330_ = v___x_1323_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_snd_1321_);
v___x_1330_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_fst_1320_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_add(v_i_1316_, v___x_1332_);
v___x_1334_ = lean_array_uset(v_bs_x27_1326_, v_i_1316_, v___x_1331_);
v_i_1316_ = v___x_1333_;
v_bs_1317_ = v___x_1334_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1338_, lean_object* v_i_1339_, lean_object* v_bs_1340_){
_start:
{
size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1338_);
lean_dec(v_sz_1338_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1339_);
lean_dec(v_i_1339_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1341_, v_i_boxed_1342_, v_bs_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(lean_object* v_inst_1344_, lean_object* v_declInfos_1345_, lean_object* v_k_1346_, uint8_t v_kind_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
size_t v_sz_1353_; size_t v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_sz_1353_ = lean_array_size(v_declInfos_1345_);
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1353_, v___x_1354_, v_declInfos_1345_);
v___x_1356_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(v_inst_1344_, v___x_1355_, v_k_1346_, v_kind_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg___boxed(lean_object* v_inst_1357_, lean_object* v_declInfos_1358_, lean_object* v_k_1359_, lean_object* v_kind_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v_kind_boxed_1366_; lean_object* v_res_1367_; 
v_kind_boxed_1366_ = lean_unbox(v_kind_1360_);
v_res_1367_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(v_inst_1357_, v_declInfos_1358_, v_k_1359_, v_kind_boxed_1366_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v_inst_1357_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v_snd_1368_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_1376_, v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec_ref(v_x_1377_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_1384_, size_t v_i_1385_, lean_object* v_bs_1386_){
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
lean_object* v_v_1388_; lean_object* v_fst_1389_; lean_object* v_snd_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1404_; 
v_v_1388_ = lean_array_uget(v_bs_1386_, v_i_1385_);
v_fst_1389_ = lean_ctor_get(v_v_1388_, 0);
v_snd_1390_ = lean_ctor_get(v_v_1388_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_v_1388_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1392_ = v_v_1388_;
v_isShared_1393_ = v_isSharedCheck_1404_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1390_);
lean_inc(v_fst_1389_);
lean_dec(v_v_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1404_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v_bs_x27_1395_; lean_object* v___f_1396_; lean_object* v___x_1398_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v_bs_x27_1395_ = lean_array_uset(v_bs_1386_, v_i_1385_, v___x_1394_);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1396_, 0, v_snd_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v___f_1396_);
v___x_1398_ = v___x_1392_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_fst_1389_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___f_1396_);
v___x_1398_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = ((size_t)1ULL);
v___x_1400_ = lean_usize_add(v_i_1385_, v___x_1399_);
v___x_1401_ = lean_array_uset(v_bs_x27_1395_, v_i_1385_, v___x_1398_);
v_i_1385_ = v___x_1400_;
v_bs_1386_ = v___x_1401_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_1405_, lean_object* v_i_1406_, lean_object* v_bs_1407_){
_start:
{
size_t v_sz_boxed_1408_; size_t v_i_boxed_1409_; lean_object* v_res_1410_; 
v_sz_boxed_1408_ = lean_unbox_usize(v_sz_1405_);
lean_dec(v_sz_1405_);
v_i_boxed_1409_ = lean_unbox_usize(v_i_1406_);
lean_dec(v_i_1406_);
v_res_1410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_1408_, v_i_boxed_1409_, v_bs_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(lean_object* v_inst_1411_, lean_object* v_declInfos_1412_, lean_object* v_k_1413_, uint8_t v_kind_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
size_t v_sz_1420_; size_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v_sz_1420_ = lean_array_size(v_declInfos_1412_);
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1420_, v___x_1421_, v_declInfos_1412_);
v___x_1423_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(v_inst_1411_, v___x_1422_, v_k_1413_, v_kind_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg___boxed(lean_object* v_inst_1424_, lean_object* v_declInfos_1425_, lean_object* v_k_1426_, lean_object* v_kind_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_kind_boxed_1433_; lean_object* v_res_1434_; 
v_kind_boxed_1433_ = lean_unbox(v_kind_1427_);
v_res_1434_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(v_inst_1424_, v_declInfos_1425_, v_k_1426_, v_kind_boxed_1433_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v_inst_1424_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1435_, lean_object* v_tail_1436_, lean_object* v_params_1437_, lean_object* v_numParams_1438_, lean_object* v_indName_1439_, lean_object* v_ism1_1440_, lean_object* v_ism2_1441_, lean_object* v___x_1442_, uint8_t v___x_1443_, uint8_t v___x_1444_, uint8_t v___x_1445_, lean_object* v_val_1446_, lean_object* v___x_1447_, lean_object* v___x_1448_, lean_object* v_name_1449_, lean_object* v___x_1450_, lean_object* v___x_1451_, lean_object* v_motive_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1458_ = lean_array_mk(v_ctors_1435_);
v___x_1459_ = lean_array_get_size(v___x_1458_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1459_);
lean_inc_ref(v_motive_1452_);
lean_inc(v_numParams_1438_);
lean_inc(v_tail_1436_);
v___x_1462_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1436_, v_params_1437_, v_numParams_1438_, v_motive_1452_, v___x_1458_, v___x_1459_, v___x_1460_, v___x_1461_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___f_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = lean_box(v___x_1443_);
v___x_1465_ = lean_box(v___x_1444_);
v___x_1466_ = lean_box(v___x_1445_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1467_, 0, v_indName_1439_);
lean_closure_set(v___f_1467_, 1, v_tail_1436_);
lean_closure_set(v___f_1467_, 2, v_params_1437_);
lean_closure_set(v___f_1467_, 3, v_ism1_1440_);
lean_closure_set(v___f_1467_, 4, v_ism2_1441_);
lean_closure_set(v___f_1467_, 5, v_motive_1452_);
lean_closure_set(v___f_1467_, 6, v___x_1442_);
lean_closure_set(v___f_1467_, 7, v___x_1464_);
lean_closure_set(v___f_1467_, 8, v___x_1465_);
lean_closure_set(v___f_1467_, 9, v___x_1466_);
lean_closure_set(v___f_1467_, 10, v___x_1458_);
lean_closure_set(v___f_1467_, 11, v_numParams_1438_);
lean_closure_set(v___f_1467_, 12, v_val_1446_);
lean_closure_set(v___f_1467_, 13, v___x_1447_);
lean_closure_set(v___f_1467_, 14, v___x_1448_);
lean_closure_set(v___f_1467_, 15, v_name_1449_);
lean_closure_set(v___f_1467_, 16, v___x_1450_);
v___x_1468_ = 0;
v___x_1469_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(v___x_1451_, v_a_1463_, v___f_1467_, v___x_1468_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1469_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec_ref(v___x_1458_);
lean_dec_ref(v_motive_1452_);
lean_dec(v___x_1450_);
lean_dec(v_name_1449_);
lean_dec(v___x_1448_);
lean_dec(v___x_1447_);
lean_dec_ref(v_val_1446_);
lean_dec_ref(v___x_1442_);
lean_dec_ref(v_ism2_1441_);
lean_dec_ref(v_ism1_1440_);
lean_dec(v_indName_1439_);
lean_dec(v_numParams_1438_);
lean_dec_ref(v_params_1437_);
lean_dec(v_tail_1436_);
v_a_1470_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1462_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1462_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1478_ = _args[0];
lean_object* v_tail_1479_ = _args[1];
lean_object* v_params_1480_ = _args[2];
lean_object* v_numParams_1481_ = _args[3];
lean_object* v_indName_1482_ = _args[4];
lean_object* v_ism1_1483_ = _args[5];
lean_object* v_ism2_1484_ = _args[6];
lean_object* v___x_1485_ = _args[7];
lean_object* v___x_1486_ = _args[8];
lean_object* v___x_1487_ = _args[9];
lean_object* v___x_1488_ = _args[10];
lean_object* v_val_1489_ = _args[11];
lean_object* v___x_1490_ = _args[12];
lean_object* v___x_1491_ = _args[13];
lean_object* v_name_1492_ = _args[14];
lean_object* v___x_1493_ = _args[15];
lean_object* v___x_1494_ = _args[16];
lean_object* v_motive_1495_ = _args[17];
lean_object* v___y_1496_ = _args[18];
lean_object* v___y_1497_ = _args[19];
lean_object* v___y_1498_ = _args[20];
lean_object* v___y_1499_ = _args[21];
lean_object* v___y_1500_ = _args[22];
_start:
{
uint8_t v___x_22110__boxed_1501_; uint8_t v___x_22111__boxed_1502_; uint8_t v___x_22112__boxed_1503_; lean_object* v_res_1504_; 
v___x_22110__boxed_1501_ = lean_unbox(v___x_1486_);
v___x_22111__boxed_1502_ = lean_unbox(v___x_1487_);
v___x_22112__boxed_1503_ = lean_unbox(v___x_1488_);
v_res_1504_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1478_, v_tail_1479_, v_params_1480_, v_numParams_1481_, v_indName_1482_, v_ism1_1483_, v_ism2_1484_, v___x_1485_, v___x_22110__boxed_1501_, v___x_22111__boxed_1502_, v___x_22112__boxed_1503_, v_val_1489_, v___x_1490_, v___x_1491_, v_name_1492_, v___x_1493_, v___x_1494_, v_motive_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec_ref(v___x_1494_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1508_, lean_object* v_head_1509_, lean_object* v_ctors_1510_, lean_object* v_tail_1511_, lean_object* v_params_1512_, lean_object* v_numParams_1513_, lean_object* v_indName_1514_, lean_object* v_val_1515_, lean_object* v___x_1516_, lean_object* v___x_1517_, lean_object* v_name_1518_, lean_object* v___x_1519_, lean_object* v___x_1520_, lean_object* v_ism2_1521_, lean_object* v_x_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; uint8_t v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; 
lean_inc_ref(v_ism1_1508_);
v___x_1528_ = l_Array_append___redArg(v_ism1_1508_, v_ism2_1521_);
v___x_1529_ = l_Lean_mkSort(v_head_1509_);
v___x_1530_ = 0;
v___x_1531_ = 1;
v___x_1532_ = 1;
v___x_1533_ = l_Lean_Meta_mkForallFVars(v___x_1528_, v___x_1529_, v___x_1530_, v___x_1531_, v___x_1531_, v___x_1532_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___f_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v___x_1533_);
v___x_1535_ = lean_box(v___x_1530_);
v___x_1536_ = lean_box(v___x_1531_);
v___x_1537_ = lean_box(v___x_1532_);
v___f_1538_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 23, 17);
lean_closure_set(v___f_1538_, 0, v_ctors_1510_);
lean_closure_set(v___f_1538_, 1, v_tail_1511_);
lean_closure_set(v___f_1538_, 2, v_params_1512_);
lean_closure_set(v___f_1538_, 3, v_numParams_1513_);
lean_closure_set(v___f_1538_, 4, v_indName_1514_);
lean_closure_set(v___f_1538_, 5, v_ism1_1508_);
lean_closure_set(v___f_1538_, 6, v_ism2_1521_);
lean_closure_set(v___f_1538_, 7, v___x_1528_);
lean_closure_set(v___f_1538_, 8, v___x_1535_);
lean_closure_set(v___f_1538_, 9, v___x_1536_);
lean_closure_set(v___f_1538_, 10, v___x_1537_);
lean_closure_set(v___f_1538_, 11, v_val_1515_);
lean_closure_set(v___f_1538_, 12, v___x_1516_);
lean_closure_set(v___f_1538_, 13, v___x_1517_);
lean_closure_set(v___f_1538_, 14, v_name_1518_);
lean_closure_set(v___f_1538_, 15, v___x_1519_);
lean_closure_set(v___f_1538_, 16, v___x_1520_);
v___x_1539_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1540_ = 0;
v___x_1541_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1539_, v___x_1532_, v_a_1534_, v___f_1538_, v___x_1540_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
return v___x_1541_;
}
else
{
lean_dec_ref(v___x_1528_);
lean_dec_ref(v_ism2_1521_);
lean_dec_ref(v___x_1520_);
lean_dec(v___x_1519_);
lean_dec(v_name_1518_);
lean_dec(v___x_1517_);
lean_dec(v___x_1516_);
lean_dec_ref(v_val_1515_);
lean_dec(v_indName_1514_);
lean_dec(v_numParams_1513_);
lean_dec_ref(v_params_1512_);
lean_dec(v_tail_1511_);
lean_dec(v_ctors_1510_);
lean_dec_ref(v_ism1_1508_);
return v___x_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1542_ = _args[0];
lean_object* v_head_1543_ = _args[1];
lean_object* v_ctors_1544_ = _args[2];
lean_object* v_tail_1545_ = _args[3];
lean_object* v_params_1546_ = _args[4];
lean_object* v_numParams_1547_ = _args[5];
lean_object* v_indName_1548_ = _args[6];
lean_object* v_val_1549_ = _args[7];
lean_object* v___x_1550_ = _args[8];
lean_object* v___x_1551_ = _args[9];
lean_object* v_name_1552_ = _args[10];
lean_object* v___x_1553_ = _args[11];
lean_object* v___x_1554_ = _args[12];
lean_object* v_ism2_1555_ = _args[13];
lean_object* v_x_1556_ = _args[14];
lean_object* v___y_1557_ = _args[15];
lean_object* v___y_1558_ = _args[16];
lean_object* v___y_1559_ = _args[17];
lean_object* v___y_1560_ = _args[18];
lean_object* v___y_1561_ = _args[19];
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1542_, v_head_1543_, v_ctors_1544_, v_tail_1545_, v_params_1546_, v_numParams_1547_, v_indName_1548_, v_val_1549_, v___x_1550_, v___x_1551_, v_name_1552_, v___x_1553_, v___x_1554_, v_ism2_1555_, v_x_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec_ref(v_x_1556_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1563_, lean_object* v_ctors_1564_, lean_object* v_tail_1565_, lean_object* v_params_1566_, lean_object* v_numParams_1567_, lean_object* v_indName_1568_, lean_object* v_val_1569_, lean_object* v___x_1570_, lean_object* v___x_1571_, lean_object* v_name_1572_, lean_object* v___x_1573_, lean_object* v___x_1574_, lean_object* v_t_1575_, lean_object* v___x_1576_, lean_object* v_ism1_1577_, lean_object* v_x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___f_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; 
v___f_1584_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 20, 13);
lean_closure_set(v___f_1584_, 0, v_ism1_1577_);
lean_closure_set(v___f_1584_, 1, v_head_1563_);
lean_closure_set(v___f_1584_, 2, v_ctors_1564_);
lean_closure_set(v___f_1584_, 3, v_tail_1565_);
lean_closure_set(v___f_1584_, 4, v_params_1566_);
lean_closure_set(v___f_1584_, 5, v_numParams_1567_);
lean_closure_set(v___f_1584_, 6, v_indName_1568_);
lean_closure_set(v___f_1584_, 7, v_val_1569_);
lean_closure_set(v___f_1584_, 8, v___x_1570_);
lean_closure_set(v___f_1584_, 9, v___x_1571_);
lean_closure_set(v___f_1584_, 10, v_name_1572_);
lean_closure_set(v___f_1584_, 11, v___x_1573_);
lean_closure_set(v___f_1584_, 12, v___x_1574_);
v___x_1585_ = 0;
v___x_1586_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1575_, v___x_1576_, v___f_1584_, v___x_1585_, v___x_1585_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1587_ = _args[0];
lean_object* v_ctors_1588_ = _args[1];
lean_object* v_tail_1589_ = _args[2];
lean_object* v_params_1590_ = _args[3];
lean_object* v_numParams_1591_ = _args[4];
lean_object* v_indName_1592_ = _args[5];
lean_object* v_val_1593_ = _args[6];
lean_object* v___x_1594_ = _args[7];
lean_object* v___x_1595_ = _args[8];
lean_object* v_name_1596_ = _args[9];
lean_object* v___x_1597_ = _args[10];
lean_object* v___x_1598_ = _args[11];
lean_object* v_t_1599_ = _args[12];
lean_object* v___x_1600_ = _args[13];
lean_object* v_ism1_1601_ = _args[14];
lean_object* v_x_1602_ = _args[15];
lean_object* v___y_1603_ = _args[16];
lean_object* v___y_1604_ = _args[17];
lean_object* v___y_1605_ = _args[18];
lean_object* v___y_1606_ = _args[19];
lean_object* v___y_1607_ = _args[20];
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1587_, v_ctors_1588_, v_tail_1589_, v_params_1590_, v_numParams_1591_, v_indName_1592_, v_val_1593_, v___x_1594_, v___x_1595_, v_name_1596_, v___x_1597_, v___x_1598_, v_t_1599_, v___x_1600_, v_ism1_1601_, v_x_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_x_1602_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1609_, lean_object* v___x_1610_, lean_object* v_head_1611_, lean_object* v_ctors_1612_, lean_object* v_tail_1613_, lean_object* v_params_1614_, lean_object* v_numParams_1615_, lean_object* v_indName_1616_, lean_object* v_val_1617_, lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v_name_1620_, lean_object* v___x_1621_, lean_object* v_x_1622_, lean_object* v_t_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___f_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1629_ = lean_nat_add(v_numIndices_1609_, v___x_1610_);
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_inc_ref(v___x_1630_);
lean_inc_ref(v_t_1623_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 21, 14);
lean_closure_set(v___f_1631_, 0, v_head_1611_);
lean_closure_set(v___f_1631_, 1, v_ctors_1612_);
lean_closure_set(v___f_1631_, 2, v_tail_1613_);
lean_closure_set(v___f_1631_, 3, v_params_1614_);
lean_closure_set(v___f_1631_, 4, v_numParams_1615_);
lean_closure_set(v___f_1631_, 5, v_indName_1616_);
lean_closure_set(v___f_1631_, 6, v_val_1617_);
lean_closure_set(v___f_1631_, 7, v___x_1618_);
lean_closure_set(v___f_1631_, 8, v___x_1619_);
lean_closure_set(v___f_1631_, 9, v_name_1620_);
lean_closure_set(v___f_1631_, 10, v___x_1610_);
lean_closure_set(v___f_1631_, 11, v___x_1621_);
lean_closure_set(v___f_1631_, 12, v_t_1623_);
lean_closure_set(v___f_1631_, 13, v___x_1630_);
v___x_1632_ = 0;
v___x_1633_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1623_, v___x_1630_, v___f_1631_, v___x_1632_, v___x_1632_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1634_ = _args[0];
lean_object* v___x_1635_ = _args[1];
lean_object* v_head_1636_ = _args[2];
lean_object* v_ctors_1637_ = _args[3];
lean_object* v_tail_1638_ = _args[4];
lean_object* v_params_1639_ = _args[5];
lean_object* v_numParams_1640_ = _args[6];
lean_object* v_indName_1641_ = _args[7];
lean_object* v_val_1642_ = _args[8];
lean_object* v___x_1643_ = _args[9];
lean_object* v___x_1644_ = _args[10];
lean_object* v_name_1645_ = _args[11];
lean_object* v___x_1646_ = _args[12];
lean_object* v_x_1647_ = _args[13];
lean_object* v_t_1648_ = _args[14];
lean_object* v___y_1649_ = _args[15];
lean_object* v___y_1650_ = _args[16];
lean_object* v___y_1651_ = _args[17];
lean_object* v___y_1652_ = _args[18];
lean_object* v___y_1653_ = _args[19];
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1634_, v___x_1635_, v_head_1636_, v_ctors_1637_, v_tail_1638_, v_params_1639_, v_numParams_1640_, v_indName_1641_, v_val_1642_, v___x_1643_, v___x_1644_, v_name_1645_, v___x_1646_, v_x_1647_, v_t_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec_ref(v_x_1647_);
lean_dec(v_numIndices_1634_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1657_, lean_object* v_head_1658_, lean_object* v_ctors_1659_, lean_object* v_tail_1660_, lean_object* v_numParams_1661_, lean_object* v_indName_1662_, lean_object* v_val_1663_, lean_object* v___x_1664_, lean_object* v___x_1665_, lean_object* v_name_1666_, lean_object* v___x_1667_, lean_object* v_params_1668_, lean_object* v_t_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; lean_object* v___f_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; 
v___x_1675_ = lean_unsigned_to_nat(1u);
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 20, 13);
lean_closure_set(v___f_1676_, 0, v_numIndices_1657_);
lean_closure_set(v___f_1676_, 1, v___x_1675_);
lean_closure_set(v___f_1676_, 2, v_head_1658_);
lean_closure_set(v___f_1676_, 3, v_ctors_1659_);
lean_closure_set(v___f_1676_, 4, v_tail_1660_);
lean_closure_set(v___f_1676_, 5, v_params_1668_);
lean_closure_set(v___f_1676_, 6, v_numParams_1661_);
lean_closure_set(v___f_1676_, 7, v_indName_1662_);
lean_closure_set(v___f_1676_, 8, v_val_1663_);
lean_closure_set(v___f_1676_, 9, v___x_1664_);
lean_closure_set(v___f_1676_, 10, v___x_1665_);
lean_closure_set(v___f_1676_, 11, v_name_1666_);
lean_closure_set(v___f_1676_, 12, v___x_1667_);
v___x_1677_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1678_ = 0;
v___x_1679_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1669_, v___x_1677_, v___f_1676_, v___x_1678_, v___x_1678_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1680_ = _args[0];
lean_object* v_head_1681_ = _args[1];
lean_object* v_ctors_1682_ = _args[2];
lean_object* v_tail_1683_ = _args[3];
lean_object* v_numParams_1684_ = _args[4];
lean_object* v_indName_1685_ = _args[5];
lean_object* v_val_1686_ = _args[6];
lean_object* v___x_1687_ = _args[7];
lean_object* v___x_1688_ = _args[8];
lean_object* v_name_1689_ = _args[9];
lean_object* v___x_1690_ = _args[10];
lean_object* v_params_1691_ = _args[11];
lean_object* v_t_1692_ = _args[12];
lean_object* v___y_1693_ = _args[13];
lean_object* v___y_1694_ = _args[14];
lean_object* v___y_1695_ = _args[15];
lean_object* v___y_1696_ = _args[16];
lean_object* v___y_1697_ = _args[17];
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1680_, v_head_1681_, v_ctors_1682_, v_tail_1683_, v_numParams_1684_, v_indName_1685_, v_val_1686_, v___x_1687_, v___x_1688_, v_name_1689_, v___x_1690_, v_params_1691_, v_t_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1699_, lean_object* v_declName_1700_, lean_object* v_levelParams_1701_, uint8_t v___x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc_ref(v_a_1699_);
v___x_1708_ = lean_infer_type(v_a_1699_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___x_1708_);
v___x_1710_ = lean_box(1);
v___x_1711_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1700_, v_levelParams_1701_, v_a_1709_, v_a_1699_, v___x_1710_, v___y_1706_);
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 1);
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_addDecl(v___x_1717_, v___x_1702_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v___x_1718_;
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v_levelParams_1701_);
lean_dec(v_declName_1700_);
lean_dec_ref(v_a_1699_);
v_a_1721_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1708_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1708_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1729_, lean_object* v_declName_1730_, lean_object* v_levelParams_1731_, lean_object* v___x_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v___x_22417__boxed_1738_; lean_object* v_res_1739_; 
v___x_22417__boxed_1738_ = lean_unbox(v___x_1732_);
v_res_1739_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1729_, v_declName_1730_, v_levelParams_1731_, v___x_22417__boxed_1738_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
if (lean_obj_tag(v_a_1740_) == 0)
{
lean_object* v___x_1742_; 
v___x_1742_ = l_List_reverse___redArg(v_a_1741_);
return v___x_1742_;
}
else
{
lean_object* v_head_1743_; lean_object* v_tail_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1753_; 
v_head_1743_ = lean_ctor_get(v_a_1740_, 0);
v_tail_1744_ = lean_ctor_get(v_a_1740_, 1);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_a_1740_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1746_ = v_a_1740_;
v_isShared_1747_ = v_isSharedCheck_1753_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_tail_1744_);
lean_inc(v_head_1743_);
lean_dec(v_a_1740_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1753_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = l_Lean_mkLevelParam(v_head_1743_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v_a_1741_);
lean_ctor_set(v___x_1746_, 0, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_a_1741_);
v___x_1750_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
v_a_1740_ = v_tail_1744_;
v_a_1741_ = v___x_1750_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; lean_object* v_env_1761_; lean_object* v___x_1762_; lean_object* v_mctx_1763_; lean_object* v_lctx_1764_; lean_object* v_options_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1760_ = lean_st_ref_get(v___y_1758_);
v_env_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc_ref(v_env_1761_);
lean_dec(v___x_1760_);
v___x_1762_ = lean_st_ref_get(v___y_1756_);
v_mctx_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc_ref(v_mctx_1763_);
lean_dec(v___x_1762_);
v_lctx_1764_ = lean_ctor_get(v___y_1755_, 2);
v_options_1765_ = lean_ctor_get(v___y_1757_, 2);
lean_inc_ref(v_options_1765_);
lean_inc_ref(v_lctx_1764_);
v___x_1766_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1766_, 0, v_env_1761_);
lean_ctor_set(v___x_1766_, 1, v_mctx_1763_);
lean_ctor_set(v___x_1766_, 2, v_lctx_1764_);
lean_ctor_set(v___x_1766_, 3, v_options_1765_);
v___x_1767_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v_msgData_1754_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_ref_1782_; lean_object* v___x_1783_; lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1792_; 
v_ref_1782_ = lean_ctor_get(v___y_1779_, 5);
v___x_1783_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_inc(v_ref_1782_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_ref_1782_);
lean_ctor_set(v___x_1788_, 1, v_a_1784_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 1);
lean_ctor_set(v___x_1786_, 0, v___x_1788_);
v___x_1790_ = v___x_1786_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1800_, lean_object* v_msg_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_fileName_1807_; lean_object* v_fileMap_1808_; lean_object* v_options_1809_; lean_object* v_currRecDepth_1810_; lean_object* v_maxRecDepth_1811_; lean_object* v_ref_1812_; lean_object* v_currNamespace_1813_; lean_object* v_openDecls_1814_; lean_object* v_initHeartbeats_1815_; lean_object* v_maxHeartbeats_1816_; lean_object* v_quotContext_1817_; lean_object* v_currMacroScope_1818_; uint8_t v_diag_1819_; lean_object* v_cancelTk_x3f_1820_; uint8_t v_suppressElabErrors_1821_; lean_object* v_inheritedTraceOptions_1822_; lean_object* v_ref_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_fileName_1807_ = lean_ctor_get(v___y_1804_, 0);
v_fileMap_1808_ = lean_ctor_get(v___y_1804_, 1);
v_options_1809_ = lean_ctor_get(v___y_1804_, 2);
v_currRecDepth_1810_ = lean_ctor_get(v___y_1804_, 3);
v_maxRecDepth_1811_ = lean_ctor_get(v___y_1804_, 4);
v_ref_1812_ = lean_ctor_get(v___y_1804_, 5);
v_currNamespace_1813_ = lean_ctor_get(v___y_1804_, 6);
v_openDecls_1814_ = lean_ctor_get(v___y_1804_, 7);
v_initHeartbeats_1815_ = lean_ctor_get(v___y_1804_, 8);
v_maxHeartbeats_1816_ = lean_ctor_get(v___y_1804_, 9);
v_quotContext_1817_ = lean_ctor_get(v___y_1804_, 10);
v_currMacroScope_1818_ = lean_ctor_get(v___y_1804_, 11);
v_diag_1819_ = lean_ctor_get_uint8(v___y_1804_, sizeof(void*)*14);
v_cancelTk_x3f_1820_ = lean_ctor_get(v___y_1804_, 12);
v_suppressElabErrors_1821_ = lean_ctor_get_uint8(v___y_1804_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1822_ = lean_ctor_get(v___y_1804_, 13);
v_ref_1823_ = l_Lean_replaceRef(v_ref_1800_, v_ref_1812_);
lean_inc_ref(v_inheritedTraceOptions_1822_);
lean_inc(v_cancelTk_x3f_1820_);
lean_inc(v_currMacroScope_1818_);
lean_inc(v_quotContext_1817_);
lean_inc(v_maxHeartbeats_1816_);
lean_inc(v_initHeartbeats_1815_);
lean_inc(v_openDecls_1814_);
lean_inc(v_currNamespace_1813_);
lean_inc(v_maxRecDepth_1811_);
lean_inc(v_currRecDepth_1810_);
lean_inc_ref(v_options_1809_);
lean_inc_ref(v_fileMap_1808_);
lean_inc_ref(v_fileName_1807_);
v___x_1824_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1824_, 0, v_fileName_1807_);
lean_ctor_set(v___x_1824_, 1, v_fileMap_1808_);
lean_ctor_set(v___x_1824_, 2, v_options_1809_);
lean_ctor_set(v___x_1824_, 3, v_currRecDepth_1810_);
lean_ctor_set(v___x_1824_, 4, v_maxRecDepth_1811_);
lean_ctor_set(v___x_1824_, 5, v_ref_1823_);
lean_ctor_set(v___x_1824_, 6, v_currNamespace_1813_);
lean_ctor_set(v___x_1824_, 7, v_openDecls_1814_);
lean_ctor_set(v___x_1824_, 8, v_initHeartbeats_1815_);
lean_ctor_set(v___x_1824_, 9, v_maxHeartbeats_1816_);
lean_ctor_set(v___x_1824_, 10, v_quotContext_1817_);
lean_ctor_set(v___x_1824_, 11, v_currMacroScope_1818_);
lean_ctor_set(v___x_1824_, 12, v_cancelTk_x3f_1820_);
lean_ctor_set(v___x_1824_, 13, v_inheritedTraceOptions_1822_);
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*14, v_diag_1819_);
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*14 + 1, v_suppressElabErrors_1821_);
v___x_1825_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1801_, v___y_1802_, v___y_1803_, v___x_1824_, v___y_1805_);
lean_dec_ref(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1826_, lean_object* v_msg_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1826_, v_msg_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v_ref_1826_);
return v_res_1833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
lean_ctor_set(v___x_1839_, 2, v___x_1838_);
lean_ctor_set(v___x_1839_, 3, v___x_1837_);
lean_ctor_set(v___x_1839_, 4, v___x_1837_);
lean_ctor_set(v___x_1839_, 5, v___x_1837_);
lean_ctor_set(v___x_1839_, 6, v___x_1837_);
lean_ctor_set(v___x_1839_, 7, v___x_1837_);
lean_ctor_set(v___x_1839_, 8, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_unsigned_to_nat(32u);
v___x_1841_ = lean_mk_empty_array_with_capacity(v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1843_ = ((size_t)5ULL);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_unsigned_to_nat(32u);
v___x_1846_ = lean_mk_empty_array_with_capacity(v___x_1845_);
v___x_1847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1848_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v___x_1846_);
lean_ctor_set(v___x_1848_, 2, v___x_1844_);
lean_ctor_set(v___x_1848_, 3, v___x_1844_);
lean_ctor_set_usize(v___x_1848_, 4, v___x_1843_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = lean_box(1);
v___x_1850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1850_);
lean_ctor_set(v___x_1852_, 2, v___x_1849_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6));
v___x_1855_ = l_Lean_stringToMessageData(v___x_1854_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8));
v___x_1858_ = l_Lean_stringToMessageData(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10));
v___x_1861_ = l_Lean_stringToMessageData(v___x_1860_);
return v___x_1861_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12));
v___x_1864_ = l_Lean_stringToMessageData(v___x_1863_);
return v___x_1864_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14));
v___x_1867_ = l_Lean_stringToMessageData(v___x_1866_);
return v___x_1867_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16));
v___x_1870_ = l_Lean_stringToMessageData(v___x_1869_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18));
v___x_1873_ = l_Lean_stringToMessageData(v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1874_, lean_object* v_declHint_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v_env_1879_; uint8_t v___x_1880_; 
v___x_1878_ = lean_st_ref_get(v___y_1876_);
v_env_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc_ref(v_env_1879_);
lean_dec(v___x_1878_);
v___x_1880_ = l_Lean_Name_isAnonymous(v_declHint_1875_);
if (v___x_1880_ == 0)
{
uint8_t v_isExporting_1881_; 
v_isExporting_1881_ = lean_ctor_get_uint8(v_env_1879_, sizeof(void*)*8);
if (v_isExporting_1881_ == 0)
{
lean_object* v___x_1882_; 
lean_dec_ref(v_env_1879_);
lean_dec(v_declHint_1875_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_msg_1874_);
return v___x_1882_;
}
else
{
lean_object* v___x_1883_; uint8_t v___x_1884_; 
lean_inc_ref(v_env_1879_);
v___x_1883_ = l_Lean_Environment_setExporting(v_env_1879_, v___x_1880_);
lean_inc(v_declHint_1875_);
lean_inc_ref(v___x_1883_);
v___x_1884_ = l_Lean_Environment_contains(v___x_1883_, v_declHint_1875_, v_isExporting_1881_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; 
lean_dec_ref(v___x_1883_);
lean_dec_ref(v_env_1879_);
lean_dec(v_declHint_1875_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v_msg_1874_);
return v___x_1885_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_c_1891_; lean_object* v___x_1892_; 
v___x_1886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1888_ = l_Lean_Options_empty;
v___x_1889_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1883_);
lean_ctor_set(v___x_1889_, 1, v___x_1886_);
lean_ctor_set(v___x_1889_, 2, v___x_1887_);
lean_ctor_set(v___x_1889_, 3, v___x_1888_);
lean_inc(v_declHint_1875_);
v___x_1890_ = l_Lean_MessageData_ofConstName(v_declHint_1875_, v___x_1880_);
v_c_1891_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1891_, 0, v___x_1889_);
lean_ctor_set(v_c_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1879_, v_declHint_1875_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec_ref(v_env_1879_);
lean_dec(v_declHint_1875_);
v___x_1893_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v_c_1891_);
v___x_1895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = l_Lean_MessageData_note(v___x_1896_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_msg_1874_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
else
{
lean_object* v_val_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1935_; 
v_val_1900_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1902_ = v___x_1892_;
v_isShared_1903_ = v_isSharedCheck_1935_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_val_1900_);
lean_dec(v___x_1892_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1935_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_mod_1907_; uint8_t v___x_1908_; 
v___x_1904_ = lean_box(0);
v___x_1905_ = l_Lean_Environment_header(v_env_1879_);
lean_dec_ref(v_env_1879_);
v___x_1906_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1905_);
v_mod_1907_ = lean_array_get(v___x_1904_, v___x_1906_, v_val_1900_);
lean_dec(v_val_1900_);
lean_dec_ref(v___x_1906_);
v___x_1908_ = l_Lean_isPrivateName(v_declHint_1875_);
lean_dec(v_declHint_1875_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1909_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v_c_1891_);
v___x_1911_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = l_Lean_MessageData_ofName(v_mod_1907_);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_MessageData_note(v___x_1916_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_msg_1874_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1918_);
v___x_1920_ = v___x_1902_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1922_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v_c_1891_);
v___x_1924_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_MessageData_ofName(v_mod_1907_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_MessageData_note(v___x_1929_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v_msg_1874_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1931_);
v___x_1933_ = v___x_1902_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1936_; 
lean_dec_ref(v_env_1879_);
lean_dec(v_declHint_1875_);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_msg_1874_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1937_, lean_object* v_declHint_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1937_, v_declHint_1938_, v___y_1939_);
lean_dec(v___y_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1942_, lean_object* v_declHint_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1959_; 
v___x_1949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1942_, v_declHint_1943_, v___y_1947_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1959_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1959_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1954_ = l_Lean_unknownIdentifierMessageTag;
v___x_1955_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v_a_1950_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1955_);
v___x_1957_ = v___x_1952_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1960_, lean_object* v_declHint_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1960_, v_declHint_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1968_, lean_object* v_msg_1969_, lean_object* v_declHint_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; lean_object* v_a_1977_; lean_object* v___x_1978_; 
v___x_1976_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1969_, v_declHint_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
v___x_1978_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1968_, v_a_1977_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1979_, lean_object* v_msg_1980_, lean_object* v_declHint_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1979_, v_msg_1980_, v_declHint_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v_ref_1979_);
return v_res_1987_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1990_ = l_Lean_stringToMessageData(v___x_1989_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1993_ = l_Lean_stringToMessageData(v___x_1992_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1994_, lean_object* v_constName_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2001_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_2002_ = 0;
lean_inc(v_constName_1995_);
v___x_2003_ = l_Lean_MessageData_ofConstName(v_constName_1995_, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2001_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1994_, v___x_2006_, v_constName_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_2008_, lean_object* v_constName_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2008_, v_constName_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v_ref_2008_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_ref_2022_; lean_object* v___x_2023_; 
v_ref_2022_ = lean_ctor_get(v___y_2019_, 5);
v___x_2023_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2022_, v_constName_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v_env_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; 
v___x_2037_ = lean_st_ref_get(v___y_2035_);
v_env_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_ref(v_env_2038_);
lean_dec(v___x_2037_);
v___x_2039_ = 0;
lean_inc(v_constName_2031_);
v___x_2040_ = l_Lean_Environment_findConstVal_x3f(v_env_2038_, v_constName_2031_, v___x_2039_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
return v___x_2041_;
}
else
{
lean_object* v_val_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_constName_2031_);
v_val_2042_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2040_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_val_2042_);
lean_dec(v___x_2040_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 0);
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_val_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2057_, uint8_t v_s_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v_env_2063_; lean_object* v_nextMacroScope_2064_; lean_object* v_ngen_2065_; lean_object* v_auxDeclNGen_2066_; lean_object* v_traceState_2067_; lean_object* v_messages_2068_; lean_object* v_infoState_2069_; lean_object* v_snapshotTasks_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2099_; 
v___x_2062_ = lean_st_ref_take(v___y_2060_);
v_env_2063_ = lean_ctor_get(v___x_2062_, 0);
v_nextMacroScope_2064_ = lean_ctor_get(v___x_2062_, 1);
v_ngen_2065_ = lean_ctor_get(v___x_2062_, 2);
v_auxDeclNGen_2066_ = lean_ctor_get(v___x_2062_, 3);
v_traceState_2067_ = lean_ctor_get(v___x_2062_, 4);
v_messages_2068_ = lean_ctor_get(v___x_2062_, 6);
v_infoState_2069_ = lean_ctor_get(v___x_2062_, 7);
v_snapshotTasks_2070_ = lean_ctor_get(v___x_2062_, 8);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v___x_2062_, 5);
lean_dec(v_unused_2100_);
v___x_2072_ = v___x_2062_;
v_isShared_2073_ = v_isSharedCheck_2099_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snapshotTasks_2070_);
lean_inc(v_infoState_2069_);
lean_inc(v_messages_2068_);
lean_inc(v_traceState_2067_);
lean_inc(v_auxDeclNGen_2066_);
lean_inc(v_ngen_2065_);
lean_inc(v_nextMacroScope_2064_);
lean_inc(v_env_2063_);
lean_dec(v___x_2062_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2099_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2074_ = 0;
v___x_2075_ = lean_box(0);
v___x_2076_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2063_, v_declName_2057_, v_s_2058_, v___x_2074_, v___x_2075_);
v___x_2077_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 5, v___x_2077_);
lean_ctor_set(v___x_2072_, 0, v___x_2076_);
v___x_2079_ = v___x_2072_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_nextMacroScope_2064_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_ngen_2065_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v_auxDeclNGen_2066_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_traceState_2067_);
lean_ctor_set(v_reuseFailAlloc_2098_, 5, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2098_, 6, v_messages_2068_);
lean_ctor_set(v_reuseFailAlloc_2098_, 7, v_infoState_2069_);
lean_ctor_set(v_reuseFailAlloc_2098_, 8, v_snapshotTasks_2070_);
v___x_2079_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v_mctx_2082_; lean_object* v_zetaDeltaFVarIds_2083_; lean_object* v_postponed_2084_; lean_object* v_diag_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2096_; 
v___x_2080_ = lean_st_ref_set(v___y_2060_, v___x_2079_);
v___x_2081_ = lean_st_ref_take(v___y_2059_);
v_mctx_2082_ = lean_ctor_get(v___x_2081_, 0);
v_zetaDeltaFVarIds_2083_ = lean_ctor_get(v___x_2081_, 2);
v_postponed_2084_ = lean_ctor_get(v___x_2081_, 3);
v_diag_2085_ = lean_ctor_get(v___x_2081_, 4);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v___x_2081_, 1);
lean_dec(v_unused_2097_);
v___x_2087_ = v___x_2081_;
v_isShared_2088_ = v_isSharedCheck_2096_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_diag_2085_);
lean_inc(v_postponed_2084_);
lean_inc(v_zetaDeltaFVarIds_2083_);
lean_inc(v_mctx_2082_);
lean_dec(v___x_2081_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2096_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2089_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_mctx_2082_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_zetaDeltaFVarIds_2083_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_postponed_2084_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_diag_2085_);
v___x_2091_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_st_ref_set(v___y_2059_, v___x_2091_);
v___x_2093_ = lean_box(0);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2101_, lean_object* v_s_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v_s_boxed_2106_; lean_object* v_res_2107_; 
v_s_boxed_2106_ = lean_unbox(v_s_2102_);
v_res_2107_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2101_, v_s_boxed_2106_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec(v___y_2103_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
uint8_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = 0;
v___x_2115_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2108_, v___x_2114_, v___y_2110_, v___y_2112_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2122_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2125_ = l_Lean_stringToMessageData(v___x_2124_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2128_ = l_Lean_stringToMessageData(v___x_2127_);
return v___x_2128_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2132_, lean_object* v_declName_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2139_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2140_ = l_Lean_MessageData_ofName(v_attrName_2132_);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = 0;
v___x_2145_ = l_Lean_MessageData_ofConstName(v_declName_2133_, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2143_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2148_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2150_, lean_object* v_declName_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2150_, v_declName_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2157_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2164_, lean_object* v_declName_2165_, lean_object* v_asyncPrefix_x3f_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___y_2173_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2166_) == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_MessageData_nil;
v___y_2173_ = v___x_2186_;
goto v___jp_2172_;
}
else
{
lean_object* v_val_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_val_2187_ = lean_ctor_get(v_asyncPrefix_x3f_2166_, 0);
lean_inc(v_val_2187_);
lean_dec_ref(v_asyncPrefix_x3f_2166_);
v___x_2188_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2189_ = l_Lean_MessageData_ofName(v_val_2187_);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___y_2173_ = v___x_2192_;
goto v___jp_2172_;
}
v___jp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2174_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2175_ = l_Lean_MessageData_ofName(v_attrName_2164_);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = 0;
v___x_2180_ = l_Lean_MessageData_ofConstName(v_declName_2165_, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2178_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v___y_2173_);
v___x_2185_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2184_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2193_, lean_object* v_declName_2194_, lean_object* v_asyncPrefix_x3f_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2193_, v_declName_2194_, v_asyncPrefix_x3f_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2202_, lean_object* v_decl_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___x_2252_; lean_object* v_env_2253_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___x_2268_; 
v___x_2252_ = lean_st_ref_get(v___y_2207_);
v_env_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc_ref(v_env_2253_);
lean_dec(v___x_2252_);
v___x_2268_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2253_, v_decl_2203_);
if (lean_obj_tag(v___x_2268_) == 0)
{
v___y_2255_ = v___y_2204_;
v___y_2256_ = v___y_2205_;
v___y_2257_ = v___y_2206_;
v___y_2258_ = v___y_2207_;
goto v___jp_2254_;
}
else
{
lean_object* v_attr_2269_; lean_object* v_toAttributeImplCore_2270_; lean_object* v_name_2271_; lean_object* v___x_2272_; 
lean_dec_ref(v___x_2268_);
lean_dec_ref(v_env_2253_);
v_attr_2269_ = lean_ctor_get(v_attr_2202_, 0);
lean_inc_ref(v_attr_2269_);
lean_dec_ref(v_attr_2202_);
v_toAttributeImplCore_2270_ = lean_ctor_get(v_attr_2269_, 0);
lean_inc_ref(v_toAttributeImplCore_2270_);
lean_dec_ref(v_attr_2269_);
v_name_2271_ = lean_ctor_get(v_toAttributeImplCore_2270_, 1);
lean_inc(v_name_2271_);
lean_dec_ref(v_toAttributeImplCore_2270_);
v___x_2272_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2271_, v_decl_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
return v___x_2272_;
}
v___jp_2209_:
{
lean_object* v___x_2212_; lean_object* v_ext_2213_; lean_object* v_toEnvExtension_2214_; lean_object* v_env_2215_; lean_object* v_nextMacroScope_2216_; lean_object* v_ngen_2217_; lean_object* v_auxDeclNGen_2218_; lean_object* v_traceState_2219_; lean_object* v_messages_2220_; lean_object* v_infoState_2221_; lean_object* v_snapshotTasks_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2250_; 
v___x_2212_ = lean_st_ref_take(v___y_2211_);
v_ext_2213_ = lean_ctor_get(v_attr_2202_, 1);
lean_inc_ref(v_ext_2213_);
lean_dec_ref(v_attr_2202_);
v_toEnvExtension_2214_ = lean_ctor_get(v_ext_2213_, 0);
v_env_2215_ = lean_ctor_get(v___x_2212_, 0);
v_nextMacroScope_2216_ = lean_ctor_get(v___x_2212_, 1);
v_ngen_2217_ = lean_ctor_get(v___x_2212_, 2);
v_auxDeclNGen_2218_ = lean_ctor_get(v___x_2212_, 3);
v_traceState_2219_ = lean_ctor_get(v___x_2212_, 4);
v_messages_2220_ = lean_ctor_get(v___x_2212_, 6);
v_infoState_2221_ = lean_ctor_get(v___x_2212_, 7);
v_snapshotTasks_2222_ = lean_ctor_get(v___x_2212_, 8);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v___x_2212_, 5);
lean_dec(v_unused_2251_);
v___x_2224_ = v___x_2212_;
v_isShared_2225_ = v_isSharedCheck_2250_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_snapshotTasks_2222_);
lean_inc(v_infoState_2221_);
lean_inc(v_messages_2220_);
lean_inc(v_traceState_2219_);
lean_inc(v_auxDeclNGen_2218_);
lean_inc(v_ngen_2217_);
lean_inc(v_nextMacroScope_2216_);
lean_inc(v_env_2215_);
lean_dec(v___x_2212_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2250_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v_asyncMode_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v_asyncMode_2226_ = lean_ctor_get(v_toEnvExtension_2214_, 2);
lean_inc(v_asyncMode_2226_);
lean_inc(v_decl_2203_);
v___x_2227_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2213_, v_env_2215_, v_decl_2203_, v_asyncMode_2226_, v_decl_2203_);
lean_dec(v_asyncMode_2226_);
v___x_2228_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 5, v___x_2228_);
lean_ctor_set(v___x_2224_, 0, v___x_2227_);
v___x_2230_ = v___x_2224_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_nextMacroScope_2216_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_ngen_2217_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_auxDeclNGen_2218_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_traceState_2219_);
lean_ctor_set(v_reuseFailAlloc_2249_, 5, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2249_, 6, v_messages_2220_);
lean_ctor_set(v_reuseFailAlloc_2249_, 7, v_infoState_2221_);
lean_ctor_set(v_reuseFailAlloc_2249_, 8, v_snapshotTasks_2222_);
v___x_2230_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v_mctx_2233_; lean_object* v_zetaDeltaFVarIds_2234_; lean_object* v_postponed_2235_; lean_object* v_diag_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2247_; 
v___x_2231_ = lean_st_ref_set(v___y_2211_, v___x_2230_);
v___x_2232_ = lean_st_ref_take(v___y_2210_);
v_mctx_2233_ = lean_ctor_get(v___x_2232_, 0);
v_zetaDeltaFVarIds_2234_ = lean_ctor_get(v___x_2232_, 2);
v_postponed_2235_ = lean_ctor_get(v___x_2232_, 3);
v_diag_2236_ = lean_ctor_get(v___x_2232_, 4);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v___x_2232_, 1);
lean_dec(v_unused_2248_);
v___x_2238_ = v___x_2232_;
v_isShared_2239_ = v_isSharedCheck_2247_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_diag_2236_);
lean_inc(v_postponed_2235_);
lean_inc(v_zetaDeltaFVarIds_2234_);
lean_inc(v_mctx_2233_);
lean_dec(v___x_2232_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2247_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v___x_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_mctx_2233_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_zetaDeltaFVarIds_2234_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_postponed_2235_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v_diag_2236_);
v___x_2242_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_st_ref_set(v___y_2210_, v___x_2242_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
}
}
}
v___jp_2254_:
{
lean_object* v_ext_2259_; lean_object* v_toEnvExtension_2260_; lean_object* v_attr_2261_; lean_object* v_asyncMode_2262_; uint8_t v___x_2263_; 
v_ext_2259_ = lean_ctor_get(v_attr_2202_, 1);
v_toEnvExtension_2260_ = lean_ctor_get(v_ext_2259_, 0);
v_attr_2261_ = lean_ctor_get(v_attr_2202_, 0);
v_asyncMode_2262_ = lean_ctor_get(v_toEnvExtension_2260_, 2);
lean_inc(v_decl_2203_);
lean_inc_ref(v_env_2253_);
v___x_2263_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2253_, v_decl_2203_, v_asyncMode_2262_);
if (v___x_2263_ == 0)
{
lean_object* v_toAttributeImplCore_2264_; lean_object* v_name_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_inc_ref(v_attr_2261_);
lean_dec_ref(v_attr_2202_);
v_toAttributeImplCore_2264_ = lean_ctor_get(v_attr_2261_, 0);
lean_inc_ref(v_toAttributeImplCore_2264_);
lean_dec_ref(v_attr_2261_);
v_name_2265_ = lean_ctor_get(v_toAttributeImplCore_2264_, 1);
lean_inc(v_name_2265_);
lean_dec_ref(v_toAttributeImplCore_2264_);
v___x_2266_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2253_);
v___x_2267_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2265_, v_decl_2203_, v___x_2266_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2267_;
}
else
{
lean_dec_ref(v_env_2253_);
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2258_;
goto v___jp_2209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2273_, lean_object* v_decl_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2273_, v_decl_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; lean_object* v_env_2288_; uint8_t v___x_2289_; lean_object* v___x_2290_; 
v___x_2287_ = lean_st_ref_get(v___y_2285_);
v_env_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc_ref(v_env_2288_);
lean_dec(v___x_2287_);
v___x_2289_ = 0;
lean_inc(v_constName_2281_);
v___x_2290_ = l_Lean_Environment_find_x3f(v_env_2288_, v_constName_2281_, v___x_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
return v___x_2291_;
}
else
{
lean_object* v_val_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_constName_2281_);
v_val_2292_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2290_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_val_2292_);
lean_dec(v___x_2290_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set_tag(v___x_2294_, 0);
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_val_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
return v_res_2306_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2310_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2311_ = lean_unsigned_to_nat(58u);
v___x_2312_ = lean_unsigned_to_nat(33u);
v___x_2313_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2314_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2315_ = l_mkPanicMessageWithDecl(v___x_2314_, v___x_2313_, v___x_2312_, v___x_2311_, v___x_2310_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2317_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2318_ = lean_unsigned_to_nat(60u);
v___x_2319_ = lean_unsigned_to_nat(30u);
v___x_2320_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2321_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2322_ = l_mkPanicMessageWithDecl(v___x_2321_, v___x_2320_, v___x_2319_, v___x_2318_, v___x_2317_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2323_, lean_object* v_indName_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___x_2330_; 
lean_inc(v_indName_2324_);
v___x_2330_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref(v___x_2330_);
if (lean_obj_tag(v_a_2331_) == 5)
{
lean_object* v_val_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2519_; 
v_val_2332_ = lean_ctor_get(v_a_2331_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_a_2331_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2334_ = v_a_2331_;
v_isShared_2335_ = v_isSharedCheck_2519_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_val_2332_);
lean_dec(v_a_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2519_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_inc(v_indName_2324_);
v___x_2336_ = l_Lean_mkCasesOnName(v_indName_2324_);
lean_inc(v___x_2336_);
v___x_2337_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2336_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v_name_2339_; lean_object* v_levelParams_2340_; lean_object* v_type_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
v_name_2339_ = lean_ctor_get(v_a_2338_, 0);
lean_inc(v_name_2339_);
v_levelParams_2340_ = lean_ctor_get(v_a_2338_, 1);
lean_inc(v_levelParams_2340_);
v_type_2341_ = lean_ctor_get(v_a_2338_, 2);
lean_inc_ref(v_type_2341_);
lean_dec(v_a_2338_);
v___x_2342_ = lean_box(0);
lean_inc(v_levelParams_2340_);
v___x_2343_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2340_, v___x_2342_);
if (lean_obj_tag(v___x_2343_) == 1)
{
lean_object* v_head_2344_; lean_object* v_tail_2345_; lean_object* v_numParams_2346_; lean_object* v_numIndices_2347_; lean_object* v_ctors_2348_; lean_object* v___x_2349_; lean_object* v___f_2350_; lean_object* v___x_2352_; 
v_head_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_head_2344_);
v_tail_2345_ = lean_ctor_get(v___x_2343_, 1);
lean_inc(v_tail_2345_);
v_numParams_2346_ = lean_ctor_get(v_val_2332_, 1);
lean_inc(v_numParams_2346_);
v_numIndices_2347_ = lean_ctor_get(v_val_2332_, 2);
lean_inc(v_numIndices_2347_);
v_ctors_2348_ = lean_ctor_get(v_val_2332_, 4);
lean_inc(v_ctors_2348_);
v___x_2349_ = l_Lean_instInhabitedExpr;
lean_inc(v_numParams_2346_);
v___f_2350_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 18, 11);
lean_closure_set(v___f_2350_, 0, v_numIndices_2347_);
lean_closure_set(v___f_2350_, 1, v_head_2344_);
lean_closure_set(v___f_2350_, 2, v_ctors_2348_);
lean_closure_set(v___f_2350_, 3, v_tail_2345_);
lean_closure_set(v___f_2350_, 4, v_numParams_2346_);
lean_closure_set(v___f_2350_, 5, v_indName_2324_);
lean_closure_set(v___f_2350_, 6, v_val_2332_);
lean_closure_set(v___f_2350_, 7, v___x_2343_);
lean_closure_set(v___f_2350_, 8, v___x_2336_);
lean_closure_set(v___f_2350_, 9, v_name_2339_);
lean_closure_set(v___f_2350_, 10, v___x_2349_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 1);
lean_ctor_set(v___x_2334_, 0, v_numParams_2346_);
v___x_2352_ = v___x_2334_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_numParams_2346_);
v___x_2352_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
uint8_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = 0;
v___x_2354_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2341_, v___x_2352_, v___f_2350_, v___x_2353_, v___x_2353_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2356_; lean_object* v___f_2357_; uint8_t v___y_2359_; uint8_t v___x_2498_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = lean_box(v___x_2353_);
lean_inc(v_declName_2323_);
v___f_2357_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2357_, 0, v_a_2355_);
lean_closure_set(v___f_2357_, 1, v_declName_2323_);
lean_closure_set(v___f_2357_, 2, v_levelParams_2340_);
lean_closure_set(v___f_2357_, 3, v___x_2356_);
v___x_2498_ = l_Lean_isPrivateName(v_declName_2323_);
if (v___x_2498_ == 0)
{
uint8_t v___x_2499_; 
v___x_2499_ = 1;
v___y_2359_ = v___x_2499_;
goto v___jp_2358_;
}
else
{
v___y_2359_ = v___x_2353_;
goto v___jp_2358_;
}
v___jp_2358_:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2357_, v___y_2359_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2361_; lean_object* v_env_2362_; lean_object* v_nextMacroScope_2363_; lean_object* v_ngen_2364_; lean_object* v_auxDeclNGen_2365_; lean_object* v_traceState_2366_; lean_object* v_messages_2367_; lean_object* v_infoState_2368_; lean_object* v_snapshotTasks_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v___x_2360_);
v___x_2361_ = lean_st_ref_take(v_a_2328_);
v_env_2362_ = lean_ctor_get(v___x_2361_, 0);
v_nextMacroScope_2363_ = lean_ctor_get(v___x_2361_, 1);
v_ngen_2364_ = lean_ctor_get(v___x_2361_, 2);
v_auxDeclNGen_2365_ = lean_ctor_get(v___x_2361_, 3);
v_traceState_2366_ = lean_ctor_get(v___x_2361_, 4);
v_messages_2367_ = lean_ctor_get(v___x_2361_, 6);
v_infoState_2368_ = lean_ctor_get(v___x_2361_, 7);
v_snapshotTasks_2369_ = lean_ctor_get(v___x_2361_, 8);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v___x_2361_, 5);
lean_dec(v_unused_2497_);
v___x_2371_ = v___x_2361_;
v_isShared_2372_ = v_isSharedCheck_2496_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_snapshotTasks_2369_);
lean_inc(v_infoState_2368_);
lean_inc(v_messages_2367_);
lean_inc(v_traceState_2366_);
lean_inc(v_auxDeclNGen_2365_);
lean_inc(v_ngen_2364_);
lean_inc(v_nextMacroScope_2363_);
lean_inc(v_env_2362_);
lean_dec(v___x_2361_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2496_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
lean_inc(v_declName_2323_);
v___x_2373_ = l_Lean_Meta_markMatcherLike(v_env_2362_, v_declName_2323_);
v___x_2374_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 5, v___x_2374_);
lean_ctor_set(v___x_2371_, 0, v___x_2373_);
v___x_2376_ = v___x_2371_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_nextMacroScope_2363_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_ngen_2364_);
lean_ctor_set(v_reuseFailAlloc_2495_, 3, v_auxDeclNGen_2365_);
lean_ctor_set(v_reuseFailAlloc_2495_, 4, v_traceState_2366_);
lean_ctor_set(v_reuseFailAlloc_2495_, 5, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2495_, 6, v_messages_2367_);
lean_ctor_set(v_reuseFailAlloc_2495_, 7, v_infoState_2368_);
lean_ctor_set(v_reuseFailAlloc_2495_, 8, v_snapshotTasks_2369_);
v___x_2376_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_mctx_2379_; lean_object* v_zetaDeltaFVarIds_2380_; lean_object* v_postponed_2381_; lean_object* v_diag_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2493_; 
v___x_2377_ = lean_st_ref_set(v_a_2328_, v___x_2376_);
v___x_2378_ = lean_st_ref_take(v_a_2326_);
v_mctx_2379_ = lean_ctor_get(v___x_2378_, 0);
v_zetaDeltaFVarIds_2380_ = lean_ctor_get(v___x_2378_, 2);
v_postponed_2381_ = lean_ctor_get(v___x_2378_, 3);
v_diag_2382_ = lean_ctor_get(v___x_2378_, 4);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v___x_2378_, 1);
lean_dec(v_unused_2494_);
v___x_2384_ = v___x_2378_;
v_isShared_2385_ = v_isSharedCheck_2493_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_diag_2382_);
lean_inc(v_postponed_2381_);
lean_inc(v_zetaDeltaFVarIds_2380_);
lean_inc(v_mctx_2379_);
lean_dec(v___x_2378_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2493_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v___x_2386_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_mctx_2379_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_zetaDeltaFVarIds_2380_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_postponed_2381_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_diag_2382_);
v___x_2388_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v_env_2391_; lean_object* v_nextMacroScope_2392_; lean_object* v_ngen_2393_; lean_object* v_auxDeclNGen_2394_; lean_object* v_traceState_2395_; lean_object* v_messages_2396_; lean_object* v_infoState_2397_; lean_object* v_snapshotTasks_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2490_; 
v___x_2389_ = lean_st_ref_set(v_a_2326_, v___x_2388_);
v___x_2390_ = lean_st_ref_take(v_a_2328_);
v_env_2391_ = lean_ctor_get(v___x_2390_, 0);
v_nextMacroScope_2392_ = lean_ctor_get(v___x_2390_, 1);
v_ngen_2393_ = lean_ctor_get(v___x_2390_, 2);
v_auxDeclNGen_2394_ = lean_ctor_get(v___x_2390_, 3);
v_traceState_2395_ = lean_ctor_get(v___x_2390_, 4);
v_messages_2396_ = lean_ctor_get(v___x_2390_, 6);
v_infoState_2397_ = lean_ctor_get(v___x_2390_, 7);
v_snapshotTasks_2398_ = lean_ctor_get(v___x_2390_, 8);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2390_, 5);
lean_dec(v_unused_2491_);
v___x_2400_ = v___x_2390_;
v_isShared_2401_ = v_isSharedCheck_2490_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_snapshotTasks_2398_);
lean_inc(v_infoState_2397_);
lean_inc(v_messages_2396_);
lean_inc(v_traceState_2395_);
lean_inc(v_auxDeclNGen_2394_);
lean_inc(v_ngen_2393_);
lean_inc(v_nextMacroScope_2392_);
lean_inc(v_env_2391_);
lean_dec(v___x_2390_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2490_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_inc(v_declName_2323_);
v___x_2402_ = l_Lean_markAuxRecursor(v_env_2391_, v_declName_2323_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 5, v___x_2374_);
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_nextMacroScope_2392_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_ngen_2393_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_auxDeclNGen_2394_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_traceState_2395_);
lean_ctor_set(v_reuseFailAlloc_2489_, 5, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2489_, 6, v_messages_2396_);
lean_ctor_set(v_reuseFailAlloc_2489_, 7, v_infoState_2397_);
lean_ctor_set(v_reuseFailAlloc_2489_, 8, v_snapshotTasks_2398_);
v___x_2404_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v_mctx_2407_; lean_object* v_zetaDeltaFVarIds_2408_; lean_object* v_postponed_2409_; lean_object* v_diag_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2487_; 
v___x_2405_ = lean_st_ref_set(v_a_2328_, v___x_2404_);
v___x_2406_ = lean_st_ref_take(v_a_2326_);
v_mctx_2407_ = lean_ctor_get(v___x_2406_, 0);
v_zetaDeltaFVarIds_2408_ = lean_ctor_get(v___x_2406_, 2);
v_postponed_2409_ = lean_ctor_get(v___x_2406_, 3);
v_diag_2410_ = lean_ctor_get(v___x_2406_, 4);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v___x_2406_, 1);
lean_dec(v_unused_2488_);
v___x_2412_ = v___x_2406_;
v_isShared_2413_ = v_isSharedCheck_2487_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_diag_2410_);
lean_inc(v_postponed_2409_);
lean_inc(v_zetaDeltaFVarIds_2408_);
lean_inc(v_mctx_2407_);
lean_dec(v___x_2406_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2487_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2386_);
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_mctx_2407_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_zetaDeltaFVarIds_2408_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_postponed_2409_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_diag_2410_);
v___x_2415_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v_env_2418_; lean_object* v_nextMacroScope_2419_; lean_object* v_ngen_2420_; lean_object* v_auxDeclNGen_2421_; lean_object* v_traceState_2422_; lean_object* v_messages_2423_; lean_object* v_infoState_2424_; lean_object* v_snapshotTasks_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2484_; 
v___x_2416_ = lean_st_ref_set(v_a_2326_, v___x_2415_);
v___x_2417_ = lean_st_ref_take(v_a_2328_);
v_env_2418_ = lean_ctor_get(v___x_2417_, 0);
v_nextMacroScope_2419_ = lean_ctor_get(v___x_2417_, 1);
v_ngen_2420_ = lean_ctor_get(v___x_2417_, 2);
v_auxDeclNGen_2421_ = lean_ctor_get(v___x_2417_, 3);
v_traceState_2422_ = lean_ctor_get(v___x_2417_, 4);
v_messages_2423_ = lean_ctor_get(v___x_2417_, 6);
v_infoState_2424_ = lean_ctor_get(v___x_2417_, 7);
v_snapshotTasks_2425_ = lean_ctor_get(v___x_2417_, 8);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v___x_2417_, 5);
lean_dec(v_unused_2485_);
v___x_2427_ = v___x_2417_;
v_isShared_2428_ = v_isSharedCheck_2484_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_snapshotTasks_2425_);
lean_inc(v_infoState_2424_);
lean_inc(v_messages_2423_);
lean_inc(v_traceState_2422_);
lean_inc(v_auxDeclNGen_2421_);
lean_inc(v_ngen_2420_);
lean_inc(v_nextMacroScope_2419_);
lean_inc(v_env_2418_);
lean_dec(v___x_2417_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2484_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
lean_inc(v_declName_2323_);
v___x_2429_ = l_Lean_Meta_addToCompletionBlackList(v_env_2418_, v_declName_2323_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 5, v___x_2374_);
lean_ctor_set(v___x_2427_, 0, v___x_2429_);
v___x_2431_ = v___x_2427_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_nextMacroScope_2419_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_ngen_2420_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_auxDeclNGen_2421_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_traceState_2422_);
lean_ctor_set(v_reuseFailAlloc_2483_, 5, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2483_, 6, v_messages_2423_);
lean_ctor_set(v_reuseFailAlloc_2483_, 7, v_infoState_2424_);
lean_ctor_set(v_reuseFailAlloc_2483_, 8, v_snapshotTasks_2425_);
v___x_2431_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_mctx_2434_; lean_object* v_zetaDeltaFVarIds_2435_; lean_object* v_postponed_2436_; lean_object* v_diag_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2481_; 
v___x_2432_ = lean_st_ref_set(v_a_2328_, v___x_2431_);
v___x_2433_ = lean_st_ref_take(v_a_2326_);
v_mctx_2434_ = lean_ctor_get(v___x_2433_, 0);
v_zetaDeltaFVarIds_2435_ = lean_ctor_get(v___x_2433_, 2);
v_postponed_2436_ = lean_ctor_get(v___x_2433_, 3);
v_diag_2437_ = lean_ctor_get(v___x_2433_, 4);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2433_, 1);
lean_dec(v_unused_2482_);
v___x_2439_ = v___x_2433_;
v_isShared_2440_ = v_isSharedCheck_2481_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_diag_2437_);
lean_inc(v_postponed_2436_);
lean_inc(v_zetaDeltaFVarIds_2435_);
lean_inc(v_mctx_2434_);
lean_dec(v___x_2433_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2481_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 1, v___x_2386_);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_mctx_2434_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_zetaDeltaFVarIds_2435_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_postponed_2436_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_diag_2437_);
v___x_2442_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_env_2445_; lean_object* v_nextMacroScope_2446_; lean_object* v_ngen_2447_; lean_object* v_auxDeclNGen_2448_; lean_object* v_traceState_2449_; lean_object* v_messages_2450_; lean_object* v_infoState_2451_; lean_object* v_snapshotTasks_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2478_; 
v___x_2443_ = lean_st_ref_set(v_a_2326_, v___x_2442_);
v___x_2444_ = lean_st_ref_take(v_a_2328_);
v_env_2445_ = lean_ctor_get(v___x_2444_, 0);
v_nextMacroScope_2446_ = lean_ctor_get(v___x_2444_, 1);
v_ngen_2447_ = lean_ctor_get(v___x_2444_, 2);
v_auxDeclNGen_2448_ = lean_ctor_get(v___x_2444_, 3);
v_traceState_2449_ = lean_ctor_get(v___x_2444_, 4);
v_messages_2450_ = lean_ctor_get(v___x_2444_, 6);
v_infoState_2451_ = lean_ctor_get(v___x_2444_, 7);
v_snapshotTasks_2452_ = lean_ctor_get(v___x_2444_, 8);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2444_, 5);
lean_dec(v_unused_2479_);
v___x_2454_ = v___x_2444_;
v_isShared_2455_ = v_isSharedCheck_2478_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_snapshotTasks_2452_);
lean_inc(v_infoState_2451_);
lean_inc(v_messages_2450_);
lean_inc(v_traceState_2449_);
lean_inc(v_auxDeclNGen_2448_);
lean_inc(v_ngen_2447_);
lean_inc(v_nextMacroScope_2446_);
lean_inc(v_env_2445_);
lean_dec(v___x_2444_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2478_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
lean_inc(v_declName_2323_);
v___x_2456_ = l_Lean_addProtected(v_env_2445_, v_declName_2323_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 5, v___x_2374_);
lean_ctor_set(v___x_2454_, 0, v___x_2456_);
v___x_2458_ = v___x_2454_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_nextMacroScope_2446_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_ngen_2447_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_auxDeclNGen_2448_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_traceState_2449_);
lean_ctor_set(v_reuseFailAlloc_2477_, 5, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2477_, 6, v_messages_2450_);
lean_ctor_set(v_reuseFailAlloc_2477_, 7, v_infoState_2451_);
lean_ctor_set(v_reuseFailAlloc_2477_, 8, v_snapshotTasks_2452_);
v___x_2458_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_mctx_2461_; lean_object* v_zetaDeltaFVarIds_2462_; lean_object* v_postponed_2463_; lean_object* v_diag_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2475_; 
v___x_2459_ = lean_st_ref_set(v_a_2328_, v___x_2458_);
v___x_2460_ = lean_st_ref_take(v_a_2326_);
v_mctx_2461_ = lean_ctor_get(v___x_2460_, 0);
v_zetaDeltaFVarIds_2462_ = lean_ctor_get(v___x_2460_, 2);
v_postponed_2463_ = lean_ctor_get(v___x_2460_, 3);
v_diag_2464_ = lean_ctor_get(v___x_2460_, 4);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2460_, 1);
lean_dec(v_unused_2476_);
v___x_2466_ = v___x_2460_;
v_isShared_2467_ = v_isSharedCheck_2475_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_diag_2464_);
lean_inc(v_postponed_2463_);
lean_inc(v_zetaDeltaFVarIds_2462_);
lean_inc(v_mctx_2461_);
lean_dec(v___x_2460_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2475_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2386_);
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_mctx_2461_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_zetaDeltaFVarIds_2462_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_postponed_2463_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_diag_2464_);
v___x_2469_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_st_ref_set(v_a_2326_, v___x_2469_);
v___x_2471_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2323_);
v___x_2472_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2471_, v_declName_2323_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___x_2473_; 
lean_dec_ref(v___x_2472_);
v___x_2473_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2323_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_2473_;
}
else
{
lean_dec(v_declName_2323_);
return v___x_2472_;
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
lean_dec(v_declName_2323_);
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_levelParams_2340_);
lean_dec(v_declName_2323_);
v_a_2500_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2354_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2354_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v___x_2343_);
lean_dec_ref(v_type_2341_);
lean_dec(v_levelParams_2340_);
lean_dec(v_name_2339_);
lean_dec(v___x_2336_);
lean_del_object(v___x_2334_);
lean_dec_ref(v_val_2332_);
lean_dec(v_indName_2324_);
lean_dec(v_declName_2323_);
v___x_2509_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2510_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2509_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_2510_;
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v___x_2336_);
lean_del_object(v___x_2334_);
lean_dec_ref(v_val_2332_);
lean_dec(v_indName_2324_);
lean_dec(v_declName_2323_);
v_a_2511_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2337_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2337_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v_a_2331_);
lean_dec(v_indName_2324_);
lean_dec(v_declName_2323_);
v___x_2520_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2521_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2520_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_2521_;
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v_indName_2324_);
lean_dec(v_declName_2323_);
v_a_2522_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2330_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2330_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2530_, lean_object* v_indName_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2530_, v_indName_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
lean_dec(v_a_2535_);
lean_dec_ref(v_a_2534_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2538_, lean_object* v_name_2539_, lean_object* v_type_2540_, lean_object* v_k_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2539_, v_type_2540_, v_k_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2548_, lean_object* v_name_2549_, lean_object* v_type_2550_, lean_object* v_k_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2548_, v_name_2549_, v_type_2550_, v_k_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2558_, lean_object* v_params_2559_, lean_object* v_alts_2560_, lean_object* v___x_2561_, lean_object* v_ism2_2562_, lean_object* v_motive_2563_, lean_object* v_val_2564_, lean_object* v_indName_2565_, lean_object* v___x_2566_, lean_object* v___x_2567_, lean_object* v___x_2568_, lean_object* v_as_2569_, lean_object* v_i_2570_, lean_object* v_j_2571_, lean_object* v_inv_2572_, lean_object* v_bs_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2558_, v_params_2559_, v_alts_2560_, v___x_2561_, v_ism2_2562_, v_motive_2563_, v_val_2564_, v_indName_2565_, v___x_2566_, v___x_2567_, v___x_2568_, v_as_2569_, v_i_2570_, v_j_2571_, v_bs_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2580_ = _args[0];
lean_object* v_params_2581_ = _args[1];
lean_object* v_alts_2582_ = _args[2];
lean_object* v___x_2583_ = _args[3];
lean_object* v_ism2_2584_ = _args[4];
lean_object* v_motive_2585_ = _args[5];
lean_object* v_val_2586_ = _args[6];
lean_object* v_indName_2587_ = _args[7];
lean_object* v___x_2588_ = _args[8];
lean_object* v___x_2589_ = _args[9];
lean_object* v___x_2590_ = _args[10];
lean_object* v_as_2591_ = _args[11];
lean_object* v_i_2592_ = _args[12];
lean_object* v_j_2593_ = _args[13];
lean_object* v_inv_2594_ = _args[14];
lean_object* v_bs_2595_ = _args[15];
lean_object* v___y_2596_ = _args[16];
lean_object* v___y_2597_ = _args[17];
lean_object* v___y_2598_ = _args[18];
lean_object* v___y_2599_ = _args[19];
lean_object* v___y_2600_ = _args[20];
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2580_, v_params_2581_, v_alts_2582_, v___x_2583_, v_ism2_2584_, v_motive_2585_, v_val_2586_, v_indName_2587_, v___x_2588_, v___x_2589_, v___x_2590_, v_as_2591_, v_i_2592_, v_j_2593_, v_inv_2594_, v_bs_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec_ref(v_as_2591_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2602_, lean_object* v_params_2603_, lean_object* v___x_2604_, lean_object* v_motive_2605_, lean_object* v_as_2606_, lean_object* v_i_2607_, lean_object* v_j_2608_, lean_object* v_inv_2609_, lean_object* v_bs_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2602_, v_params_2603_, v___x_2604_, v_motive_2605_, v_as_2606_, v_i_2607_, v_j_2608_, v_bs_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2617_, lean_object* v_params_2618_, lean_object* v___x_2619_, lean_object* v_motive_2620_, lean_object* v_as_2621_, lean_object* v_i_2622_, lean_object* v_j_2623_, lean_object* v_inv_2624_, lean_object* v_bs_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2617_, v_params_2618_, v___x_2619_, v_motive_2620_, v_as_2621_, v_i_2622_, v_j_2623_, v_inv_2624_, v_bs_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v_as_2621_);
lean_dec_ref(v_params_2618_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_00_u03b1_2632_, lean_object* v_inst_2633_, lean_object* v_declInfos_2634_, lean_object* v_k_2635_, uint8_t v_kind_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(v_inst_2633_, v_declInfos_2634_, v_k_2635_, v_kind_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_00_u03b1_2643_, lean_object* v_inst_2644_, lean_object* v_declInfos_2645_, lean_object* v_k_2646_, lean_object* v_kind_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v_kind_boxed_2653_; lean_object* v_res_2654_; 
v_kind_boxed_2653_ = lean_unbox(v_kind_2647_);
v_res_2654_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_00_u03b1_2643_, v_inst_2644_, v_declInfos_2645_, v_k_2646_, v_kind_boxed_2653_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v_inst_2644_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2655_, uint8_t v_s_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2655_, v_s_2656_, v___y_2658_, v___y_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2663_, lean_object* v_s_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v_s_boxed_2670_; lean_object* v_res_2671_; 
v_s_boxed_2670_ = lean_unbox(v_s_2664_);
v_res_2671_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2663_, v_s_boxed_2670_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2672_, lean_object* v_constName_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2680_, lean_object* v_constName_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2680_, v_constName_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_00_u03b1_2688_, lean_object* v_inst_2689_, lean_object* v_declInfos_2690_, lean_object* v_k_2691_, uint8_t v_kind_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___redArg(v_inst_2689_, v_declInfos_2690_, v_k_2691_, v_kind_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2699_, lean_object* v_inst_2700_, lean_object* v_declInfos_2701_, lean_object* v_k_2702_, lean_object* v_kind_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
uint8_t v_kind_boxed_2709_; lean_object* v_res_2710_; 
v_kind_boxed_2709_ = lean_unbox(v_kind_2703_);
v_res_2710_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_00_u03b1_2699_, v_inst_2700_, v_declInfos_2701_, v_k_2702_, v_kind_boxed_2709_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v_inst_2700_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2711_, lean_object* v_attrName_2712_, lean_object* v_declName_2713_, lean_object* v_asyncPrefix_x3f_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2712_, v_declName_2713_, v_asyncPrefix_x3f_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2721_, lean_object* v_attrName_2722_, lean_object* v_declName_2723_, lean_object* v_asyncPrefix_x3f_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2721_, v_attrName_2722_, v_declName_2723_, v_asyncPrefix_x3f_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2731_, lean_object* v_attrName_2732_, lean_object* v_declName_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2732_, v_declName_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2740_, lean_object* v_attrName_2741_, lean_object* v_declName_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2740_, v_attrName_2741_, v_declName_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2749_, lean_object* v_ref_2750_, lean_object* v_constName_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2750_, v_constName_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2758_, lean_object* v_ref_2759_, lean_object* v_constName_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2758_, v_ref_2759_, v_constName_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v_ref_2759_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_00_u03b1_2767_, lean_object* v_inst_2768_, lean_object* v_declInfos_2769_, lean_object* v_k_2770_, uint8_t v_kind_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___redArg(v_inst_2768_, v_declInfos_2769_, v_k_2770_, v_kind_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_inst_2779_, lean_object* v_declInfos_2780_, lean_object* v_k_2781_, lean_object* v_kind_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
uint8_t v_kind_boxed_2788_; lean_object* v_res_2789_; 
v_kind_boxed_2788_ = lean_unbox(v_kind_2782_);
v_res_2789_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_00_u03b1_2778_, v_inst_2779_, v_declInfos_2780_, v_k_2781_, v_kind_boxed_2788_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v_inst_2779_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2790_, lean_object* v_msg_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2798_, lean_object* v_msg_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2798_, v_msg_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2806_, lean_object* v_ref_2807_, lean_object* v_msg_2808_, lean_object* v_declHint_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2807_, v_msg_2808_, v_declHint_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2816_, lean_object* v_ref_2817_, lean_object* v_msg_2818_, lean_object* v_declHint_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2816_, v_ref_2817_, v_msg_2818_, v_declHint_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_ref_2817_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_00_u03b1_2826_, lean_object* v_declInfos_2827_, lean_object* v_k_2828_, uint8_t v_kind_2829_, lean_object* v_inst_2830_, lean_object* v_acc_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___redArg(v_declInfos_2827_, v_k_2828_, v_kind_2829_, v_acc_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_declInfos_2839_, lean_object* v_k_2840_, lean_object* v_kind_2841_, lean_object* v_inst_2842_, lean_object* v_acc_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v_kind_boxed_2849_; lean_object* v_res_2850_; 
v_kind_boxed_2849_ = lean_unbox(v_kind_2841_);
v_res_2850_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_00_u03b1_2838_, v_declInfos_2839_, v_k_2840_, v_kind_boxed_2849_, v_inst_2842_, v_acc_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v_inst_2842_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2851_, lean_object* v_declHint_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2851_, v_declHint_2852_, v___y_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2859_, lean_object* v_declHint_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2859_, v_declHint_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2867_, lean_object* v_ref_2868_, lean_object* v_msg_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2868_, v_msg_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2876_, lean_object* v_ref_2877_, lean_object* v_msg_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2876_, v_ref_2877_, v_msg_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v_ref_2877_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v___x_2888_; 
v___x_2888_ = l_Lean_Expr_hasMVar(v_e_2885_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_e_2885_);
return v___x_2889_;
}
else
{
lean_object* v___x_2890_; lean_object* v_mctx_2891_; lean_object* v___x_2892_; lean_object* v_fst_2893_; lean_object* v_snd_2894_; lean_object* v___x_2895_; lean_object* v_cache_2896_; lean_object* v_zetaDeltaFVarIds_2897_; lean_object* v_postponed_2898_; lean_object* v_diag_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2908_; 
v___x_2890_ = lean_st_ref_get(v___y_2886_);
v_mctx_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc_ref(v_mctx_2891_);
lean_dec(v___x_2890_);
v___x_2892_ = l_Lean_instantiateMVarsCore(v_mctx_2891_, v_e_2885_);
v_fst_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_fst_2893_);
v_snd_2894_ = lean_ctor_get(v___x_2892_, 1);
lean_inc(v_snd_2894_);
lean_dec_ref(v___x_2892_);
v___x_2895_ = lean_st_ref_take(v___y_2886_);
v_cache_2896_ = lean_ctor_get(v___x_2895_, 1);
v_zetaDeltaFVarIds_2897_ = lean_ctor_get(v___x_2895_, 2);
v_postponed_2898_ = lean_ctor_get(v___x_2895_, 3);
v_diag_2899_ = lean_ctor_get(v___x_2895_, 4);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v___x_2895_, 0);
lean_dec(v_unused_2909_);
v___x_2901_ = v___x_2895_;
v_isShared_2902_ = v_isSharedCheck_2908_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_diag_2899_);
lean_inc(v_postponed_2898_);
lean_inc(v_zetaDeltaFVarIds_2897_);
lean_inc(v_cache_2896_);
lean_dec(v___x_2895_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2908_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v_snd_2894_);
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_snd_2894_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_cache_2896_);
lean_ctor_set(v_reuseFailAlloc_2907_, 2, v_zetaDeltaFVarIds_2897_);
lean_ctor_set(v_reuseFailAlloc_2907_, 3, v_postponed_2898_);
lean_ctor_set(v_reuseFailAlloc_2907_, 4, v_diag_2899_);
v___x_2904_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_st_ref_set(v___y_2886_, v___x_2904_);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_fst_2893_);
return v___x_2906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2910_, v___y_2911_);
lean_dec(v___y_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2914_, v___y_2916_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2928_, lean_object* v_info_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; lean_object* v_env_2934_; lean_object* v_nextMacroScope_2935_; lean_object* v_ngen_2936_; lean_object* v_auxDeclNGen_2937_; lean_object* v_traceState_2938_; lean_object* v_messages_2939_; lean_object* v_infoState_2940_; lean_object* v_snapshotTasks_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2968_; 
v___x_2933_ = lean_st_ref_take(v___y_2931_);
v_env_2934_ = lean_ctor_get(v___x_2933_, 0);
v_nextMacroScope_2935_ = lean_ctor_get(v___x_2933_, 1);
v_ngen_2936_ = lean_ctor_get(v___x_2933_, 2);
v_auxDeclNGen_2937_ = lean_ctor_get(v___x_2933_, 3);
v_traceState_2938_ = lean_ctor_get(v___x_2933_, 4);
v_messages_2939_ = lean_ctor_get(v___x_2933_, 6);
v_infoState_2940_ = lean_ctor_get(v___x_2933_, 7);
v_snapshotTasks_2941_ = lean_ctor_get(v___x_2933_, 8);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v___x_2933_, 5);
lean_dec(v_unused_2969_);
v___x_2943_ = v___x_2933_;
v_isShared_2944_ = v_isSharedCheck_2968_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_snapshotTasks_2941_);
lean_inc(v_infoState_2940_);
lean_inc(v_messages_2939_);
lean_inc(v_traceState_2938_);
lean_inc(v_auxDeclNGen_2937_);
lean_inc(v_ngen_2936_);
lean_inc(v_nextMacroScope_2935_);
lean_inc(v_env_2934_);
lean_dec(v___x_2933_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2968_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2945_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2934_, v_matcherName_2928_, v_info_2929_);
v___x_2946_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 5, v___x_2946_);
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2948_ = v___x_2943_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_nextMacroScope_2935_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_ngen_2936_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_auxDeclNGen_2937_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v_traceState_2938_);
lean_ctor_set(v_reuseFailAlloc_2967_, 5, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2967_, 6, v_messages_2939_);
lean_ctor_set(v_reuseFailAlloc_2967_, 7, v_infoState_2940_);
lean_ctor_set(v_reuseFailAlloc_2967_, 8, v_snapshotTasks_2941_);
v___x_2948_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v_mctx_2951_; lean_object* v_zetaDeltaFVarIds_2952_; lean_object* v_postponed_2953_; lean_object* v_diag_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2965_; 
v___x_2949_ = lean_st_ref_set(v___y_2931_, v___x_2948_);
v___x_2950_ = lean_st_ref_take(v___y_2930_);
v_mctx_2951_ = lean_ctor_get(v___x_2950_, 0);
v_zetaDeltaFVarIds_2952_ = lean_ctor_get(v___x_2950_, 2);
v_postponed_2953_ = lean_ctor_get(v___x_2950_, 3);
v_diag_2954_ = lean_ctor_get(v___x_2950_, 4);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; 
v_unused_2966_ = lean_ctor_get(v___x_2950_, 1);
lean_dec(v_unused_2966_);
v___x_2956_ = v___x_2950_;
v_isShared_2957_ = v_isSharedCheck_2965_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_diag_2954_);
lean_inc(v_postponed_2953_);
lean_inc(v_zetaDeltaFVarIds_2952_);
lean_inc(v_mctx_2951_);
lean_dec(v___x_2950_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2965_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2958_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2958_);
v___x_2960_ = v___x_2956_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_mctx_2951_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_zetaDeltaFVarIds_2952_);
lean_ctor_set(v_reuseFailAlloc_2964_, 3, v_postponed_2953_);
lean_ctor_set(v_reuseFailAlloc_2964_, 4, v_diag_2954_);
v___x_2960_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_st_ref_set(v___y_2930_, v___x_2960_);
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2970_, lean_object* v_info_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2970_, v_info_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec(v___y_2972_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2976_, lean_object* v_info_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2976_, v_info_2977_, v___y_2979_, v___y_2981_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2984_, lean_object* v_info_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2984_, v_info_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2992_, lean_object* v___x_2993_, lean_object* v_newEqs1_2994_, uint8_t v___x_2995_, uint8_t v___x_2996_, uint8_t v___x_2997_, lean_object* v_ism1_x27_2998_, lean_object* v_ism2_x27_2999_, lean_object* v_newRefls1_3000_, lean_object* v_newEqs2_3001_, lean_object* v_newRefls2_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = l_Lean_mkAppN(v_motive_2992_, v___x_2993_);
v___x_3009_ = l_Array_append___redArg(v_newEqs1_2994_, v_newEqs2_3001_);
v___x_3010_ = l_Lean_Meta_mkForallFVars(v___x_3009_, v___x_3008_, v___x_2995_, v___x_2996_, v___x_2996_, v___x_2997_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec_ref(v___x_3009_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = l_Array_append___redArg(v_ism1_x27_2998_, v_ism2_x27_2999_);
v___x_3013_ = l_Lean_Meta_mkLambdaFVars(v___x_3012_, v_a_3011_, v___x_2995_, v___x_2996_, v___x_2995_, v___x_2996_, v___x_2997_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec_ref(v___x_3012_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3023_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3023_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3023_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3018_ = l_Array_append___redArg(v_newRefls1_3000_, v_newRefls2_3002_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_a_3014_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3019_);
v___x_3021_ = v___x_3016_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref(v_newRefls1_3000_);
v_a_3024_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3013_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3013_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_newRefls1_3000_);
lean_dec_ref(v_ism1_x27_2998_);
v_a_3032_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3010_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3010_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_3040_, lean_object* v___x_3041_, lean_object* v_newEqs1_3042_, lean_object* v___x_3043_, lean_object* v___x_3044_, lean_object* v___x_3045_, lean_object* v_ism1_x27_3046_, lean_object* v_ism2_x27_3047_, lean_object* v_newRefls1_3048_, lean_object* v_newEqs2_3049_, lean_object* v_newRefls2_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
uint8_t v___x_14877__boxed_3056_; uint8_t v___x_14878__boxed_3057_; uint8_t v___x_14879__boxed_3058_; lean_object* v_res_3059_; 
v___x_14877__boxed_3056_ = lean_unbox(v___x_3043_);
v___x_14878__boxed_3057_ = lean_unbox(v___x_3044_);
v___x_14879__boxed_3058_ = lean_unbox(v___x_3045_);
v_res_3059_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_3040_, v___x_3041_, v_newEqs1_3042_, v___x_14877__boxed_3056_, v___x_14878__boxed_3057_, v___x_14879__boxed_3058_, v_ism1_x27_3046_, v_ism2_x27_3047_, v_newRefls1_3048_, v_newEqs2_3049_, v_newRefls2_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v_newRefls2_3050_);
lean_dec_ref(v_newEqs2_3049_);
lean_dec_ref(v_ism2_x27_3047_);
lean_dec_ref(v___x_3041_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_3060_, lean_object* v___x_3061_, uint8_t v___x_3062_, uint8_t v___x_3063_, uint8_t v___x_3064_, lean_object* v_ism1_x27_3065_, lean_object* v_ism2_x27_3066_, lean_object* v_is_3067_, lean_object* v___x_3068_, lean_object* v_newEqs1_3069_, lean_object* v_newRefls1_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___f_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3076_ = lean_box(v___x_3062_);
v___x_3077_ = lean_box(v___x_3063_);
v___x_3078_ = lean_box(v___x_3064_);
lean_inc_ref(v_ism2_x27_3066_);
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3079_, 0, v_motive_3060_);
lean_closure_set(v___f_3079_, 1, v___x_3061_);
lean_closure_set(v___f_3079_, 2, v_newEqs1_3069_);
lean_closure_set(v___f_3079_, 3, v___x_3076_);
lean_closure_set(v___f_3079_, 4, v___x_3077_);
lean_closure_set(v___f_3079_, 5, v___x_3078_);
lean_closure_set(v___f_3079_, 6, v_ism1_x27_3065_);
lean_closure_set(v___f_3079_, 7, v_ism2_x27_3066_);
lean_closure_set(v___f_3079_, 8, v_newRefls1_3070_);
v___x_3080_ = lean_array_push(v_is_3067_, v___x_3068_);
v___x_3081_ = l_Lean_Meta_withNewEqs___redArg(v___x_3080_, v_ism2_x27_3066_, v___f_3079_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_3082_, lean_object* v___x_3083_, lean_object* v___x_3084_, lean_object* v___x_3085_, lean_object* v___x_3086_, lean_object* v_ism1_x27_3087_, lean_object* v_ism2_x27_3088_, lean_object* v_is_3089_, lean_object* v___x_3090_, lean_object* v_newEqs1_3091_, lean_object* v_newRefls1_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
uint8_t v___x_14968__boxed_3098_; uint8_t v___x_14969__boxed_3099_; uint8_t v___x_14970__boxed_3100_; lean_object* v_res_3101_; 
v___x_14968__boxed_3098_ = lean_unbox(v___x_3084_);
v___x_14969__boxed_3099_ = lean_unbox(v___x_3085_);
v___x_14970__boxed_3100_ = lean_unbox(v___x_3086_);
v_res_3101_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_3082_, v___x_3083_, v___x_14968__boxed_3098_, v___x_14969__boxed_3099_, v___x_14970__boxed_3100_, v_ism1_x27_3087_, v_ism2_x27_3088_, v_is_3089_, v___x_3090_, v_newEqs1_3091_, v_newRefls1_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_3102_, uint8_t v___x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_addDecl(v___x_3102_, v___x_3103_, v___y_3106_, v___y_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3110_, lean_object* v___x_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
uint8_t v___x_15010__boxed_3117_; lean_object* v_res_3118_; 
v___x_15010__boxed_3117_ = lean_unbox(v___x_3111_);
v_res_3118_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3110_, v___x_15010__boxed_3117_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
return v_res_3118_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3121_ = l_Lean_stringToMessageData(v___x_3120_);
return v___x_3121_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3124_ = l_Lean_stringToMessageData(v___x_3123_);
return v___x_3124_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = lean_box(0);
v___x_3131_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3132_ = l_Lean_mkConst(v___x_3131_, v___x_3130_);
return v___x_3132_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3135_ = l_Lean_stringToMessageData(v___x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3136_, lean_object* v_a_3137_, lean_object* v_j_3138_, lean_object* v_zs1_3139_, lean_object* v_snd_3140_, uint8_t v___x_3141_, uint8_t v_isZero_3142_, uint8_t v___x_3143_, lean_object* v_alts_3144_, lean_object* v_zs2_3145_, lean_object* v___ctorRet2_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = lean_array_get_borrowed(v___x_3136_, v_a_3137_, v_j_3138_);
lean_inc_ref(v_zs1_3139_);
v___x_3153_ = l_Array_append___redArg(v_zs1_3139_, v_zs2_3145_);
lean_inc(v___x_3152_);
v___x_3154_ = l_Lean_Meta_instantiateForall(v___x_3152_, v___x_3153_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref(v___x_3154_);
v___x_3156_ = lean_box(0);
v___x_3157_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3155_, v___x_3156_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref(v___x_3157_);
v___x_3159_ = l_Lean_Expr_mvarId_x21(v_a_3158_);
v___x_3160_ = lean_array_get_size(v_snd_3140_);
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_box(0);
lean_inc_ref(v___y_3149_);
v___x_3163_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3160_, v___x_3159_, v___x_3161_, v___x_3162_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref(v___x_3163_);
if (lean_obj_tag(v_a_3164_) == 1)
{
lean_object* v_val_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3212_; 
v_val_3165_ = lean_ctor_get(v_a_3164_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_a_3164_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3167_ = v_a_3164_;
v_isShared_3168_ = v_isSharedCheck_3212_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_val_3165_);
lean_dec(v_a_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3212_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_fst_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3210_; 
v_fst_3169_ = lean_ctor_get(v_val_3165_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_val_3165_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v_val_3165_, 1);
lean_dec(v_unused_3211_);
v___x_3171_ = v_val_3165_;
v_isShared_3172_ = v_isSharedCheck_3210_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_fst_3169_);
lean_dec(v_val_3165_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3210_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___y_3174_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v___x_3202_ = lean_array_get_borrowed(v___x_3136_, v_alts_3144_, v_j_3138_);
v___x_3203_ = lean_array_get_size(v_zs1_3139_);
lean_dec_ref(v_zs1_3139_);
v___x_3204_ = lean_unsigned_to_nat(0u);
v___x_3205_ = lean_nat_dec_eq(v___x_3203_, v___x_3204_);
if (v___x_3205_ == 0)
{
lean_inc(v___x_3202_);
v___y_3174_ = v___x_3202_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3206_ = lean_array_get_size(v_zs2_3145_);
v___x_3207_ = lean_nat_dec_eq(v___x_3206_, v___x_3204_);
if (v___x_3207_ == 0)
{
lean_inc(v___x_3202_);
v___y_3174_ = v___x_3202_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3202_);
v___x_3209_ = l_Lean_Expr_app___override(v___x_3202_, v___x_3208_);
v___y_3174_ = v___x_3209_;
goto v___jp_3173_;
}
}
v___jp_3173_:
{
uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = 0;
v___x_3176_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3176_, 0, v___x_3175_);
lean_ctor_set_uint8(v___x_3176_, 1, v___x_3141_);
lean_ctor_set_uint8(v___x_3176_, 2, v_isZero_3142_);
lean_ctor_set_uint8(v___x_3176_, 3, v___x_3141_);
lean_inc_ref(v___y_3174_);
lean_inc(v_fst_3169_);
v___x_3177_ = l_Lean_MVarId_apply(v_fst_3169_, v___y_3174_, v___x_3176_, v___x_3162_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref(v___x_3177_);
if (lean_obj_tag(v_a_3178_) == 0)
{
lean_object* v___x_3179_; lean_object* v_a_3180_; lean_object* v___x_3181_; 
lean_dec_ref(v___y_3174_);
lean_del_object(v___x_3171_);
lean_dec(v_fst_3169_);
lean_del_object(v___x_3167_);
v___x_3179_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3158_, v___y_3148_);
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3179_);
v___x_3181_ = l_Lean_Meta_mkLambdaFVars(v___x_3153_, v_a_3180_, v_isZero_3142_, v___x_3141_, v_isZero_3142_, v___x_3141_, v___x_3143_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec_ref(v___x_3153_);
return v___x_3181_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; 
lean_dec(v_a_3178_);
lean_dec(v_a_3158_);
lean_dec_ref(v___x_3153_);
v___x_3182_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3183_ = l_Lean_MessageData_ofExpr(v___y_3174_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 7);
lean_ctor_set(v___x_3171_, 1, v___x_3183_);
lean_ctor_set(v___x_3171_, 0, v___x_3182_);
v___x_3185_ = v___x_3171_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3182_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3186_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3185_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v_fst_3169_);
v___x_3189_ = v___x_3167_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_fst_3169_);
v___x_3189_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3187_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3190_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v___y_3174_);
lean_del_object(v___x_3171_);
lean_dec(v_fst_3169_);
lean_del_object(v___x_3167_);
lean_dec(v_a_3158_);
lean_dec_ref(v___x_3153_);
v_a_3194_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3177_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3177_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_dec(v_a_3164_);
lean_dec(v_a_3158_);
lean_dec_ref(v___x_3153_);
lean_dec_ref(v_zs1_3139_);
v___x_3213_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3214_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3213_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
return v___x_3214_;
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec(v_a_3158_);
lean_dec_ref(v___x_3153_);
lean_dec_ref(v_zs1_3139_);
v_a_3215_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3163_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3163_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_dec_ref(v___x_3153_);
lean_dec_ref(v_zs1_3139_);
return v___x_3157_;
}
}
else
{
lean_dec_ref(v___x_3153_);
lean_dec_ref(v_zs1_3139_);
return v___x_3154_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3223_, lean_object* v_a_3224_, lean_object* v_j_3225_, lean_object* v_zs1_3226_, lean_object* v_snd_3227_, lean_object* v___x_3228_, lean_object* v_isZero_3229_, lean_object* v___x_3230_, lean_object* v_alts_3231_, lean_object* v_zs2_3232_, lean_object* v___ctorRet2_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v___x_15069__boxed_3239_; uint8_t v_isZero_boxed_3240_; uint8_t v___x_15070__boxed_3241_; lean_object* v_res_3242_; 
v___x_15069__boxed_3239_ = lean_unbox(v___x_3228_);
v_isZero_boxed_3240_ = lean_unbox(v_isZero_3229_);
v___x_15070__boxed_3241_ = lean_unbox(v___x_3230_);
v_res_3242_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3223_, v_a_3224_, v_j_3225_, v_zs1_3226_, v_snd_3227_, v___x_15069__boxed_3239_, v_isZero_boxed_3240_, v___x_15070__boxed_3241_, v_alts_3231_, v_zs2_3232_, v___ctorRet2_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___ctorRet2_3233_);
lean_dec_ref(v_zs2_3232_);
lean_dec_ref(v_alts_3231_);
lean_dec_ref(v_snd_3227_);
lean_dec(v_j_3225_);
lean_dec_ref(v_a_3224_);
lean_dec_ref(v___x_3223_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3243_, lean_object* v_a_3244_, lean_object* v_j_3245_, lean_object* v_snd_3246_, uint8_t v___x_3247_, uint8_t v_isZero_3248_, uint8_t v___x_3249_, lean_object* v_alts_3250_, lean_object* v_a_3251_, lean_object* v_zs1_3252_, lean_object* v___ctorRet1_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; 
v___x_3259_ = lean_box(v___x_3247_);
v___x_3260_ = lean_box(v_isZero_3248_);
v___x_3261_ = lean_box(v___x_3249_);
v___f_3262_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3262_, 0, v___x_3243_);
lean_closure_set(v___f_3262_, 1, v_a_3244_);
lean_closure_set(v___f_3262_, 2, v_j_3245_);
lean_closure_set(v___f_3262_, 3, v_zs1_3252_);
lean_closure_set(v___f_3262_, 4, v_snd_3246_);
lean_closure_set(v___f_3262_, 5, v___x_3259_);
lean_closure_set(v___f_3262_, 6, v___x_3260_);
lean_closure_set(v___f_3262_, 7, v___x_3261_);
lean_closure_set(v___f_3262_, 8, v_alts_3250_);
v___x_3263_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3251_, v___f_3262_, v_isZero_3248_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3264_, lean_object* v_a_3265_, lean_object* v_j_3266_, lean_object* v_snd_3267_, lean_object* v___x_3268_, lean_object* v_isZero_3269_, lean_object* v___x_3270_, lean_object* v_alts_3271_, lean_object* v_a_3272_, lean_object* v_zs1_3273_, lean_object* v___ctorRet1_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v___x_15262__boxed_3280_; uint8_t v_isZero_boxed_3281_; uint8_t v___x_15263__boxed_3282_; lean_object* v_res_3283_; 
v___x_15262__boxed_3280_ = lean_unbox(v___x_3268_);
v_isZero_boxed_3281_ = lean_unbox(v_isZero_3269_);
v___x_15263__boxed_3282_ = lean_unbox(v___x_3270_);
v_res_3283_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3264_, v_a_3265_, v_j_3266_, v_snd_3267_, v___x_15262__boxed_3280_, v_isZero_boxed_3281_, v___x_15263__boxed_3282_, v_alts_3271_, v_a_3272_, v_zs1_3273_, v___ctorRet1_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v___ctorRet1_3274_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3284_, lean_object* v_params_3285_, lean_object* v_a_3286_, lean_object* v_snd_3287_, lean_object* v_alts_3288_, lean_object* v_as_3289_, lean_object* v_i_3290_, lean_object* v_j_3291_, lean_object* v_bs_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_zero_3298_; uint8_t v_isZero_3299_; 
v_zero_3298_ = lean_unsigned_to_nat(0u);
v_isZero_3299_ = lean_nat_dec_eq(v_i_3290_, v_zero_3298_);
if (v_isZero_3299_ == 1)
{
lean_object* v___x_3300_; 
lean_dec(v_j_3291_);
lean_dec(v_i_3290_);
lean_dec_ref(v_alts_3288_);
lean_dec_ref(v_snd_3287_);
lean_dec_ref(v_a_3286_);
lean_dec(v_tail_3284_);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v_bs_3292_);
return v___x_3300_;
}
else
{
lean_object* v_one_3301_; lean_object* v_n_3302_; lean_object* v___y_3304_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_one_3301_ = lean_unsigned_to_nat(1u);
v_n_3302_ = lean_nat_sub(v_i_3290_, v_one_3301_);
lean_dec(v_i_3290_);
v___x_3317_ = lean_array_fget_borrowed(v_as_3289_, v_j_3291_);
lean_inc(v_tail_3284_);
lean_inc(v___x_3317_);
v___x_3318_ = l_Lean_mkConst(v___x_3317_, v_tail_3284_);
v___x_3319_ = l_Lean_mkAppN(v___x_3318_, v_params_3285_);
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3295_);
lean_inc(v___y_3294_);
lean_inc_ref(v___y_3293_);
v___x_3320_ = lean_infer_type(v___x_3319_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; uint8_t v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___f_3328_; lean_object* v___x_3329_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref(v___x_3320_);
v___x_3322_ = l_Lean_instInhabitedExpr;
v___x_3323_ = 1;
v___x_3324_ = 1;
v___x_3325_ = lean_box(v___x_3323_);
v___x_3326_ = lean_box(v_isZero_3299_);
v___x_3327_ = lean_box(v___x_3324_);
lean_inc(v_a_3321_);
lean_inc_ref(v_alts_3288_);
lean_inc_ref(v_snd_3287_);
lean_inc(v_j_3291_);
lean_inc_ref(v_a_3286_);
v___f_3328_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3328_, 0, v___x_3322_);
lean_closure_set(v___f_3328_, 1, v_a_3286_);
lean_closure_set(v___f_3328_, 2, v_j_3291_);
lean_closure_set(v___f_3328_, 3, v_snd_3287_);
lean_closure_set(v___f_3328_, 4, v___x_3325_);
lean_closure_set(v___f_3328_, 5, v___x_3326_);
lean_closure_set(v___f_3328_, 6, v___x_3327_);
lean_closure_set(v___f_3328_, 7, v_alts_3288_);
lean_closure_set(v___f_3328_, 8, v_a_3321_);
v___x_3329_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3321_, v___f_3328_, v_isZero_3299_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
v___y_3304_ = v___x_3329_;
goto v___jp_3303_;
}
else
{
v___y_3304_ = v___x_3320_;
goto v___jp_3303_;
}
v___jp_3303_:
{
if (lean_obj_tag(v___y_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_a_3305_ = lean_ctor_get(v___y_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref(v___y_3304_);
v___x_3306_ = lean_nat_add(v_j_3291_, v_one_3301_);
lean_dec(v_j_3291_);
v___x_3307_ = lean_array_push(v_bs_3292_, v_a_3305_);
v_i_3290_ = v_n_3302_;
v_j_3291_ = v___x_3306_;
v_bs_3292_ = v___x_3307_;
goto _start;
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v_n_3302_);
lean_dec_ref(v_bs_3292_);
lean_dec(v_j_3291_);
lean_dec_ref(v_alts_3288_);
lean_dec_ref(v_snd_3287_);
lean_dec_ref(v_a_3286_);
lean_dec(v_tail_3284_);
v_a_3309_ = lean_ctor_get(v___y_3304_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___y_3304_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___y_3304_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___y_3304_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3330_, lean_object* v_params_3331_, lean_object* v_a_3332_, lean_object* v_snd_3333_, lean_object* v_alts_3334_, lean_object* v_as_3335_, lean_object* v_i_3336_, lean_object* v_j_3337_, lean_object* v_bs_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3330_, v_params_3331_, v_a_3332_, v_snd_3333_, v_alts_3334_, v_as_3335_, v_i_3336_, v_j_3337_, v_bs_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec_ref(v_as_3335_);
lean_dec_ref(v_params_3331_);
return v_res_3344_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = lean_box(0);
v___x_3346_ = lean_unsigned_to_nat(16u);
v___x_3347_ = lean_mk_array(v___x_3346_, v___x_3345_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3348_, lean_object* v___x_3349_, uint8_t v___x_3350_, uint8_t v___x_3351_, uint8_t v___x_3352_, lean_object* v_ism1_x27_3353_, lean_object* v_is_3354_, lean_object* v___x_3355_, lean_object* v___x_3356_, lean_object* v___x_3357_, lean_object* v___x_3358_, lean_object* v_params_3359_, lean_object* v___x_3360_, lean_object* v___x_3361_, lean_object* v_heq_3362_, lean_object* v_val_3363_, lean_object* v___x_3364_, lean_object* v_tail_3365_, lean_object* v_alts_3366_, lean_object* v___x_3367_, lean_object* v___x_3368_, lean_object* v___x_3369_, lean_object* v_declName_3370_, lean_object* v_levelParams_3371_, lean_object* v_numIndices_3372_, lean_object* v___x_3373_, lean_object* v_numParams_3374_, lean_object* v_snd_3375_, lean_object* v_ism2_x27_3376_, lean_object* v_x_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3383_ = lean_box(v___x_3350_);
v___x_3384_ = lean_box(v___x_3351_);
v___x_3385_ = lean_box(v___x_3352_);
lean_inc_ref(v___x_3355_);
lean_inc_ref(v_is_3354_);
lean_inc_ref(v_ism1_x27_3353_);
lean_inc_ref(v_motive_3348_);
v___f_3386_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3386_, 0, v_motive_3348_);
lean_closure_set(v___f_3386_, 1, v___x_3349_);
lean_closure_set(v___f_3386_, 2, v___x_3383_);
lean_closure_set(v___f_3386_, 3, v___x_3384_);
lean_closure_set(v___f_3386_, 4, v___x_3385_);
lean_closure_set(v___f_3386_, 5, v_ism1_x27_3353_);
lean_closure_set(v___f_3386_, 6, v_ism2_x27_3376_);
lean_closure_set(v___f_3386_, 7, v_is_3354_);
lean_closure_set(v___f_3386_, 8, v___x_3355_);
lean_inc_ref(v___x_3356_);
lean_inc_ref(v_is_3354_);
v___x_3387_ = lean_array_push(v_is_3354_, v___x_3356_);
v___x_3388_ = l_Lean_Meta_withNewEqs___redArg(v___x_3387_, v_ism1_x27_3353_, v___f_3386_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v_fst_3390_; lean_object* v_snd_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3493_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref(v___x_3388_);
v_fst_3390_ = lean_ctor_get(v_a_3389_, 0);
v_snd_3391_ = lean_ctor_get(v_a_3389_, 1);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_3389_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3393_ = v_a_3389_;
v_isShared_3394_ = v_isSharedCheck_3493_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_snd_3391_);
lean_inc(v_fst_3390_);
lean_dec(v_a_3389_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3493_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3395_ = l_Lean_mkConst(v___x_3357_, v___x_3358_);
v___x_3396_ = l_Lean_mkAppN(v___x_3395_, v_params_3359_);
v___x_3397_ = l_Lean_Expr_app___override(v___x_3396_, v_fst_3390_);
lean_inc_ref(v_is_3354_);
v___x_3398_ = l_Array_append___redArg(v_is_3354_, v___x_3360_);
v___x_3399_ = l_Array_append___redArg(v___x_3398_, v_is_3354_);
v___x_3400_ = l_Array_append___redArg(v___x_3399_, v___x_3361_);
v___x_3401_ = l_Lean_mkAppN(v___x_3397_, v___x_3400_);
lean_dec_ref(v___x_3400_);
lean_inc_ref(v_heq_3362_);
v___x_3402_ = l_Lean_Expr_app___override(v___x_3401_, v_heq_3362_);
v___x_3403_ = l_Lean_InductiveVal_numCtors(v_val_3363_);
lean_inc_ref(v___x_3402_);
v___x_3404_ = l_Lean_Meta_inferArgumentTypesN(v___x_3403_, v___x_3402_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref(v___x_3404_);
v___x_3406_ = lean_mk_empty_array_with_capacity(v___x_3364_);
lean_inc(v___x_3368_);
lean_inc_ref(v_alts_3366_);
lean_inc(v_snd_3391_);
v___x_3407_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3365_, v_params_3359_, v_a_3405_, v_snd_3391_, v_alts_3366_, v___x_3367_, v___x_3364_, v___x_3368_, v___x_3406_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = l_Lean_mkAppN(v___x_3402_, v_a_3408_);
lean_dec(v_a_3408_);
v___x_3410_ = l_Lean_mkAppN(v___x_3409_, v_snd_3391_);
lean_dec(v_snd_3391_);
lean_inc_ref(v___x_3369_);
v___x_3411_ = lean_array_push(v___x_3369_, v_motive_3348_);
v___x_3412_ = l_Array_append___redArg(v_params_3359_, v___x_3411_);
lean_dec_ref(v___x_3411_);
v___x_3413_ = l_Array_append___redArg(v___x_3412_, v_is_3354_);
lean_dec_ref(v_is_3354_);
v___x_3414_ = lean_unsigned_to_nat(2u);
v___x_3415_ = lean_mk_empty_array_with_capacity(v___x_3414_);
v___x_3416_ = lean_array_push(v___x_3415_, v___x_3356_);
v___x_3417_ = lean_array_push(v___x_3416_, v___x_3355_);
v___x_3418_ = l_Array_append___redArg(v___x_3413_, v___x_3417_);
lean_dec_ref(v___x_3417_);
v___x_3419_ = lean_array_push(v___x_3369_, v_heq_3362_);
v___x_3420_ = l_Array_append___redArg(v___x_3418_, v___x_3419_);
lean_dec_ref(v___x_3419_);
v___x_3421_ = l_Array_append___redArg(v___x_3420_, v_alts_3366_);
lean_dec_ref(v_alts_3366_);
v___x_3422_ = l_Lean_Meta_mkLambdaFVars(v___x_3421_, v___x_3410_, v___x_3350_, v___x_3351_, v___x_3350_, v___x_3351_, v___x_3352_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec_ref(v___x_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3424_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref(v___x_3422_);
lean_inc(v___y_3381_);
lean_inc_ref(v___y_3380_);
lean_inc(v___y_3379_);
lean_inc_ref(v___y_3378_);
lean_inc(v_a_3423_);
v___x_3424_ = lean_infer_type(v_a_3423_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3460_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref(v___x_3424_);
v___x_3426_ = lean_box(1);
lean_inc(v_declName_3370_);
v___x_3427_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3370_, v_levelParams_3371_, v_a_3425_, v_a_3423_, v___x_3426_, v___y_3381_);
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3460_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3460_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set_tag(v___x_3430_, 1);
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; lean_object* v___f_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3434_ = lean_box(v___x_3350_);
lean_inc_ref(v___x_3433_);
v___f_3435_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3435_, 0, v___x_3433_);
lean_closure_set(v___f_3435_, 1, v___x_3434_);
v___x_3436_ = lean_nat_add(v_numIndices_3372_, v___x_3373_);
lean_inc(v___x_3368_);
v___x_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3368_);
v___x_3438_ = lean_box(0);
v___x_3439_ = lean_mk_empty_array_with_capacity(v___x_3373_);
v___x_3440_ = lean_array_push(v___x_3439_, v___x_3438_);
v___x_3441_ = lean_array_push(v___x_3440_, v___x_3438_);
v___x_3442_ = lean_array_push(v___x_3441_, v___x_3438_);
v___x_3443_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v___x_3443_);
lean_ctor_set(v___x_3393_, 0, v___x_3368_);
v___x_3445_ = v___x_3393_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; uint8_t v___y_3448_; uint8_t v___x_3457_; 
v___x_3446_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3446_, 0, v_numParams_3374_);
lean_ctor_set(v___x_3446_, 1, v___x_3436_);
lean_ctor_set(v___x_3446_, 2, v_snd_3375_);
lean_ctor_set(v___x_3446_, 3, v___x_3437_);
lean_ctor_set(v___x_3446_, 4, v___x_3442_);
lean_ctor_set(v___x_3446_, 5, v___x_3445_);
v___x_3457_ = l_Lean_isPrivateName(v_declName_3370_);
if (v___x_3457_ == 0)
{
v___y_3448_ = v___x_3351_;
goto v___jp_3447_;
}
else
{
v___y_3448_ = v___x_3350_;
goto v___jp_3447_;
}
v___jp_3447_:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3435_, v___y_3448_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec_ref(v___x_3449_);
v___x_3450_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3370_);
v___x_3451_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3450_, v_declName_3370_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3452_; uint8_t v___x_3453_; lean_object* v___x_3454_; 
lean_dec_ref(v___x_3451_);
lean_inc(v_declName_3370_);
v___x_3452_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3370_, v___x_3446_, v___y_3379_, v___y_3381_);
lean_dec_ref(v___x_3452_);
v___x_3453_ = 0;
lean_inc(v_declName_3370_);
v___x_3454_ = l_Lean_Meta_setInlineAttribute(v_declName_3370_, v___x_3453_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; 
lean_dec_ref(v___x_3454_);
v___x_3455_ = l_Lean_enableRealizationsForConst(v_declName_3370_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v___x_3456_; 
lean_dec_ref(v___x_3455_);
v___x_3456_ = l_Lean_compileDecl(v___x_3433_, v___x_3351_, v___y_3380_, v___y_3381_);
return v___x_3456_;
}
else
{
lean_dec_ref(v___x_3433_);
return v___x_3455_;
}
}
else
{
lean_dec_ref(v___x_3433_);
lean_dec(v_declName_3370_);
return v___x_3454_;
}
}
else
{
lean_dec_ref(v___x_3446_);
lean_dec_ref(v___x_3433_);
lean_dec(v_declName_3370_);
return v___x_3451_;
}
}
else
{
lean_dec_ref(v___x_3446_);
lean_dec_ref(v___x_3433_);
lean_dec(v_declName_3370_);
return v___x_3449_;
}
}
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_a_3423_);
lean_del_object(v___x_3393_);
lean_dec_ref(v_snd_3375_);
lean_dec(v_numParams_3374_);
lean_dec(v_levelParams_3371_);
lean_dec(v_declName_3370_);
lean_dec(v___x_3368_);
v_a_3461_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3424_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3424_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_del_object(v___x_3393_);
lean_dec_ref(v_snd_3375_);
lean_dec(v_numParams_3374_);
lean_dec(v_levelParams_3371_);
lean_dec(v_declName_3370_);
lean_dec(v___x_3368_);
v_a_3469_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3422_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3422_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref(v___x_3402_);
lean_del_object(v___x_3393_);
lean_dec(v_snd_3391_);
lean_dec_ref(v_snd_3375_);
lean_dec(v_numParams_3374_);
lean_dec(v_levelParams_3371_);
lean_dec(v_declName_3370_);
lean_dec_ref(v___x_3369_);
lean_dec(v___x_3368_);
lean_dec_ref(v_alts_3366_);
lean_dec_ref(v_heq_3362_);
lean_dec_ref(v_params_3359_);
lean_dec_ref(v___x_3356_);
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_is_3354_);
lean_dec_ref(v_motive_3348_);
v_a_3477_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3407_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3407_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___x_3402_);
lean_del_object(v___x_3393_);
lean_dec(v_snd_3391_);
lean_dec_ref(v_snd_3375_);
lean_dec(v_numParams_3374_);
lean_dec(v_levelParams_3371_);
lean_dec(v_declName_3370_);
lean_dec_ref(v___x_3369_);
lean_dec(v___x_3368_);
lean_dec_ref(v_alts_3366_);
lean_dec(v_tail_3365_);
lean_dec(v___x_3364_);
lean_dec_ref(v_heq_3362_);
lean_dec_ref(v_params_3359_);
lean_dec_ref(v___x_3356_);
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_is_3354_);
lean_dec_ref(v_motive_3348_);
v_a_3485_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3404_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3404_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v_snd_3375_);
lean_dec(v_numParams_3374_);
lean_dec(v_levelParams_3371_);
lean_dec(v_declName_3370_);
lean_dec_ref(v___x_3369_);
lean_dec(v___x_3368_);
lean_dec_ref(v_alts_3366_);
lean_dec(v_tail_3365_);
lean_dec(v___x_3364_);
lean_dec_ref(v_heq_3362_);
lean_dec_ref(v_params_3359_);
lean_dec(v___x_3358_);
lean_dec(v___x_3357_);
lean_dec_ref(v___x_3356_);
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_is_3354_);
lean_dec_ref(v_motive_3348_);
v_a_3494_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3388_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3388_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3502_ = _args[0];
lean_object* v___x_3503_ = _args[1];
lean_object* v___x_3504_ = _args[2];
lean_object* v___x_3505_ = _args[3];
lean_object* v___x_3506_ = _args[4];
lean_object* v_ism1_x27_3507_ = _args[5];
lean_object* v_is_3508_ = _args[6];
lean_object* v___x_3509_ = _args[7];
lean_object* v___x_3510_ = _args[8];
lean_object* v___x_3511_ = _args[9];
lean_object* v___x_3512_ = _args[10];
lean_object* v_params_3513_ = _args[11];
lean_object* v___x_3514_ = _args[12];
lean_object* v___x_3515_ = _args[13];
lean_object* v_heq_3516_ = _args[14];
lean_object* v_val_3517_ = _args[15];
lean_object* v___x_3518_ = _args[16];
lean_object* v_tail_3519_ = _args[17];
lean_object* v_alts_3520_ = _args[18];
lean_object* v___x_3521_ = _args[19];
lean_object* v___x_3522_ = _args[20];
lean_object* v___x_3523_ = _args[21];
lean_object* v_declName_3524_ = _args[22];
lean_object* v_levelParams_3525_ = _args[23];
lean_object* v_numIndices_3526_ = _args[24];
lean_object* v___x_3527_ = _args[25];
lean_object* v_numParams_3528_ = _args[26];
lean_object* v_snd_3529_ = _args[27];
lean_object* v_ism2_x27_3530_ = _args[28];
lean_object* v_x_3531_ = _args[29];
lean_object* v___y_3532_ = _args[30];
lean_object* v___y_3533_ = _args[31];
lean_object* v___y_3534_ = _args[32];
lean_object* v___y_3535_ = _args[33];
lean_object* v___y_3536_ = _args[34];
_start:
{
uint8_t v___x_15392__boxed_3537_; uint8_t v___x_15393__boxed_3538_; uint8_t v___x_15394__boxed_3539_; lean_object* v_res_3540_; 
v___x_15392__boxed_3537_ = lean_unbox(v___x_3504_);
v___x_15393__boxed_3538_ = lean_unbox(v___x_3505_);
v___x_15394__boxed_3539_ = lean_unbox(v___x_3506_);
v_res_3540_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3502_, v___x_3503_, v___x_15392__boxed_3537_, v___x_15393__boxed_3538_, v___x_15394__boxed_3539_, v_ism1_x27_3507_, v_is_3508_, v___x_3509_, v___x_3510_, v___x_3511_, v___x_3512_, v_params_3513_, v___x_3514_, v___x_3515_, v_heq_3516_, v_val_3517_, v___x_3518_, v_tail_3519_, v_alts_3520_, v___x_3521_, v___x_3522_, v___x_3523_, v_declName_3524_, v_levelParams_3525_, v_numIndices_3526_, v___x_3527_, v_numParams_3528_, v_snd_3529_, v_ism2_x27_3530_, v_x_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec_ref(v_x_3531_);
lean_dec(v___x_3527_);
lean_dec(v_numIndices_3526_);
lean_dec_ref(v___x_3521_);
lean_dec_ref(v_val_3517_);
lean_dec_ref(v___x_3515_);
lean_dec_ref(v___x_3514_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3541_, lean_object* v___x_3542_, uint8_t v___x_3543_, uint8_t v___x_3544_, uint8_t v___x_3545_, lean_object* v_is_3546_, lean_object* v___x_3547_, lean_object* v___x_3548_, lean_object* v___x_3549_, lean_object* v___x_3550_, lean_object* v_params_3551_, lean_object* v___x_3552_, lean_object* v___x_3553_, lean_object* v_heq_3554_, lean_object* v_val_3555_, lean_object* v___x_3556_, lean_object* v_tail_3557_, lean_object* v_alts_3558_, lean_object* v___x_3559_, lean_object* v___x_3560_, lean_object* v___x_3561_, lean_object* v_declName_3562_, lean_object* v_levelParams_3563_, lean_object* v_numIndices_3564_, lean_object* v___x_3565_, lean_object* v_numParams_3566_, lean_object* v_snd_3567_, lean_object* v___x_3568_, lean_object* v___x_3569_, lean_object* v_ism1_x27_3570_, lean_object* v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___f_3580_; lean_object* v___x_3581_; 
v___x_3577_ = lean_box(v___x_3543_);
v___x_3578_ = lean_box(v___x_3544_);
v___x_3579_ = lean_box(v___x_3545_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 35, 28);
lean_closure_set(v___f_3580_, 0, v_motive_3541_);
lean_closure_set(v___f_3580_, 1, v___x_3542_);
lean_closure_set(v___f_3580_, 2, v___x_3577_);
lean_closure_set(v___f_3580_, 3, v___x_3578_);
lean_closure_set(v___f_3580_, 4, v___x_3579_);
lean_closure_set(v___f_3580_, 5, v_ism1_x27_3570_);
lean_closure_set(v___f_3580_, 6, v_is_3546_);
lean_closure_set(v___f_3580_, 7, v___x_3547_);
lean_closure_set(v___f_3580_, 8, v___x_3548_);
lean_closure_set(v___f_3580_, 9, v___x_3549_);
lean_closure_set(v___f_3580_, 10, v___x_3550_);
lean_closure_set(v___f_3580_, 11, v_params_3551_);
lean_closure_set(v___f_3580_, 12, v___x_3552_);
lean_closure_set(v___f_3580_, 13, v___x_3553_);
lean_closure_set(v___f_3580_, 14, v_heq_3554_);
lean_closure_set(v___f_3580_, 15, v_val_3555_);
lean_closure_set(v___f_3580_, 16, v___x_3556_);
lean_closure_set(v___f_3580_, 17, v_tail_3557_);
lean_closure_set(v___f_3580_, 18, v_alts_3558_);
lean_closure_set(v___f_3580_, 19, v___x_3559_);
lean_closure_set(v___f_3580_, 20, v___x_3560_);
lean_closure_set(v___f_3580_, 21, v___x_3561_);
lean_closure_set(v___f_3580_, 22, v_declName_3562_);
lean_closure_set(v___f_3580_, 23, v_levelParams_3563_);
lean_closure_set(v___f_3580_, 24, v_numIndices_3564_);
lean_closure_set(v___f_3580_, 25, v___x_3565_);
lean_closure_set(v___f_3580_, 26, v_numParams_3566_);
lean_closure_set(v___f_3580_, 27, v_snd_3567_);
v___x_3581_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3568_, v___x_3569_, v___f_3580_, v___x_3543_, v___x_3543_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3582_ = _args[0];
lean_object* v___x_3583_ = _args[1];
lean_object* v___x_3584_ = _args[2];
lean_object* v___x_3585_ = _args[3];
lean_object* v___x_3586_ = _args[4];
lean_object* v_is_3587_ = _args[5];
lean_object* v___x_3588_ = _args[6];
lean_object* v___x_3589_ = _args[7];
lean_object* v___x_3590_ = _args[8];
lean_object* v___x_3591_ = _args[9];
lean_object* v_params_3592_ = _args[10];
lean_object* v___x_3593_ = _args[11];
lean_object* v___x_3594_ = _args[12];
lean_object* v_heq_3595_ = _args[13];
lean_object* v_val_3596_ = _args[14];
lean_object* v___x_3597_ = _args[15];
lean_object* v_tail_3598_ = _args[16];
lean_object* v_alts_3599_ = _args[17];
lean_object* v___x_3600_ = _args[18];
lean_object* v___x_3601_ = _args[19];
lean_object* v___x_3602_ = _args[20];
lean_object* v_declName_3603_ = _args[21];
lean_object* v_levelParams_3604_ = _args[22];
lean_object* v_numIndices_3605_ = _args[23];
lean_object* v___x_3606_ = _args[24];
lean_object* v_numParams_3607_ = _args[25];
lean_object* v_snd_3608_ = _args[26];
lean_object* v___x_3609_ = _args[27];
lean_object* v___x_3610_ = _args[28];
lean_object* v_ism1_x27_3611_ = _args[29];
lean_object* v_x_3612_ = _args[30];
lean_object* v___y_3613_ = _args[31];
lean_object* v___y_3614_ = _args[32];
lean_object* v___y_3615_ = _args[33];
lean_object* v___y_3616_ = _args[34];
lean_object* v___y_3617_ = _args[35];
_start:
{
uint8_t v___x_15716__boxed_3618_; uint8_t v___x_15717__boxed_3619_; uint8_t v___x_15718__boxed_3620_; lean_object* v_res_3621_; 
v___x_15716__boxed_3618_ = lean_unbox(v___x_3584_);
v___x_15717__boxed_3619_ = lean_unbox(v___x_3585_);
v___x_15718__boxed_3620_ = lean_unbox(v___x_3586_);
v_res_3621_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3582_, v___x_3583_, v___x_15716__boxed_3618_, v___x_15717__boxed_3619_, v___x_15718__boxed_3620_, v_is_3587_, v___x_3588_, v___x_3589_, v___x_3590_, v___x_3591_, v_params_3592_, v___x_3593_, v___x_3594_, v_heq_3595_, v_val_3596_, v___x_3597_, v_tail_3598_, v_alts_3599_, v___x_3600_, v___x_3601_, v___x_3602_, v_declName_3603_, v_levelParams_3604_, v_numIndices_3605_, v___x_3606_, v_numParams_3607_, v_snd_3608_, v___x_3609_, v___x_3610_, v_ism1_x27_3611_, v_x_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v_x_3612_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3622_, lean_object* v___x_3623_, lean_object* v_motive_3624_, lean_object* v___x_3625_, uint8_t v___x_3626_, uint8_t v___x_3627_, uint8_t v___x_3628_, lean_object* v_is_3629_, lean_object* v___x_3630_, lean_object* v___x_3631_, lean_object* v___x_3632_, lean_object* v___x_3633_, lean_object* v_params_3634_, lean_object* v___x_3635_, lean_object* v___x_3636_, lean_object* v_heq_3637_, lean_object* v_val_3638_, lean_object* v___x_3639_, lean_object* v_tail_3640_, lean_object* v___x_3641_, lean_object* v___x_3642_, lean_object* v___x_3643_, lean_object* v_declName_3644_, lean_object* v_levelParams_3645_, lean_object* v___x_3646_, lean_object* v_numParams_3647_, lean_object* v_snd_3648_, lean_object* v___x_3649_, lean_object* v_alts_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___f_3661_; lean_object* v___x_3662_; 
v___x_3656_ = lean_nat_add(v_numIndices_3622_, v___x_3623_);
v___x_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3656_);
v___x_3658_ = lean_box(v___x_3626_);
v___x_3659_ = lean_box(v___x_3627_);
v___x_3660_ = lean_box(v___x_3628_);
lean_inc_ref(v___x_3657_);
lean_inc_ref(v___x_3649_);
v___f_3661_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 36, 29);
lean_closure_set(v___f_3661_, 0, v_motive_3624_);
lean_closure_set(v___f_3661_, 1, v___x_3625_);
lean_closure_set(v___f_3661_, 2, v___x_3658_);
lean_closure_set(v___f_3661_, 3, v___x_3659_);
lean_closure_set(v___f_3661_, 4, v___x_3660_);
lean_closure_set(v___f_3661_, 5, v_is_3629_);
lean_closure_set(v___f_3661_, 6, v___x_3630_);
lean_closure_set(v___f_3661_, 7, v___x_3631_);
lean_closure_set(v___f_3661_, 8, v___x_3632_);
lean_closure_set(v___f_3661_, 9, v___x_3633_);
lean_closure_set(v___f_3661_, 10, v_params_3634_);
lean_closure_set(v___f_3661_, 11, v___x_3635_);
lean_closure_set(v___f_3661_, 12, v___x_3636_);
lean_closure_set(v___f_3661_, 13, v_heq_3637_);
lean_closure_set(v___f_3661_, 14, v_val_3638_);
lean_closure_set(v___f_3661_, 15, v___x_3639_);
lean_closure_set(v___f_3661_, 16, v_tail_3640_);
lean_closure_set(v___f_3661_, 17, v_alts_3650_);
lean_closure_set(v___f_3661_, 18, v___x_3641_);
lean_closure_set(v___f_3661_, 19, v___x_3642_);
lean_closure_set(v___f_3661_, 20, v___x_3643_);
lean_closure_set(v___f_3661_, 21, v_declName_3644_);
lean_closure_set(v___f_3661_, 22, v_levelParams_3645_);
lean_closure_set(v___f_3661_, 23, v_numIndices_3622_);
lean_closure_set(v___f_3661_, 24, v___x_3646_);
lean_closure_set(v___f_3661_, 25, v_numParams_3647_);
lean_closure_set(v___f_3661_, 26, v_snd_3648_);
lean_closure_set(v___f_3661_, 27, v___x_3649_);
lean_closure_set(v___f_3661_, 28, v___x_3657_);
v___x_3662_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3649_, v___x_3657_, v___f_3661_, v___x_3626_, v___x_3626_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3663_ = _args[0];
lean_object* v___x_3664_ = _args[1];
lean_object* v_motive_3665_ = _args[2];
lean_object* v___x_3666_ = _args[3];
lean_object* v___x_3667_ = _args[4];
lean_object* v___x_3668_ = _args[5];
lean_object* v___x_3669_ = _args[6];
lean_object* v_is_3670_ = _args[7];
lean_object* v___x_3671_ = _args[8];
lean_object* v___x_3672_ = _args[9];
lean_object* v___x_3673_ = _args[10];
lean_object* v___x_3674_ = _args[11];
lean_object* v_params_3675_ = _args[12];
lean_object* v___x_3676_ = _args[13];
lean_object* v___x_3677_ = _args[14];
lean_object* v_heq_3678_ = _args[15];
lean_object* v_val_3679_ = _args[16];
lean_object* v___x_3680_ = _args[17];
lean_object* v_tail_3681_ = _args[18];
lean_object* v___x_3682_ = _args[19];
lean_object* v___x_3683_ = _args[20];
lean_object* v___x_3684_ = _args[21];
lean_object* v_declName_3685_ = _args[22];
lean_object* v_levelParams_3686_ = _args[23];
lean_object* v___x_3687_ = _args[24];
lean_object* v_numParams_3688_ = _args[25];
lean_object* v_snd_3689_ = _args[26];
lean_object* v___x_3690_ = _args[27];
lean_object* v_alts_3691_ = _args[28];
lean_object* v___y_3692_ = _args[29];
lean_object* v___y_3693_ = _args[30];
lean_object* v___y_3694_ = _args[31];
lean_object* v___y_3695_ = _args[32];
lean_object* v___y_3696_ = _args[33];
_start:
{
uint8_t v___x_15805__boxed_3697_; uint8_t v___x_15806__boxed_3698_; uint8_t v___x_15807__boxed_3699_; lean_object* v_res_3700_; 
v___x_15805__boxed_3697_ = lean_unbox(v___x_3667_);
v___x_15806__boxed_3698_ = lean_unbox(v___x_3668_);
v___x_15807__boxed_3699_ = lean_unbox(v___x_3669_);
v_res_3700_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3663_, v___x_3664_, v_motive_3665_, v___x_3666_, v___x_15805__boxed_3697_, v___x_15806__boxed_3698_, v___x_15807__boxed_3699_, v_is_3670_, v___x_3671_, v___x_3672_, v___x_3673_, v___x_3674_, v_params_3675_, v___x_3676_, v___x_3677_, v_heq_3678_, v_val_3679_, v___x_3680_, v_tail_3681_, v___x_3682_, v___x_3683_, v___x_3684_, v_declName_3685_, v_levelParams_3686_, v___x_3687_, v_numParams_3688_, v_snd_3689_, v___x_3690_, v_alts_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___x_3664_);
return v_res_3700_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_box(0);
v___x_3704_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3705_ = l_Lean_mkConst(v___x_3704_, v___x_3703_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v_j_3706_, lean_object* v___x_3707_, lean_object* v_motive_3708_, uint8_t v_isZero_3709_, uint8_t v___x_3710_, uint8_t v___x_3711_, lean_object* v___x_3712_, lean_object* v___x_3713_, lean_object* v___x_3714_, lean_object* v_zs12_3715_, lean_object* v_is_3716_, lean_object* v_fields1_3717_, lean_object* v_fields2_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v_e_3734_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_inc(v_j_3706_);
v___x_3744_ = l_Lean_mkNatLit(v_j_3706_);
v___x_3745_ = l_Lean_Meta_mkEqRefl(v___x_3744_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref(v___x_3745_);
lean_inc_ref(v___x_3707_);
v___x_3747_ = l_Lean_mkAppN(v___x_3707_, v_fields1_3717_);
v___x_3748_ = l_Lean_mkAppN(v___x_3707_, v_fields2_3718_);
v___x_3749_ = lean_unsigned_to_nat(3u);
v___x_3750_ = lean_mk_empty_array_with_capacity(v___x_3749_);
v___x_3751_ = lean_array_push(v___x_3750_, v___x_3747_);
v___x_3752_ = lean_array_push(v___x_3751_, v___x_3748_);
v___x_3753_ = lean_array_push(v___x_3752_, v_a_3746_);
v___x_3754_ = l_Array_append___redArg(v_is_3716_, v___x_3753_);
lean_dec_ref(v___x_3753_);
v___x_3755_ = l_Lean_mkAppN(v_motive_3708_, v___x_3754_);
lean_dec_ref(v___x_3754_);
v___x_3756_ = l_Lean_Meta_mkForallFVars(v_zs12_3715_, v___x_3755_, v_isZero_3709_, v___x_3710_, v___x_3710_, v___x_3711_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref(v___x_3756_);
v___x_3758_ = lean_array_get_size(v_zs12_3715_);
v___x_3759_ = lean_nat_dec_eq(v___x_3758_, v___x_3712_);
if (v___x_3759_ == 0)
{
v_e_3734_ = v_a_3757_;
goto v___jp_3733_;
}
else
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3761_ = l_Lean_mkArrow(v___x_3760_, v_a_3757_, v___y_3721_, v___y_3722_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref(v___x_3761_);
v_e_3734_ = v_a_3762_;
goto v___jp_3733_;
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v___x_3713_);
lean_dec(v___x_3712_);
lean_dec(v_j_3706_);
v_a_3763_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3761_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3761_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec(v___x_3713_);
lean_dec(v___x_3712_);
lean_dec(v_j_3706_);
v_a_3771_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3756_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3756_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v_is_3716_);
lean_dec(v___x_3713_);
lean_dec(v___x_3712_);
lean_dec_ref(v_motive_3708_);
lean_dec_ref(v___x_3707_);
lean_dec(v_j_3706_);
v_a_3779_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3745_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3745_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
v___jp_3724_:
{
lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3727_ = lean_array_get_size(v_zs12_3715_);
v___x_3728_ = lean_nat_dec_eq(v___x_3727_, v___x_3712_);
v___x_3729_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3712_);
lean_ctor_set_uint8(v___x_3729_, sizeof(void*)*2, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___y_3726_);
lean_ctor_set(v___x_3730_, 1, v___y_3725_);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
lean_ctor_set(v___x_3731_, 1, v___x_3729_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
v___jp_3733_:
{
if (lean_obj_tag(v___x_3713_) == 1)
{
lean_object* v_str_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_dec(v_j_3706_);
v_str_3735_ = lean_ctor_get(v___x_3713_, 1);
lean_inc_ref(v_str_3735_);
lean_dec_ref(v___x_3713_);
v___x_3736_ = lean_box(0);
v___x_3737_ = l_Lean_Name_str___override(v___x_3736_, v_str_3735_);
v___y_3725_ = v_e_3734_;
v___y_3726_ = v___x_3737_;
goto v___jp_3724_;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_dec(v___x_3713_);
v___x_3738_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3739_ = lean_nat_add(v_j_3706_, v___x_3714_);
lean_dec(v_j_3706_);
v___x_3740_ = l_Nat_reprFast(v___x_3739_);
v___x_3741_ = lean_string_append(v___x_3738_, v___x_3740_);
lean_dec_ref(v___x_3740_);
v___x_3742_ = lean_box(0);
v___x_3743_ = l_Lean_Name_str___override(v___x_3742_, v___x_3741_);
v___y_3725_ = v_e_3734_;
v___y_3726_ = v___x_3743_;
goto v___jp_3724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_j_3787_ = _args[0];
lean_object* v___x_3788_ = _args[1];
lean_object* v_motive_3789_ = _args[2];
lean_object* v_isZero_3790_ = _args[3];
lean_object* v___x_3791_ = _args[4];
lean_object* v___x_3792_ = _args[5];
lean_object* v___x_3793_ = _args[6];
lean_object* v___x_3794_ = _args[7];
lean_object* v___x_3795_ = _args[8];
lean_object* v_zs12_3796_ = _args[9];
lean_object* v_is_3797_ = _args[10];
lean_object* v_fields1_3798_ = _args[11];
lean_object* v_fields2_3799_ = _args[12];
lean_object* v___y_3800_ = _args[13];
lean_object* v___y_3801_ = _args[14];
lean_object* v___y_3802_ = _args[15];
lean_object* v___y_3803_ = _args[16];
lean_object* v___y_3804_ = _args[17];
_start:
{
uint8_t v_isZero_boxed_3805_; uint8_t v___x_15905__boxed_3806_; uint8_t v___x_15906__boxed_3807_; lean_object* v_res_3808_; 
v_isZero_boxed_3805_ = lean_unbox(v_isZero_3790_);
v___x_15905__boxed_3806_ = lean_unbox(v___x_3791_);
v___x_15906__boxed_3807_ = lean_unbox(v___x_3792_);
v_res_3808_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v_j_3787_, v___x_3788_, v_motive_3789_, v_isZero_boxed_3805_, v___x_15905__boxed_3806_, v___x_15906__boxed_3807_, v___x_3793_, v___x_3794_, v___x_3795_, v_zs12_3796_, v_is_3797_, v_fields1_3798_, v_fields2_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec_ref(v_fields2_3799_);
lean_dec_ref(v_fields1_3798_);
lean_dec_ref(v_zs12_3796_);
lean_dec(v___x_3795_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3809_, lean_object* v_params_3810_, lean_object* v_motive_3811_, lean_object* v_as_3812_, lean_object* v_i_3813_, lean_object* v_j_3814_, lean_object* v_bs_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_zero_3821_; uint8_t v_isZero_3822_; 
v_zero_3821_ = lean_unsigned_to_nat(0u);
v_isZero_3822_ = lean_nat_dec_eq(v_i_3813_, v_zero_3821_);
if (v_isZero_3822_ == 1)
{
lean_object* v___x_3823_; 
lean_dec(v_j_3814_);
lean_dec(v_i_3813_);
lean_dec_ref(v_motive_3811_);
lean_dec(v_tail_3809_);
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v_bs_3815_);
return v___x_3823_;
}
else
{
lean_object* v___x_3824_; uint8_t v___x_3825_; uint8_t v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___f_3833_; lean_object* v___x_3834_; 
v___x_3824_ = lean_unsigned_to_nat(1u);
v___x_3825_ = 1;
v___x_3826_ = 1;
v___x_3827_ = lean_array_fget_borrowed(v_as_3812_, v_j_3814_);
lean_inc(v_tail_3809_);
lean_inc(v___x_3827_);
v___x_3828_ = l_Lean_mkConst(v___x_3827_, v_tail_3809_);
v___x_3829_ = l_Lean_mkAppN(v___x_3828_, v_params_3810_);
v___x_3830_ = lean_box(v_isZero_3822_);
v___x_3831_ = lean_box(v___x_3825_);
v___x_3832_ = lean_box(v___x_3826_);
lean_inc(v___x_3827_);
lean_inc_ref(v_motive_3811_);
lean_inc_ref(v___x_3829_);
lean_inc(v_j_3814_);
v___f_3833_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3833_, 0, v_j_3814_);
lean_closure_set(v___f_3833_, 1, v___x_3829_);
lean_closure_set(v___f_3833_, 2, v_motive_3811_);
lean_closure_set(v___f_3833_, 3, v___x_3830_);
lean_closure_set(v___f_3833_, 4, v___x_3831_);
lean_closure_set(v___f_3833_, 5, v___x_3832_);
lean_closure_set(v___f_3833_, 6, v_zero_3821_);
lean_closure_set(v___f_3833_, 7, v___x_3827_);
lean_closure_set(v___f_3833_, 8, v___x_3824_);
v___x_3834_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3829_, v___f_3833_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v_n_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref(v___x_3834_);
v_n_3836_ = lean_nat_sub(v_i_3813_, v___x_3824_);
lean_dec(v_i_3813_);
v___x_3837_ = lean_nat_add(v_j_3814_, v___x_3824_);
lean_dec(v_j_3814_);
v___x_3838_ = lean_array_push(v_bs_3815_, v_a_3835_);
v_i_3813_ = v_n_3836_;
v_j_3814_ = v___x_3837_;
v_bs_3815_ = v___x_3838_;
goto _start;
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v_bs_3815_);
lean_dec(v_j_3814_);
lean_dec(v_i_3813_);
lean_dec_ref(v_motive_3811_);
lean_dec(v_tail_3809_);
v_a_3840_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3834_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3834_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3848_, lean_object* v_params_3849_, lean_object* v_motive_3850_, lean_object* v_as_3851_, lean_object* v_i_3852_, lean_object* v_j_3853_, lean_object* v_bs_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3848_, v_params_3849_, v_motive_3850_, v_as_3851_, v_i_3852_, v_j_3853_, v_bs_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec_ref(v_as_3851_);
lean_dec_ref(v_params_3849_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3861_, lean_object* v_tail_3862_, lean_object* v_params_3863_, lean_object* v___x_3864_, lean_object* v_numIndices_3865_, lean_object* v___x_3866_, lean_object* v___x_3867_, uint8_t v___x_3868_, uint8_t v___x_3869_, uint8_t v___x_3870_, lean_object* v_is_3871_, lean_object* v___x_3872_, lean_object* v___x_3873_, lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v___x_3876_, lean_object* v___x_3877_, lean_object* v_heq_3878_, lean_object* v_val_3879_, lean_object* v___x_3880_, lean_object* v_declName_3881_, lean_object* v_levelParams_3882_, lean_object* v___x_3883_, lean_object* v_numParams_3884_, lean_object* v___x_3885_, lean_object* v___x_3886_, lean_object* v_motive_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3893_ = lean_array_mk(v_ctors_3861_);
v___x_3894_ = lean_array_get_size(v___x_3893_);
v___x_3895_ = lean_mk_empty_array_with_capacity(v___x_3894_);
lean_inc(v___x_3864_);
lean_inc_ref(v_motive_3887_);
lean_inc(v_tail_3862_);
v___x_3896_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3862_, v_params_3863_, v_motive_3887_, v___x_3893_, v___x_3894_, v___x_3864_, v___x_3895_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; lean_object* v_fst_3899_; lean_object* v_snd_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___f_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref(v___x_3896_);
v___x_3898_ = l_Array_unzip___redArg(v_a_3897_);
lean_dec(v_a_3897_);
v_fst_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_fst_3899_);
v_snd_3900_ = lean_ctor_get(v___x_3898_, 1);
lean_inc(v_snd_3900_);
lean_dec_ref(v___x_3898_);
v___x_3901_ = lean_box(v___x_3868_);
v___x_3902_ = lean_box(v___x_3869_);
v___x_3903_ = lean_box(v___x_3870_);
v___f_3904_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 34, 28);
lean_closure_set(v___f_3904_, 0, v_numIndices_3865_);
lean_closure_set(v___f_3904_, 1, v___x_3866_);
lean_closure_set(v___f_3904_, 2, v_motive_3887_);
lean_closure_set(v___f_3904_, 3, v___x_3867_);
lean_closure_set(v___f_3904_, 4, v___x_3901_);
lean_closure_set(v___f_3904_, 5, v___x_3902_);
lean_closure_set(v___f_3904_, 6, v___x_3903_);
lean_closure_set(v___f_3904_, 7, v_is_3871_);
lean_closure_set(v___f_3904_, 8, v___x_3872_);
lean_closure_set(v___f_3904_, 9, v___x_3873_);
lean_closure_set(v___f_3904_, 10, v___x_3874_);
lean_closure_set(v___f_3904_, 11, v___x_3875_);
lean_closure_set(v___f_3904_, 12, v_params_3863_);
lean_closure_set(v___f_3904_, 13, v___x_3876_);
lean_closure_set(v___f_3904_, 14, v___x_3877_);
lean_closure_set(v___f_3904_, 15, v_heq_3878_);
lean_closure_set(v___f_3904_, 16, v_val_3879_);
lean_closure_set(v___f_3904_, 17, v___x_3894_);
lean_closure_set(v___f_3904_, 18, v_tail_3862_);
lean_closure_set(v___f_3904_, 19, v___x_3893_);
lean_closure_set(v___f_3904_, 20, v___x_3864_);
lean_closure_set(v___f_3904_, 21, v___x_3880_);
lean_closure_set(v___f_3904_, 22, v_declName_3881_);
lean_closure_set(v___f_3904_, 23, v_levelParams_3882_);
lean_closure_set(v___f_3904_, 24, v___x_3883_);
lean_closure_set(v___f_3904_, 25, v_numParams_3884_);
lean_closure_set(v___f_3904_, 26, v_snd_3900_);
lean_closure_set(v___f_3904_, 27, v___x_3885_);
v___x_3905_ = 0;
v___x_3906_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___redArg(v___x_3886_, v_fst_3899_, v___f_3904_, v___x_3905_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
return v___x_3906_;
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec_ref(v___x_3893_);
lean_dec_ref(v_motive_3887_);
lean_dec_ref(v___x_3885_);
lean_dec(v_numParams_3884_);
lean_dec(v___x_3883_);
lean_dec(v_levelParams_3882_);
lean_dec(v_declName_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v_val_3879_);
lean_dec_ref(v_heq_3878_);
lean_dec_ref(v___x_3877_);
lean_dec_ref(v___x_3876_);
lean_dec(v___x_3875_);
lean_dec(v___x_3874_);
lean_dec_ref(v___x_3873_);
lean_dec_ref(v___x_3872_);
lean_dec_ref(v_is_3871_);
lean_dec_ref(v___x_3867_);
lean_dec(v___x_3866_);
lean_dec(v_numIndices_3865_);
lean_dec(v___x_3864_);
lean_dec_ref(v_params_3863_);
lean_dec(v_tail_3862_);
v_a_3907_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3896_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3896_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_3915_ = _args[0];
lean_object* v_tail_3916_ = _args[1];
lean_object* v_params_3917_ = _args[2];
lean_object* v___x_3918_ = _args[3];
lean_object* v_numIndices_3919_ = _args[4];
lean_object* v___x_3920_ = _args[5];
lean_object* v___x_3921_ = _args[6];
lean_object* v___x_3922_ = _args[7];
lean_object* v___x_3923_ = _args[8];
lean_object* v___x_3924_ = _args[9];
lean_object* v_is_3925_ = _args[10];
lean_object* v___x_3926_ = _args[11];
lean_object* v___x_3927_ = _args[12];
lean_object* v___x_3928_ = _args[13];
lean_object* v___x_3929_ = _args[14];
lean_object* v___x_3930_ = _args[15];
lean_object* v___x_3931_ = _args[16];
lean_object* v_heq_3932_ = _args[17];
lean_object* v_val_3933_ = _args[18];
lean_object* v___x_3934_ = _args[19];
lean_object* v_declName_3935_ = _args[20];
lean_object* v_levelParams_3936_ = _args[21];
lean_object* v___x_3937_ = _args[22];
lean_object* v_numParams_3938_ = _args[23];
lean_object* v___x_3939_ = _args[24];
lean_object* v___x_3940_ = _args[25];
lean_object* v_motive_3941_ = _args[26];
lean_object* v___y_3942_ = _args[27];
lean_object* v___y_3943_ = _args[28];
lean_object* v___y_3944_ = _args[29];
lean_object* v___y_3945_ = _args[30];
lean_object* v___y_3946_ = _args[31];
_start:
{
uint8_t v___x_16139__boxed_3947_; uint8_t v___x_16140__boxed_3948_; uint8_t v___x_16141__boxed_3949_; lean_object* v_res_3950_; 
v___x_16139__boxed_3947_ = lean_unbox(v___x_3922_);
v___x_16140__boxed_3948_ = lean_unbox(v___x_3923_);
v___x_16141__boxed_3949_ = lean_unbox(v___x_3924_);
v_res_3950_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_3915_, v_tail_3916_, v_params_3917_, v___x_3918_, v_numIndices_3919_, v___x_3920_, v___x_3921_, v___x_16139__boxed_3947_, v___x_16140__boxed_3948_, v___x_16141__boxed_3949_, v_is_3925_, v___x_3926_, v___x_3927_, v___x_3928_, v___x_3929_, v___x_3930_, v___x_3931_, v_heq_3932_, v_val_3933_, v___x_3934_, v_declName_3935_, v_levelParams_3936_, v___x_3937_, v_numParams_3938_, v___x_3939_, v___x_3940_, v_motive_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_3951_, lean_object* v___x_3952_, lean_object* v_is_3953_, lean_object* v_head_3954_, lean_object* v_ctors_3955_, lean_object* v_tail_3956_, lean_object* v_params_3957_, lean_object* v___x_3958_, lean_object* v_numIndices_3959_, lean_object* v___x_3960_, lean_object* v___x_3961_, lean_object* v___x_3962_, lean_object* v___x_3963_, lean_object* v___x_3964_, lean_object* v_val_3965_, lean_object* v___x_3966_, lean_object* v_declName_3967_, lean_object* v_levelParams_3968_, lean_object* v_numParams_3969_, lean_object* v___x_3970_, lean_object* v___x_3971_, lean_object* v_heq_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; uint8_t v___x_3986_; uint8_t v___x_3987_; lean_object* v___x_3988_; 
v___x_3978_ = lean_unsigned_to_nat(3u);
v___x_3979_ = lean_mk_empty_array_with_capacity(v___x_3978_);
lean_inc_ref(v___x_3951_);
v___x_3980_ = lean_array_push(v___x_3979_, v___x_3951_);
lean_inc_ref(v___x_3952_);
v___x_3981_ = lean_array_push(v___x_3980_, v___x_3952_);
lean_inc_ref(v_heq_3972_);
v___x_3982_ = lean_array_push(v___x_3981_, v_heq_3972_);
lean_inc_ref(v_is_3953_);
v___x_3983_ = l_Array_append___redArg(v_is_3953_, v___x_3982_);
lean_dec_ref(v___x_3982_);
v___x_3984_ = l_Lean_mkSort(v_head_3954_);
v___x_3985_ = 0;
v___x_3986_ = 1;
v___x_3987_ = 1;
v___x_3988_ = l_Lean_Meta_mkForallFVars(v___x_3983_, v___x_3984_, v___x_3985_, v___x_3986_, v___x_3986_, v___x_3987_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___f_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; lean_object* v___x_3996_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_a_3989_);
lean_dec_ref(v___x_3988_);
v___x_3990_ = lean_box(v___x_3985_);
v___x_3991_ = lean_box(v___x_3986_);
v___x_3992_ = lean_box(v___x_3987_);
v___f_3993_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 32, 26);
lean_closure_set(v___f_3993_, 0, v_ctors_3955_);
lean_closure_set(v___f_3993_, 1, v_tail_3956_);
lean_closure_set(v___f_3993_, 2, v_params_3957_);
lean_closure_set(v___f_3993_, 3, v___x_3958_);
lean_closure_set(v___f_3993_, 4, v_numIndices_3959_);
lean_closure_set(v___f_3993_, 5, v___x_3960_);
lean_closure_set(v___f_3993_, 6, v___x_3983_);
lean_closure_set(v___f_3993_, 7, v___x_3990_);
lean_closure_set(v___f_3993_, 8, v___x_3991_);
lean_closure_set(v___f_3993_, 9, v___x_3992_);
lean_closure_set(v___f_3993_, 10, v_is_3953_);
lean_closure_set(v___f_3993_, 11, v___x_3952_);
lean_closure_set(v___f_3993_, 12, v___x_3951_);
lean_closure_set(v___f_3993_, 13, v___x_3961_);
lean_closure_set(v___f_3993_, 14, v___x_3962_);
lean_closure_set(v___f_3993_, 15, v___x_3963_);
lean_closure_set(v___f_3993_, 16, v___x_3964_);
lean_closure_set(v___f_3993_, 17, v_heq_3972_);
lean_closure_set(v___f_3993_, 18, v_val_3965_);
lean_closure_set(v___f_3993_, 19, v___x_3966_);
lean_closure_set(v___f_3993_, 20, v_declName_3967_);
lean_closure_set(v___f_3993_, 21, v_levelParams_3968_);
lean_closure_set(v___f_3993_, 22, v___x_3978_);
lean_closure_set(v___f_3993_, 23, v_numParams_3969_);
lean_closure_set(v___f_3993_, 24, v___x_3970_);
lean_closure_set(v___f_3993_, 25, v___x_3971_);
v___x_3994_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_3995_ = 0;
v___x_3996_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_3994_, v___x_3987_, v_a_3989_, v___f_3993_, v___x_3995_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
return v___x_3996_;
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_dec_ref(v___x_3983_);
lean_dec_ref(v_heq_3972_);
lean_dec_ref(v___x_3970_);
lean_dec(v_numParams_3969_);
lean_dec(v_levelParams_3968_);
lean_dec(v_declName_3967_);
lean_dec_ref(v___x_3966_);
lean_dec_ref(v_val_3965_);
lean_dec_ref(v___x_3964_);
lean_dec_ref(v___x_3963_);
lean_dec(v___x_3962_);
lean_dec(v___x_3961_);
lean_dec(v___x_3960_);
lean_dec(v_numIndices_3959_);
lean_dec(v___x_3958_);
lean_dec_ref(v_params_3957_);
lean_dec(v_tail_3956_);
lean_dec(v_ctors_3955_);
lean_dec_ref(v_is_3953_);
lean_dec_ref(v___x_3952_);
lean_dec_ref(v___x_3951_);
v_a_3997_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3988_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3988_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4005_ = _args[0];
lean_object* v___x_4006_ = _args[1];
lean_object* v_is_4007_ = _args[2];
lean_object* v_head_4008_ = _args[3];
lean_object* v_ctors_4009_ = _args[4];
lean_object* v_tail_4010_ = _args[5];
lean_object* v_params_4011_ = _args[6];
lean_object* v___x_4012_ = _args[7];
lean_object* v_numIndices_4013_ = _args[8];
lean_object* v___x_4014_ = _args[9];
lean_object* v___x_4015_ = _args[10];
lean_object* v___x_4016_ = _args[11];
lean_object* v___x_4017_ = _args[12];
lean_object* v___x_4018_ = _args[13];
lean_object* v_val_4019_ = _args[14];
lean_object* v___x_4020_ = _args[15];
lean_object* v_declName_4021_ = _args[16];
lean_object* v_levelParams_4022_ = _args[17];
lean_object* v_numParams_4023_ = _args[18];
lean_object* v___x_4024_ = _args[19];
lean_object* v___x_4025_ = _args[20];
lean_object* v_heq_4026_ = _args[21];
lean_object* v___y_4027_ = _args[22];
lean_object* v___y_4028_ = _args[23];
lean_object* v___y_4029_ = _args[24];
lean_object* v___y_4030_ = _args[25];
lean_object* v___y_4031_ = _args[26];
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4005_, v___x_4006_, v_is_4007_, v_head_4008_, v_ctors_4009_, v_tail_4010_, v_params_4011_, v___x_4012_, v_numIndices_4013_, v___x_4014_, v___x_4015_, v___x_4016_, v___x_4017_, v___x_4018_, v_val_4019_, v___x_4020_, v_declName_4021_, v_levelParams_4022_, v_numParams_4023_, v___x_4024_, v___x_4025_, v_heq_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4033_, lean_object* v_x1_4034_, lean_object* v_indName_4035_, lean_object* v_tail_4036_, lean_object* v_params_4037_, lean_object* v_is_4038_, lean_object* v___x_4039_, lean_object* v_head_4040_, lean_object* v_ctors_4041_, lean_object* v_numIndices_4042_, lean_object* v___x_4043_, lean_object* v___x_4044_, lean_object* v_val_4045_, lean_object* v_declName_4046_, lean_object* v_levelParams_4047_, lean_object* v_numParams_4048_, lean_object* v___x_4049_, lean_object* v___x_4050_, lean_object* v_x2_4051_, lean_object* v_x_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4058_ = lean_unsigned_to_nat(0u);
v___x_4059_ = lean_array_get_borrowed(v___x_4033_, v_x1_4034_, v___x_4058_);
v___x_4060_ = lean_array_get_borrowed(v___x_4033_, v_x2_4051_, v___x_4058_);
v___x_4061_ = l_mkCtorIdxName(v_indName_4035_);
lean_inc(v_tail_4036_);
v___x_4062_ = l_Lean_mkConst(v___x_4061_, v_tail_4036_);
lean_inc_ref(v_params_4037_);
v___x_4063_ = l_Array_append___redArg(v_params_4037_, v_is_4038_);
v___x_4064_ = lean_mk_empty_array_with_capacity(v___x_4039_);
lean_inc(v___x_4059_);
lean_inc_ref(v___x_4064_);
v___x_4065_ = lean_array_push(v___x_4064_, v___x_4059_);
lean_inc_ref(v___x_4063_);
v___x_4066_ = l_Array_append___redArg(v___x_4063_, v___x_4065_);
lean_inc_ref(v___x_4062_);
v___x_4067_ = l_Lean_mkAppN(v___x_4062_, v___x_4066_);
lean_dec_ref(v___x_4066_);
lean_inc(v___x_4060_);
lean_inc_ref(v___x_4064_);
v___x_4068_ = lean_array_push(v___x_4064_, v___x_4060_);
v___x_4069_ = l_Array_append___redArg(v___x_4063_, v___x_4068_);
v___x_4070_ = l_Lean_mkAppN(v___x_4062_, v___x_4069_);
lean_dec_ref(v___x_4069_);
v___x_4071_ = l_Lean_Meta_mkEq(v___x_4067_, v___x_4070_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___f_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref(v___x_4071_);
lean_inc(v___x_4060_);
lean_inc(v___x_4059_);
v___f_4073_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 27, 21);
lean_closure_set(v___f_4073_, 0, v___x_4059_);
lean_closure_set(v___f_4073_, 1, v___x_4060_);
lean_closure_set(v___f_4073_, 2, v_is_4038_);
lean_closure_set(v___f_4073_, 3, v_head_4040_);
lean_closure_set(v___f_4073_, 4, v_ctors_4041_);
lean_closure_set(v___f_4073_, 5, v_tail_4036_);
lean_closure_set(v___f_4073_, 6, v_params_4037_);
lean_closure_set(v___f_4073_, 7, v___x_4058_);
lean_closure_set(v___f_4073_, 8, v_numIndices_4042_);
lean_closure_set(v___f_4073_, 9, v___x_4039_);
lean_closure_set(v___f_4073_, 10, v___x_4043_);
lean_closure_set(v___f_4073_, 11, v___x_4044_);
lean_closure_set(v___f_4073_, 12, v___x_4065_);
lean_closure_set(v___f_4073_, 13, v___x_4068_);
lean_closure_set(v___f_4073_, 14, v_val_4045_);
lean_closure_set(v___f_4073_, 15, v___x_4064_);
lean_closure_set(v___f_4073_, 16, v_declName_4046_);
lean_closure_set(v___f_4073_, 17, v_levelParams_4047_);
lean_closure_set(v___f_4073_, 18, v_numParams_4048_);
lean_closure_set(v___f_4073_, 19, v___x_4049_);
lean_closure_set(v___f_4073_, 20, v___x_4050_);
v___x_4074_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4075_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4074_, v_a_4072_, v___f_4073_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
return v___x_4075_;
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec_ref(v___x_4068_);
lean_dec_ref(v___x_4065_);
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4049_);
lean_dec(v_numParams_4048_);
lean_dec(v_levelParams_4047_);
lean_dec(v_declName_4046_);
lean_dec_ref(v_val_4045_);
lean_dec(v___x_4044_);
lean_dec(v___x_4043_);
lean_dec(v_numIndices_4042_);
lean_dec(v_ctors_4041_);
lean_dec(v_head_4040_);
lean_dec(v___x_4039_);
lean_dec_ref(v_is_4038_);
lean_dec_ref(v_params_4037_);
lean_dec(v_tail_4036_);
v_a_4076_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4071_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4071_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4084_ = _args[0];
lean_object* v_x1_4085_ = _args[1];
lean_object* v_indName_4086_ = _args[2];
lean_object* v_tail_4087_ = _args[3];
lean_object* v_params_4088_ = _args[4];
lean_object* v_is_4089_ = _args[5];
lean_object* v___x_4090_ = _args[6];
lean_object* v_head_4091_ = _args[7];
lean_object* v_ctors_4092_ = _args[8];
lean_object* v_numIndices_4093_ = _args[9];
lean_object* v___x_4094_ = _args[10];
lean_object* v___x_4095_ = _args[11];
lean_object* v_val_4096_ = _args[12];
lean_object* v_declName_4097_ = _args[13];
lean_object* v_levelParams_4098_ = _args[14];
lean_object* v_numParams_4099_ = _args[15];
lean_object* v___x_4100_ = _args[16];
lean_object* v___x_4101_ = _args[17];
lean_object* v_x2_4102_ = _args[18];
lean_object* v_x_4103_ = _args[19];
lean_object* v___y_4104_ = _args[20];
lean_object* v___y_4105_ = _args[21];
lean_object* v___y_4106_ = _args[22];
lean_object* v___y_4107_ = _args[23];
lean_object* v___y_4108_ = _args[24];
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4084_, v_x1_4085_, v_indName_4086_, v_tail_4087_, v_params_4088_, v_is_4089_, v___x_4090_, v_head_4091_, v_ctors_4092_, v_numIndices_4093_, v___x_4094_, v___x_4095_, v_val_4096_, v_declName_4097_, v_levelParams_4098_, v_numParams_4099_, v___x_4100_, v___x_4101_, v_x2_4102_, v_x_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec_ref(v_x_4103_);
lean_dec_ref(v_x2_4102_);
lean_dec_ref(v_x1_4085_);
lean_dec_ref(v___x_4084_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4110_, lean_object* v_indName_4111_, lean_object* v_tail_4112_, lean_object* v_params_4113_, lean_object* v_is_4114_, lean_object* v___x_4115_, lean_object* v_head_4116_, lean_object* v_ctors_4117_, lean_object* v_numIndices_4118_, lean_object* v___x_4119_, lean_object* v___x_4120_, lean_object* v_val_4121_, lean_object* v_declName_4122_, lean_object* v_levelParams_4123_, lean_object* v_numParams_4124_, lean_object* v___x_4125_, lean_object* v___x_4126_, lean_object* v_t_4127_, lean_object* v___x_4128_, lean_object* v_x1_4129_, lean_object* v_x_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v___f_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; 
v___f_4136_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 25, 18);
lean_closure_set(v___f_4136_, 0, v___x_4110_);
lean_closure_set(v___f_4136_, 1, v_x1_4129_);
lean_closure_set(v___f_4136_, 2, v_indName_4111_);
lean_closure_set(v___f_4136_, 3, v_tail_4112_);
lean_closure_set(v___f_4136_, 4, v_params_4113_);
lean_closure_set(v___f_4136_, 5, v_is_4114_);
lean_closure_set(v___f_4136_, 6, v___x_4115_);
lean_closure_set(v___f_4136_, 7, v_head_4116_);
lean_closure_set(v___f_4136_, 8, v_ctors_4117_);
lean_closure_set(v___f_4136_, 9, v_numIndices_4118_);
lean_closure_set(v___f_4136_, 10, v___x_4119_);
lean_closure_set(v___f_4136_, 11, v___x_4120_);
lean_closure_set(v___f_4136_, 12, v_val_4121_);
lean_closure_set(v___f_4136_, 13, v_declName_4122_);
lean_closure_set(v___f_4136_, 14, v_levelParams_4123_);
lean_closure_set(v___f_4136_, 15, v_numParams_4124_);
lean_closure_set(v___f_4136_, 16, v___x_4125_);
lean_closure_set(v___f_4136_, 17, v___x_4126_);
v___x_4137_ = 0;
v___x_4138_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4127_, v___x_4128_, v___f_4136_, v___x_4137_, v___x_4137_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4139_ = _args[0];
lean_object* v_indName_4140_ = _args[1];
lean_object* v_tail_4141_ = _args[2];
lean_object* v_params_4142_ = _args[3];
lean_object* v_is_4143_ = _args[4];
lean_object* v___x_4144_ = _args[5];
lean_object* v_head_4145_ = _args[6];
lean_object* v_ctors_4146_ = _args[7];
lean_object* v_numIndices_4147_ = _args[8];
lean_object* v___x_4148_ = _args[9];
lean_object* v___x_4149_ = _args[10];
lean_object* v_val_4150_ = _args[11];
lean_object* v_declName_4151_ = _args[12];
lean_object* v_levelParams_4152_ = _args[13];
lean_object* v_numParams_4153_ = _args[14];
lean_object* v___x_4154_ = _args[15];
lean_object* v___x_4155_ = _args[16];
lean_object* v_t_4156_ = _args[17];
lean_object* v___x_4157_ = _args[18];
lean_object* v_x1_4158_ = _args[19];
lean_object* v_x_4159_ = _args[20];
lean_object* v___y_4160_ = _args[21];
lean_object* v___y_4161_ = _args[22];
lean_object* v___y_4162_ = _args[23];
lean_object* v___y_4163_ = _args[24];
lean_object* v___y_4164_ = _args[25];
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4139_, v_indName_4140_, v_tail_4141_, v_params_4142_, v_is_4143_, v___x_4144_, v_head_4145_, v_ctors_4146_, v_numIndices_4147_, v___x_4148_, v___x_4149_, v_val_4150_, v_declName_4151_, v_levelParams_4152_, v_numParams_4153_, v___x_4154_, v___x_4155_, v_t_4156_, v___x_4157_, v_x1_4158_, v_x_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec_ref(v_x_4159_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4166_, lean_object* v_indName_4167_, lean_object* v_tail_4168_, lean_object* v_params_4169_, lean_object* v_head_4170_, lean_object* v_ctors_4171_, lean_object* v_numIndices_4172_, lean_object* v___x_4173_, lean_object* v___x_4174_, lean_object* v_val_4175_, lean_object* v_declName_4176_, lean_object* v_levelParams_4177_, lean_object* v_numParams_4178_, lean_object* v___x_4179_, lean_object* v___x_4180_, lean_object* v_is_4181_, lean_object* v_t_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___f_4190_; uint8_t v___x_4191_; lean_object* v___x_4192_; 
v___x_4188_ = lean_unsigned_to_nat(1u);
v___x_4189_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4182_);
v___f_4190_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 26, 19);
lean_closure_set(v___f_4190_, 0, v___x_4166_);
lean_closure_set(v___f_4190_, 1, v_indName_4167_);
lean_closure_set(v___f_4190_, 2, v_tail_4168_);
lean_closure_set(v___f_4190_, 3, v_params_4169_);
lean_closure_set(v___f_4190_, 4, v_is_4181_);
lean_closure_set(v___f_4190_, 5, v___x_4188_);
lean_closure_set(v___f_4190_, 6, v_head_4170_);
lean_closure_set(v___f_4190_, 7, v_ctors_4171_);
lean_closure_set(v___f_4190_, 8, v_numIndices_4172_);
lean_closure_set(v___f_4190_, 9, v___x_4173_);
lean_closure_set(v___f_4190_, 10, v___x_4174_);
lean_closure_set(v___f_4190_, 11, v_val_4175_);
lean_closure_set(v___f_4190_, 12, v_declName_4176_);
lean_closure_set(v___f_4190_, 13, v_levelParams_4177_);
lean_closure_set(v___f_4190_, 14, v_numParams_4178_);
lean_closure_set(v___f_4190_, 15, v___x_4179_);
lean_closure_set(v___f_4190_, 16, v___x_4180_);
lean_closure_set(v___f_4190_, 17, v_t_4182_);
lean_closure_set(v___f_4190_, 18, v___x_4189_);
v___x_4191_ = 0;
v___x_4192_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4182_, v___x_4189_, v___f_4190_, v___x_4191_, v___x_4191_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4193_ = _args[0];
lean_object* v_indName_4194_ = _args[1];
lean_object* v_tail_4195_ = _args[2];
lean_object* v_params_4196_ = _args[3];
lean_object* v_head_4197_ = _args[4];
lean_object* v_ctors_4198_ = _args[5];
lean_object* v_numIndices_4199_ = _args[6];
lean_object* v___x_4200_ = _args[7];
lean_object* v___x_4201_ = _args[8];
lean_object* v_val_4202_ = _args[9];
lean_object* v_declName_4203_ = _args[10];
lean_object* v_levelParams_4204_ = _args[11];
lean_object* v_numParams_4205_ = _args[12];
lean_object* v___x_4206_ = _args[13];
lean_object* v___x_4207_ = _args[14];
lean_object* v_is_4208_ = _args[15];
lean_object* v_t_4209_ = _args[16];
lean_object* v___y_4210_ = _args[17];
lean_object* v___y_4211_ = _args[18];
lean_object* v___y_4212_ = _args[19];
lean_object* v___y_4213_ = _args[20];
lean_object* v___y_4214_ = _args[21];
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4193_, v_indName_4194_, v_tail_4195_, v_params_4196_, v_head_4197_, v_ctors_4198_, v_numIndices_4199_, v___x_4200_, v___x_4201_, v_val_4202_, v_declName_4203_, v_levelParams_4204_, v_numParams_4205_, v___x_4206_, v___x_4207_, v_is_4208_, v_t_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4216_, lean_object* v_indName_4217_, lean_object* v_tail_4218_, lean_object* v_head_4219_, lean_object* v_ctors_4220_, lean_object* v_numIndices_4221_, lean_object* v___x_4222_, lean_object* v___x_4223_, lean_object* v_val_4224_, lean_object* v_declName_4225_, lean_object* v_levelParams_4226_, lean_object* v_numParams_4227_, lean_object* v___x_4228_, lean_object* v_params_4229_, lean_object* v_t_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v___x_4236_; lean_object* v___f_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; lean_object* v___x_4240_; 
v___x_4236_ = l_Lean_Expr_bindingBody_x21(v_t_4230_);
lean_inc_ref(v___x_4236_);
lean_inc(v_numIndices_4221_);
v___f_4237_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 22, 15);
lean_closure_set(v___f_4237_, 0, v___x_4216_);
lean_closure_set(v___f_4237_, 1, v_indName_4217_);
lean_closure_set(v___f_4237_, 2, v_tail_4218_);
lean_closure_set(v___f_4237_, 3, v_params_4229_);
lean_closure_set(v___f_4237_, 4, v_head_4219_);
lean_closure_set(v___f_4237_, 5, v_ctors_4220_);
lean_closure_set(v___f_4237_, 6, v_numIndices_4221_);
lean_closure_set(v___f_4237_, 7, v___x_4222_);
lean_closure_set(v___f_4237_, 8, v___x_4223_);
lean_closure_set(v___f_4237_, 9, v_val_4224_);
lean_closure_set(v___f_4237_, 10, v_declName_4225_);
lean_closure_set(v___f_4237_, 11, v_levelParams_4226_);
lean_closure_set(v___f_4237_, 12, v_numParams_4227_);
lean_closure_set(v___f_4237_, 13, v___x_4236_);
lean_closure_set(v___f_4237_, 14, v___x_4228_);
v___x_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_numIndices_4221_);
v___x_4239_ = 0;
v___x_4240_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4236_, v___x_4238_, v___f_4237_, v___x_4239_, v___x_4239_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4241_ = _args[0];
lean_object* v_indName_4242_ = _args[1];
lean_object* v_tail_4243_ = _args[2];
lean_object* v_head_4244_ = _args[3];
lean_object* v_ctors_4245_ = _args[4];
lean_object* v_numIndices_4246_ = _args[5];
lean_object* v___x_4247_ = _args[6];
lean_object* v___x_4248_ = _args[7];
lean_object* v_val_4249_ = _args[8];
lean_object* v_declName_4250_ = _args[9];
lean_object* v_levelParams_4251_ = _args[10];
lean_object* v_numParams_4252_ = _args[11];
lean_object* v___x_4253_ = _args[12];
lean_object* v_params_4254_ = _args[13];
lean_object* v_t_4255_ = _args[14];
lean_object* v___y_4256_ = _args[15];
lean_object* v___y_4257_ = _args[16];
lean_object* v___y_4258_ = _args[17];
lean_object* v___y_4259_ = _args[18];
lean_object* v___y_4260_ = _args[19];
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4241_, v_indName_4242_, v_tail_4243_, v_head_4244_, v_ctors_4245_, v_numIndices_4246_, v___x_4247_, v___x_4248_, v_val_4249_, v_declName_4250_, v_levelParams_4251_, v_numParams_4252_, v___x_4253_, v_params_4254_, v_t_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec_ref(v_t_4255_);
return v_res_4261_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4266_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4267_ = lean_unsigned_to_nat(58u);
v___x_4268_ = lean_unsigned_to_nat(142u);
v___x_4269_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4270_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4271_ = l_mkPanicMessageWithDecl(v___x_4270_, v___x_4269_, v___x_4268_, v___x_4267_, v___x_4266_);
return v___x_4271_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4272_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4273_ = lean_unsigned_to_nat(60u);
v___x_4274_ = lean_unsigned_to_nat(136u);
v___x_4275_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4276_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4277_ = l_mkPanicMessageWithDecl(v___x_4276_, v___x_4275_, v___x_4274_, v___x_4273_, v___x_4272_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4278_, lean_object* v_indName_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v___x_4285_; 
lean_inc(v_indName_4279_);
v___x_4285_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref(v___x_4285_);
if (lean_obj_tag(v_a_4286_) == 5)
{
lean_object* v_val_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v_val_4287_ = lean_ctor_get(v_a_4286_, 0);
lean_inc_ref(v_val_4287_);
lean_dec_ref(v_a_4286_);
v___x_4288_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4278_);
v___x_4289_ = l_Lean_Name_append(v_declName_4278_, v___x_4288_);
lean_inc(v_indName_4279_);
lean_inc(v___x_4289_);
v___x_4290_ = l_Lean_mkCasesOnSameCtorHet(v___x_4289_, v_indName_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4324_; 
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4324_ == 0)
{
lean_object* v_unused_4325_; 
v_unused_4325_ = lean_ctor_get(v___x_4290_, 0);
lean_dec(v_unused_4325_);
v___x_4292_ = v___x_4290_;
v_isShared_4293_ = v_isSharedCheck_4324_;
goto v_resetjp_4291_;
}
else
{
lean_dec(v___x_4290_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4324_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; 
lean_inc(v_indName_4279_);
v___x_4294_ = l_Lean_mkCasesOnName(v_indName_4279_);
v___x_4295_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4294_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v_levelParams_4297_; lean_object* v_type_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref(v___x_4295_);
v_levelParams_4297_ = lean_ctor_get(v_a_4296_, 1);
lean_inc(v_levelParams_4297_);
v_type_4298_ = lean_ctor_get(v_a_4296_, 2);
lean_inc_ref(v_type_4298_);
lean_dec(v_a_4296_);
v___x_4299_ = lean_box(0);
lean_inc(v_levelParams_4297_);
v___x_4300_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4297_, v___x_4299_);
if (lean_obj_tag(v___x_4300_) == 1)
{
lean_object* v_head_4301_; lean_object* v_tail_4302_; lean_object* v_numParams_4303_; lean_object* v_numIndices_4304_; lean_object* v_ctors_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___f_4308_; lean_object* v___x_4310_; 
v_head_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_head_4301_);
v_tail_4302_ = lean_ctor_get(v___x_4300_, 1);
lean_inc(v_tail_4302_);
v_numParams_4303_ = lean_ctor_get(v_val_4287_, 1);
lean_inc(v_numParams_4303_);
v_numIndices_4304_ = lean_ctor_get(v_val_4287_, 2);
lean_inc(v_numIndices_4304_);
v_ctors_4305_ = lean_ctor_get(v_val_4287_, 4);
lean_inc(v_ctors_4305_);
v___x_4306_ = l_Lean_instInhabitedExpr;
v___x_4307_ = lean_box(0);
lean_inc(v_numParams_4303_);
v___f_4308_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 20, 13);
lean_closure_set(v___f_4308_, 0, v___x_4306_);
lean_closure_set(v___f_4308_, 1, v_indName_4279_);
lean_closure_set(v___f_4308_, 2, v_tail_4302_);
lean_closure_set(v___f_4308_, 3, v_head_4301_);
lean_closure_set(v___f_4308_, 4, v_ctors_4305_);
lean_closure_set(v___f_4308_, 5, v_numIndices_4304_);
lean_closure_set(v___f_4308_, 6, v___x_4289_);
lean_closure_set(v___f_4308_, 7, v___x_4300_);
lean_closure_set(v___f_4308_, 8, v_val_4287_);
lean_closure_set(v___f_4308_, 9, v_declName_4278_);
lean_closure_set(v___f_4308_, 10, v_levelParams_4297_);
lean_closure_set(v___f_4308_, 11, v_numParams_4303_);
lean_closure_set(v___f_4308_, 12, v___x_4307_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set_tag(v___x_4292_, 1);
lean_ctor_set(v___x_4292_, 0, v_numParams_4303_);
v___x_4310_ = v___x_4292_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_numParams_4303_);
v___x_4310_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
uint8_t v___x_4311_; lean_object* v___x_4312_; 
v___x_4311_ = 0;
v___x_4312_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4298_, v___x_4310_, v___f_4308_, v___x_4311_, v___x_4311_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
return v___x_4312_;
}
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
lean_dec(v___x_4300_);
lean_dec_ref(v_type_4298_);
lean_dec(v_levelParams_4297_);
lean_del_object(v___x_4292_);
lean_dec(v___x_4289_);
lean_dec_ref(v_val_4287_);
lean_dec(v_indName_4279_);
lean_dec(v_declName_4278_);
v___x_4314_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4315_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4314_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
return v___x_4315_;
}
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_del_object(v___x_4292_);
lean_dec(v___x_4289_);
lean_dec_ref(v_val_4287_);
lean_dec(v_indName_4279_);
lean_dec(v_declName_4278_);
v_a_4316_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4295_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4295_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
else
{
lean_dec(v___x_4289_);
lean_dec_ref(v_val_4287_);
lean_dec(v_indName_4279_);
lean_dec(v_declName_4278_);
return v___x_4290_;
}
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
lean_dec(v_a_4286_);
lean_dec(v_indName_4279_);
lean_dec(v_declName_4278_);
v___x_4326_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4327_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4326_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
return v___x_4327_;
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_indName_4279_);
lean_dec(v_declName_4278_);
v_a_4328_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4285_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4285_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4336_, lean_object* v_indName_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_mkCasesOnSameCtor(v_declName_4336_, v_indName_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
lean_dec(v_a_4341_);
lean_dec_ref(v_a_4340_);
lean_dec(v_a_4339_);
lean_dec_ref(v_a_4338_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4344_, lean_object* v_params_4345_, lean_object* v_motive_4346_, lean_object* v_as_4347_, lean_object* v_i_4348_, lean_object* v_j_4349_, lean_object* v_inv_4350_, lean_object* v_bs_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4344_, v_params_4345_, v_motive_4346_, v_as_4347_, v_i_4348_, v_j_4349_, v_bs_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4358_, lean_object* v_params_4359_, lean_object* v_motive_4360_, lean_object* v_as_4361_, lean_object* v_i_4362_, lean_object* v_j_4363_, lean_object* v_inv_4364_, lean_object* v_bs_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4358_, v_params_4359_, v_motive_4360_, v_as_4361_, v_i_4362_, v_j_4363_, v_inv_4364_, v_bs_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec_ref(v_as_4361_);
lean_dec_ref(v_params_4359_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4372_, lean_object* v_params_4373_, lean_object* v_a_4374_, lean_object* v_snd_4375_, lean_object* v_alts_4376_, lean_object* v_as_4377_, lean_object* v_i_4378_, lean_object* v_j_4379_, lean_object* v_inv_4380_, lean_object* v_bs_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4372_, v_params_4373_, v_a_4374_, v_snd_4375_, v_alts_4376_, v_as_4377_, v_i_4378_, v_j_4379_, v_bs_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4388_, lean_object* v_params_4389_, lean_object* v_a_4390_, lean_object* v_snd_4391_, lean_object* v_alts_4392_, lean_object* v_as_4393_, lean_object* v_i_4394_, lean_object* v_j_4395_, lean_object* v_inv_4396_, lean_object* v_bs_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4388_, v_params_4389_, v_a_4390_, v_snd_4391_, v_alts_4392_, v_as_4393_, v_i_4394_, v_j_4395_, v_inv_4396_, v_bs_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
lean_dec_ref(v_as_4393_);
lean_dec_ref(v_params_4389_);
return v_res_4403_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* initialize_Lean_Elab_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
}
#ifdef __cplusplus
}
#endif
