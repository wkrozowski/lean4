// Lean compiler output
// Module: Lean.Meta.WrapInstance
// Imports: public import Lean.Meta.Closure public import Lean.Meta.SynthInstance public import Lean.Meta.CtorRecognizer public import Lean.Meta.AppBuilder import Lean.Structure
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
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureParentInfo(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getFieldInfo_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inferInstanceAs"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "wrap"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "wrap instance bodies in `inferInstanceAs` and the default `deriving` handler"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reuseSubInstances"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(10, 196, 243, 125, 230, 240, 101, 207)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "when recursing into sub-instances, reuse existing instances for the target type instead of re-wrapping them, which can be important to avoid non-defeq instance diamonds"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 247, 150, 241, 101, 127, 32, 183)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(154, 83, 182, 188, 30, 204, 110, 119)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "wrap non-reducible instances in auxiliary definitions to fix their types"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 217, 132, 111, 195, 190, 14, 255)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 208, 243, 158, 154, 215, 49, 58)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "wrap data fields in auxiliary definitions to fix their types"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(59, 4, 237, 30, 122, 190, 35, 247)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_data;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "wrapInstance"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 191, 244, 235, 250, 100, 130, 195)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "WrapInstance"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 173, 45, 246, 47, 55, 243, 119)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(185, 135, 228, 210, 15, 68, 162, 204)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 3, 219, 249, 198, 148, 9, 129)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 244, 76, 43, 236, 107, 113, 110)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 218, 192, 96, 244, 90, 226, 106)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 37, 133, 70, 202, 123, 99, 119)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(201, 48, 88, 11, 50, 139, 104, 61)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(89, 200, 58, 34, 117, 240, 39, 228)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 33, 3, 130, 142, 149, 29, 62)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "no such field "};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2_value;
static const lean_ctor_object l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1_value;
static const lean_ctor_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "could not reduce type `"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5;
static const lean_string_object l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6 = (const lean_object*)&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6_value;
static lean_once_cell_t l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7;
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "parent type depends on instance fields"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "self"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(120, 226, 111, 209, 39, 160, 197, 219)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_wrapInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "error when attempting to reuse existing instance for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "using projection of existing instance `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "did not find existing instance for `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_wrapInstance___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "did not reduce to constructor application, returning/wrapping as is: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found inherited field `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "` from parent `"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__5_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "using existing instance "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof field "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " does not have expected type "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " but "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = ", wrapping in auxiliary theorem: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "wrapInstance: incorrect number of arguments for constructor application `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "wrapInstance: `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__4_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not unify with the conclusion of `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__6_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_wrapInstance___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "class is "};
static const lean_object* l_Lean_Meta_wrapInstance___closed__2 = (const lean_object*)&l_Lean_Meta_wrapInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_));
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_));
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_));
v___x_85_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v___x_82_, v___x_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_));
v___x_109_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_));
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_));
v___x_111_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4____boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_();
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_));
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_));
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_));
v___x_137_ = l_Lean_Option_register___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4__spec__0(v___x_134_, v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4____boxed(lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_();
return v_res_139_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_unsigned_to_nat(3246864463u);
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_186_ = l_Lean_Name_num___override(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_190_ = l_Lean_Name_str___override(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_193_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_194_ = l_Lean_Name_str___override(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(2u);
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_197_ = l_Lean_Name_num___override(v___x_196_, v___x_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_200_ = 0;
v___x_201_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_202_ = l_Lean_registerTraceClass(v___x_199_, v___x_200_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2____boxed(lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; lean_object* v_env_212_; lean_object* v___x_213_; lean_object* v_mctx_214_; lean_object* v_lctx_215_; lean_object* v_options_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_211_ = lean_st_ref_get(v___y_209_);
v_env_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_env_212_);
lean_dec(v___x_211_);
v___x_213_ = lean_st_ref_get(v___y_207_);
v_mctx_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc_ref(v_mctx_214_);
lean_dec(v___x_213_);
v_lctx_215_ = lean_ctor_get(v___y_206_, 2);
v_options_216_ = lean_ctor_get(v___y_208_, 2);
lean_inc_ref(v_options_216_);
lean_inc_ref(v_lctx_215_);
v___x_217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_217_, 0, v_env_212_);
lean_ctor_set(v___x_217_, 1, v_mctx_214_);
lean_ctor_set(v___x_217_, 2, v_lctx_215_);
lean_ctor_set(v___x_217_, 3, v_options_216_);
v___x_218_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_msgData_205_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1___boxed(lean_object* v_msgData_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msgData_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_ref_233_; lean_object* v___x_234_; lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_ref_233_ = lean_ctor_get(v___y_230_, 5);
v___x_234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
lean_inc(v_ref_233_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_ref_233_);
lean_ctor_set(v___x_239_, 1, v_a_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 1);
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg___boxed(lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__0));
v___x_256_ = l_Lean_stringToMessageData(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__2));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(lean_object* v_structName_260_, lean_object* v_field_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_env_268_; lean_object* v___x_269_; lean_object* v___x_270_; size_t v_sz_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_st_ref_get(v_a_265_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref_n(v_env_268_, 3);
lean_dec(v___x_267_);
lean_inc(v_structName_260_);
v___x_269_ = l_Lean_getStructureParentInfo(v_env_268_, v_structName_260_);
v___x_270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0));
v_sz_271_ = lean_array_size(v___x_269_);
v___x_272_ = ((size_t)0ULL);
lean_inc(v_field_261_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(v_env_268_, v_field_261_, v___x_269_, v_sz_271_, v___x_272_, v___x_270_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
lean_dec_ref(v___x_269_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_304_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_304_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_304_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_304_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_fst_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_302_; 
v_fst_278_ = lean_ctor_get(v_a_274_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_a_274_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v_a_274_, 1);
lean_dec(v_unused_303_);
v___x_280_ = v_a_274_;
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_fst_278_);
lean_dec(v_a_274_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
if (lean_obj_tag(v_fst_278_) == 0)
{
lean_object* v___x_282_; 
lean_inc(v_field_261_);
lean_inc(v_structName_260_);
v___x_282_ = l_Lean_getFieldInfo_x3f(v_env_268_, v_structName_260_, v_field_261_);
if (lean_obj_tag(v___x_282_) == 1)
{
lean_object* v_val_283_; lean_object* v___x_285_; 
lean_dec(v_field_261_);
v_val_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_val_283_);
lean_dec_ref(v___x_282_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v_val_283_);
lean_ctor_set(v___x_280_, 0, v_structName_260_);
v___x_285_ = v___x_280_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_structName_260_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_val_283_);
v___x_285_ = v_reuseFailAlloc_289_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_285_);
v___x_287_ = v___x_276_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v___x_282_);
lean_del_object(v___x_280_);
lean_del_object(v___x_276_);
v___x_290_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__1);
v___x_291_ = l_Lean_MessageData_ofName(v_field_261_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___closed__3);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_MessageData_ofName(v_structName_260_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_296_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
return v___x_297_;
}
}
else
{
lean_object* v_val_298_; lean_object* v___x_300_; 
lean_del_object(v___x_280_);
lean_dec_ref(v_env_268_);
lean_dec(v_field_261_);
lean_dec(v_structName_260_);
v_val_298_ = lean_ctor_get(v_fst_278_, 0);
lean_inc(v_val_298_);
lean_dec_ref(v_fst_278_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v_val_298_);
v___x_300_ = v___x_276_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_val_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec_ref(v_env_268_);
lean_dec(v_field_261_);
lean_dec(v_structName_260_);
v_a_305_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_273_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_273_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(lean_object* v___x_313_, lean_object* v_field_314_, lean_object* v_as_315_, size_t v_sz_316_, size_t v_i_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_lt(v_i_317_, v_sz_316_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec(v_field_314_);
lean_dec_ref(v___x_313_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_b_318_);
return v___x_325_;
}
else
{
lean_object* v_a_326_; lean_object* v_structName_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_b_318_);
v_a_326_ = lean_array_uget_borrowed(v_as_315_, v_i_317_);
v_structName_327_ = lean_ctor_get(v_a_326_, 0);
v___x_328_ = lean_box(0);
lean_inc(v_structName_327_);
lean_inc_ref(v___x_313_);
v___x_329_ = l_Lean_findField_x3f(v___x_313_, v_structName_327_, v_field_314_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v___x_330_; size_t v___x_331_; size_t v___x_332_; 
v___x_330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___closed__0));
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_317_, v___x_331_);
v_i_317_ = v___x_332_;
v_b_318_ = v___x_330_;
goto _start;
}
else
{
lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v___x_313_);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_329_, 0);
lean_dec(v_unused_359_);
v___x_335_ = v___x_329_;
v_isShared_336_ = v_isSharedCheck_358_;
goto v_resetjp_334_;
}
else
{
lean_dec(v___x_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_358_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; 
lean_inc(v_structName_327_);
v___x_337_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_structName_327_, v_field_314_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_349_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_349_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v_a_338_);
v___x_343_ = v___x_335_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_348_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_328_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_del_object(v___x_335_);
v_a_350_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_337_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_337_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0___boxed(lean_object* v___x_360_, lean_object* v_field_361_, lean_object* v_as_362_, lean_object* v_sz_363_, lean_object* v_i_364_, lean_object* v_b_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_363_);
lean_dec(v_sz_363_);
v_i_boxed_372_ = lean_unbox_usize(v_i_364_);
lean_dec(v_i_364_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__0(v___x_360_, v_field_361_, v_as_362_, v_sz_boxed_371_, v_i_boxed_372_, v_b_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec_ref(v_as_362_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin___boxed(lean_object* v_structName_374_, lean_object* v_field_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_structName_374_, v_field_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1(lean_object* v_00_u03b1_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___boxed(lean_object* v_00_u03b1_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1(v_00_u03b1_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_398_; double v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_float_of_nat(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(lean_object* v_cls_405_, lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_ref_412_; lean_object* v___x_413_; lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_458_; 
v_ref_412_ = lean_ctor_get(v___y_409_, 5);
v___x_413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_458_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_458_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_458_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v_traceState_419_; lean_object* v_env_420_; lean_object* v_nextMacroScope_421_; lean_object* v_ngen_422_; lean_object* v_auxDeclNGen_423_; lean_object* v_cache_424_; lean_object* v_messages_425_; lean_object* v_infoState_426_; lean_object* v_snapshotTasks_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_457_; 
v___x_418_ = lean_st_ref_take(v___y_410_);
v_traceState_419_ = lean_ctor_get(v___x_418_, 4);
v_env_420_ = lean_ctor_get(v___x_418_, 0);
v_nextMacroScope_421_ = lean_ctor_get(v___x_418_, 1);
v_ngen_422_ = lean_ctor_get(v___x_418_, 2);
v_auxDeclNGen_423_ = lean_ctor_get(v___x_418_, 3);
v_cache_424_ = lean_ctor_get(v___x_418_, 5);
v_messages_425_ = lean_ctor_get(v___x_418_, 6);
v_infoState_426_ = lean_ctor_get(v___x_418_, 7);
v_snapshotTasks_427_ = lean_ctor_get(v___x_418_, 8);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_457_ == 0)
{
v___x_429_ = v___x_418_;
v_isShared_430_ = v_isSharedCheck_457_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_snapshotTasks_427_);
lean_inc(v_infoState_426_);
lean_inc(v_messages_425_);
lean_inc(v_cache_424_);
lean_inc(v_traceState_419_);
lean_inc(v_auxDeclNGen_423_);
lean_inc(v_ngen_422_);
lean_inc(v_nextMacroScope_421_);
lean_inc(v_env_420_);
lean_dec(v___x_418_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_457_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint64_t v_tid_431_; lean_object* v_traces_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_456_; 
v_tid_431_ = lean_ctor_get_uint64(v_traceState_419_, sizeof(void*)*1);
v_traces_432_ = lean_ctor_get(v_traceState_419_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_traceState_419_);
if (v_isSharedCheck_456_ == 0)
{
v___x_434_ = v_traceState_419_;
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_traces_432_);
lean_dec(v_traceState_419_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_456_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; double v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_436_ = lean_box(0);
v___x_437_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
v___x_438_ = 0;
v___x_439_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_440_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_440_, 0, v_cls_405_);
lean_ctor_set(v___x_440_, 1, v___x_436_);
lean_ctor_set(v___x_440_, 2, v___x_439_);
lean_ctor_set_float(v___x_440_, sizeof(void*)*3, v___x_437_);
lean_ctor_set_float(v___x_440_, sizeof(void*)*3 + 8, v___x_437_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*3 + 16, v___x_438_);
v___x_441_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2));
v___x_442_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v_a_414_);
lean_ctor_set(v___x_442_, 2, v___x_441_);
lean_inc(v_ref_412_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_ref_412_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_Lean_PersistentArray_push___redArg(v_traces_432_, v___x_443_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_444_);
v___x_446_ = v___x_434_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_444_);
lean_ctor_set_uint64(v_reuseFailAlloc_455_, sizeof(void*)*1, v_tid_431_);
v___x_446_ = v_reuseFailAlloc_455_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 4, v___x_446_);
v___x_448_ = v___x_429_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_env_420_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_nextMacroScope_421_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_ngen_422_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_auxDeclNGen_423_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_cache_424_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_messages_425_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_infoState_426_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_snapshotTasks_427_);
v___x_448_ = v_reuseFailAlloc_454_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = lean_st_ref_set(v___y_410_, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__3));
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_450_);
v___x_452_ = v___x_416_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___boxed(lean_object* v_cls_459_, lean_object* v_msg_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v_cls_459_, v_msg_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_466_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0(void){
_start:
{
lean_object* v___x_467_; lean_object* v_dummy_468_; 
v___x_467_ = lean_box(0);
v_dummy_468_ = l_Lean_Expr_sort___override(v___x_467_);
return v_dummy_468_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_473_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
v___x_474_ = l_Lean_Name_append(v___x_473_, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__4));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__6));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_x_481_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v_head_493_; lean_object* v_tail_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_552_; 
v_head_493_ = lean_ctor_get(v_x_482_, 0);
v_tail_494_ = lean_ctor_get(v_x_482_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_552_ == 0)
{
v___x_496_ = v_x_482_;
v_isShared_497_ = v_isSharedCheck_552_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_tail_494_);
lean_inc(v_head_493_);
lean_dec(v_x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_552_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; 
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
lean_inc_ref(v_x_481_);
v___x_498_ = lean_infer_type(v_x_481_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
v___x_500_ = lean_whnf(v_a_499_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = l_Lean_Expr_getAppFn(v_a_501_);
if (lean_obj_tag(v___x_502_) == 4)
{
lean_object* v_us_503_; lean_object* v_dummy_504_; lean_object* v_nargs_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_del_object(v___x_496_);
v_us_503_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_us_503_);
lean_dec_ref(v___x_502_);
v_dummy_504_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_505_ = l_Lean_Expr_getAppNumArgs(v_a_501_);
lean_inc(v_nargs_505_);
v___x_506_ = lean_mk_array(v_nargs_505_, v_dummy_504_);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_sub(v_nargs_505_, v___x_507_);
lean_dec(v_nargs_505_);
v___x_509_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_501_, v___x_506_, v___x_508_);
v___x_510_ = l_Lean_Expr_const___override(v_head_493_, v_us_503_);
v___x_511_ = l_Lean_mkAppN(v___x_510_, v___x_509_);
lean_dec_ref(v___x_509_);
v___x_512_ = l_Lean_Expr_app___override(v___x_511_, v_x_481_);
v_x_481_ = v___x_512_;
v_x_482_ = v_tail_494_;
goto _start;
}
else
{
lean_object* v_options_514_; uint8_t v_hasTrace_515_; 
lean_dec_ref(v___x_502_);
lean_dec(v_tail_494_);
lean_dec(v_head_493_);
lean_dec_ref(v_x_481_);
v_options_514_ = lean_ctor_get(v___y_485_, 2);
v_hasTrace_515_ = lean_ctor_get_uint8(v_options_514_, sizeof(void*)*1);
if (v_hasTrace_515_ == 0)
{
lean_dec(v_a_501_);
lean_del_object(v___x_496_);
goto v___jp_488_;
}
else
{
lean_object* v_inheritedTraceOptions_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_inheritedTraceOptions_516_ = lean_ctor_get(v___y_485_, 13);
v___x_517_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_518_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_519_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_516_, v_options_514_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v_a_501_);
lean_del_object(v___x_496_);
goto v___jp_488_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__5);
v___x_521_ = l_Lean_MessageData_ofExpr(v_a_501_);
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 7);
lean_ctor_set(v___x_496_, 1, v___x_521_);
lean_ctor_set(v___x_496_, 0, v___x_520_);
v___x_523_ = v___x_496_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_535_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v___x_517_, v___x_525_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_dec_ref(v___x_526_);
goto v___jp_488_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
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
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_del_object(v___x_496_);
lean_dec(v_tail_494_);
lean_dec(v_head_493_);
lean_dec_ref(v_x_481_);
v_a_536_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_500_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_500_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_del_object(v___x_496_);
lean_dec(v_tail_494_);
lean_dec(v_head_493_);
lean_dec_ref(v_x_481_);
v_a_544_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_498_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_498_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
v___jp_488_:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___boxed(lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(v_x_553_, v_x_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_560_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__0));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0(lean_object* v_val_564_, lean_object* v_self_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_574_; 
lean_inc_ref(v_self_565_);
v___x_574_ = l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1(v_self_565_, v_val_564_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
if (lean_obj_tag(v_a_575_) == 0)
{
lean_dec_ref(v_self_565_);
return v___x_574_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___x_574_);
v_val_576_ = lean_ctor_get(v_a_575_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_575_);
if (v_isSharedCheck_630_ == 0)
{
v___x_578_ = v_a_575_;
v_isShared_579_ = v_isSharedCheck_630_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v_a_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_630_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; 
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
v___x_580_ = lean_infer_type(v_val_576_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_580_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
v___x_582_ = lean_whnf(v_a_581_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_613_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_613_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_613_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_613_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = l_Lean_Expr_fvarId_x21(v_self_565_);
lean_dec_ref(v_self_565_);
v___x_588_ = l_Lean_Expr_containsFVar(v_a_583_, v___x_587_);
lean_dec(v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_590_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_a_583_);
v___x_590_ = v___x_578_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_583_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_590_);
v___x_592_ = v___x_585_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_object* v_options_595_; uint8_t v_hasTrace_596_; 
lean_del_object(v___x_585_);
lean_del_object(v___x_578_);
v_options_595_ = lean_ctor_get(v___y_568_, 2);
v_hasTrace_596_ = lean_ctor_get_uint8(v_options_595_, sizeof(void*)*1);
if (v_hasTrace_596_ == 0)
{
lean_dec(v_a_583_);
goto v___jp_571_;
}
else
{
lean_object* v_inheritedTraceOptions_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_inheritedTraceOptions_597_ = lean_ctor_get(v___y_568_, 13);
v___x_598_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_599_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_597_, v_options_595_, v___x_599_);
if (v___x_600_ == 0)
{
lean_dec(v_a_583_);
goto v___jp_571_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1_once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___closed__1);
v___x_602_ = l_Lean_indentExpr(v_a_583_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0(v___x_598_, v___x_603_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_dec_ref(v___x_604_);
goto v___jp_571_;
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
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
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_del_object(v___x_578_);
lean_dec_ref(v_self_565_);
v_a_614_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_582_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_582_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_del_object(v___x_578_);
lean_dec_ref(v_self_565_);
v_a_622_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_580_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_580_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_self_565_);
return v___x_574_;
}
v___jp_571_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___boxed(lean_object* v_val_631_, lean_object* v_self_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0(v_val_631_, v_self_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0(lean_object* v_k_639_, lean_object* v_b_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; 
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
v___x_646_ = lean_apply_6(v_k_639_, v_b_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_k_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0(v_k_647_, v_b_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(lean_object* v_name_655_, uint8_t v_bi_656_, lean_object* v_type_657_, lean_object* v_k_658_, uint8_t v_kind_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___f_665_; lean_object* v___x_666_; 
v___f_665_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_665_, 0, v_k_658_);
v___x_666_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_655_, v_bi_656_, v_type_657_, v___f_665_, v_kind_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_666_) == 0)
{
return v___x_666_;
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_name_675_, lean_object* v_bi_676_, lean_object* v_type_677_, lean_object* v_k_678_, lean_object* v_kind_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v_bi_boxed_685_; uint8_t v_kind_boxed_686_; lean_object* v_res_687_; 
v_bi_boxed_685_ = lean_unbox(v_bi_676_);
v_kind_boxed_686_ = lean_unbox(v_kind_679_);
v_res_687_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_675_, v_bi_boxed_685_, v_type_677_, v_k_678_, v_kind_boxed_686_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(lean_object* v_name_688_, lean_object* v_type_689_, lean_object* v_k_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; 
v___x_696_ = 0;
v___x_697_ = 0;
v___x_698_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_688_, v___x_696_, v_type_689_, v_k_690_, v___x_697_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg___boxed(lean_object* v_name_699_, lean_object* v_type_700_, lean_object* v_k_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v_name_699_, v_type_700_, v_k_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(lean_object* v_structName_711_, lean_object* v_parentStructName_712_, lean_object* v_structType_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; lean_object* v_env_720_; lean_object* v___x_721_; 
v___x_719_ = lean_st_ref_get(v_a_717_);
v_env_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_env_720_);
lean_dec(v___x_719_);
v___x_721_ = l_Lean_getPathToBaseStructure_x3f(v_env_720_, v_parentStructName_712_, v_structName_711_);
if (lean_obj_tag(v___x_721_) == 1)
{
lean_object* v_val_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_val_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_722_);
lean_dec_ref(v___x_721_);
v___f_723_ = lean_alloc_closure((void*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___lam__0___boxed), 7, 1);
lean_closure_set(v___f_723_, 0, v_val_722_);
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___closed__1));
v___x_725_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v___x_724_, v_structType_713_, v___f_723_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec(v___x_721_);
lean_dec_ref(v_structType_713_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f___boxed(lean_object* v_structName_728_, lean_object* v_parentStructName_729_, lean_object* v_structType_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_structName_728_, v_parentStructName_729_, v_structType_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_parentStructName_729_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2(lean_object* v_00_u03b1_737_, lean_object* v_name_738_, uint8_t v_bi_739_, lean_object* v_type_740_, lean_object* v_k_741_, uint8_t v_kind_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___redArg(v_name_738_, v_bi_739_, v_type_740_, v_k_741_, v_kind_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2___boxed(lean_object* v_00_u03b1_749_, lean_object* v_name_750_, lean_object* v_bi_751_, lean_object* v_type_752_, lean_object* v_k_753_, lean_object* v_kind_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
uint8_t v_bi_boxed_760_; uint8_t v_kind_boxed_761_; lean_object* v_res_762_; 
v_bi_boxed_760_ = lean_unbox(v_bi_751_);
v_kind_boxed_761_ = lean_unbox(v_kind_754_);
v_res_762_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2_spec__2(v_00_u03b1_749_, v_name_750_, v_bi_boxed_760_, v_type_752_, v_k_753_, v_kind_boxed_761_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2(lean_object* v_00_u03b1_763_, lean_object* v_name_764_, lean_object* v_type_765_, lean_object* v_k_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___redArg(v_name_764_, v_type_765_, v_k_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2___boxed(lean_object* v_00_u03b1_773_, lean_object* v_name_774_, lean_object* v_type_775_, lean_object* v_k_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__2(v_00_u03b1_773_, v_name_774_, v_type_775_, v_k_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_782_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(lean_object* v_opts_783_, lean_object* v_opt_784_){
_start:
{
lean_object* v_name_785_; lean_object* v_defValue_786_; lean_object* v_map_787_; lean_object* v___x_788_; 
v_name_785_ = lean_ctor_get(v_opt_784_, 0);
v_defValue_786_ = lean_ctor_get(v_opt_784_, 1);
v_map_787_ = lean_ctor_get(v_opts_783_, 0);
v___x_788_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_787_, v_name_785_);
if (lean_obj_tag(v___x_788_) == 0)
{
uint8_t v___x_789_; 
v___x_789_ = lean_unbox(v_defValue_786_);
return v___x_789_;
}
else
{
lean_object* v_val_790_; 
v_val_790_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_val_790_);
lean_dec_ref(v___x_788_);
if (lean_obj_tag(v_val_790_) == 1)
{
uint8_t v_v_791_; 
v_v_791_ = lean_ctor_get_uint8(v_val_790_, 0);
lean_dec_ref(v_val_790_);
return v_v_791_;
}
else
{
uint8_t v___x_792_; 
lean_dec(v_val_790_);
v___x_792_ = lean_unbox(v_defValue_786_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0___boxed(lean_object* v_opts_793_, lean_object* v_opt_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_793_, v_opt_794_);
lean_dec_ref(v_opt_794_);
lean_dec_ref(v_opts_793_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(lean_object* v_kind_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v_auxDeclNGen_801_; lean_object* v___x_802_; lean_object* v_env_803_; lean_object* v___x_804_; lean_object* v_fst_805_; lean_object* v_snd_806_; lean_object* v___x_807_; lean_object* v_env_808_; lean_object* v_nextMacroScope_809_; lean_object* v_ngen_810_; lean_object* v_traceState_811_; lean_object* v_cache_812_; lean_object* v_messages_813_; lean_object* v_infoState_814_; lean_object* v_snapshotTasks_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_824_; 
v___x_800_ = lean_st_ref_get(v___y_798_);
v_auxDeclNGen_801_ = lean_ctor_get(v___x_800_, 3);
lean_inc_ref(v_auxDeclNGen_801_);
lean_dec(v___x_800_);
v___x_802_ = lean_st_ref_get(v___y_798_);
v_env_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_ref(v_env_803_);
lean_dec(v___x_802_);
v___x_804_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_803_, v_auxDeclNGen_801_, v_kind_797_);
v_fst_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_fst_805_);
v_snd_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_snd_806_);
lean_dec_ref(v___x_804_);
v___x_807_ = lean_st_ref_take(v___y_798_);
v_env_808_ = lean_ctor_get(v___x_807_, 0);
v_nextMacroScope_809_ = lean_ctor_get(v___x_807_, 1);
v_ngen_810_ = lean_ctor_get(v___x_807_, 2);
v_traceState_811_ = lean_ctor_get(v___x_807_, 4);
v_cache_812_ = lean_ctor_get(v___x_807_, 5);
v_messages_813_ = lean_ctor_get(v___x_807_, 6);
v_infoState_814_ = lean_ctor_get(v___x_807_, 7);
v_snapshotTasks_815_ = lean_ctor_get(v___x_807_, 8);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_807_, 3);
lean_dec(v_unused_825_);
v___x_817_ = v___x_807_;
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snapshotTasks_815_);
lean_inc(v_infoState_814_);
lean_inc(v_messages_813_);
lean_inc(v_cache_812_);
lean_inc(v_traceState_811_);
lean_inc(v_ngen_810_);
lean_inc(v_nextMacroScope_809_);
lean_inc(v_env_808_);
lean_dec(v___x_807_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 3, v_snd_806_);
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_env_808_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_nextMacroScope_809_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_ngen_810_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_snd_806_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_traceState_811_);
lean_ctor_set(v_reuseFailAlloc_823_, 5, v_cache_812_);
lean_ctor_set(v_reuseFailAlloc_823_, 6, v_messages_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 7, v_infoState_814_);
lean_ctor_set(v_reuseFailAlloc_823_, 8, v_snapshotTasks_815_);
v___x_820_ = v_reuseFailAlloc_823_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_st_ref_set(v___y_798_, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_fst_805_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg___boxed(lean_object* v_kind_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_826_, v___y_827_);
lean_dec(v___y_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(lean_object* v_kind_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_830_, v___y_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___boxed(lean_object* v_kind_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(v_kind_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_843_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_844_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_850_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
lean_ctor_set(v___x_850_, 2, v___x_849_);
lean_ctor_set(v___x_850_, 3, v___x_849_);
lean_ctor_set(v___x_850_, 4, v___x_849_);
lean_ctor_set(v___x_850_, 5, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(lean_object* v_declName_851_, uint8_t v_s_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; lean_object* v_env_857_; lean_object* v_nextMacroScope_858_; lean_object* v_ngen_859_; lean_object* v_auxDeclNGen_860_; lean_object* v_traceState_861_; lean_object* v_messages_862_; lean_object* v_infoState_863_; lean_object* v_snapshotTasks_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_893_; 
v___x_856_ = lean_st_ref_take(v___y_854_);
v_env_857_ = lean_ctor_get(v___x_856_, 0);
v_nextMacroScope_858_ = lean_ctor_get(v___x_856_, 1);
v_ngen_859_ = lean_ctor_get(v___x_856_, 2);
v_auxDeclNGen_860_ = lean_ctor_get(v___x_856_, 3);
v_traceState_861_ = lean_ctor_get(v___x_856_, 4);
v_messages_862_ = lean_ctor_get(v___x_856_, 6);
v_infoState_863_ = lean_ctor_get(v___x_856_, 7);
v_snapshotTasks_864_ = lean_ctor_get(v___x_856_, 8);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_856_, 5);
lean_dec(v_unused_894_);
v___x_866_ = v___x_856_;
v_isShared_867_ = v_isSharedCheck_893_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_snapshotTasks_864_);
lean_inc(v_infoState_863_);
lean_inc(v_messages_862_);
lean_inc(v_traceState_861_);
lean_inc(v_auxDeclNGen_860_);
lean_inc(v_ngen_859_);
lean_inc(v_nextMacroScope_858_);
lean_inc(v_env_857_);
lean_dec(v___x_856_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_893_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_868_ = 0;
v___x_869_ = lean_box(0);
v___x_870_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_857_, v_declName_851_, v_s_852_, v___x_868_, v___x_869_);
v___x_871_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 5, v___x_871_);
lean_ctor_set(v___x_866_, 0, v___x_870_);
v___x_873_ = v___x_866_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_nextMacroScope_858_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_ngen_859_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_auxDeclNGen_860_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_traceState_861_);
lean_ctor_set(v_reuseFailAlloc_892_, 5, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_892_, 6, v_messages_862_);
lean_ctor_set(v_reuseFailAlloc_892_, 7, v_infoState_863_);
lean_ctor_set(v_reuseFailAlloc_892_, 8, v_snapshotTasks_864_);
v___x_873_ = v_reuseFailAlloc_892_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_mctx_876_; lean_object* v_zetaDeltaFVarIds_877_; lean_object* v_postponed_878_; lean_object* v_diag_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_890_; 
v___x_874_ = lean_st_ref_set(v___y_854_, v___x_873_);
v___x_875_ = lean_st_ref_take(v___y_853_);
v_mctx_876_ = lean_ctor_get(v___x_875_, 0);
v_zetaDeltaFVarIds_877_ = lean_ctor_get(v___x_875_, 2);
v_postponed_878_ = lean_ctor_get(v___x_875_, 3);
v_diag_879_ = lean_ctor_get(v___x_875_, 4);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_875_, 1);
lean_dec(v_unused_891_);
v___x_881_ = v___x_875_;
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_diag_879_);
lean_inc(v_postponed_878_);
lean_inc(v_zetaDeltaFVarIds_877_);
lean_inc(v_mctx_876_);
lean_dec(v___x_875_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v___x_883_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_mctx_876_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_zetaDeltaFVarIds_877_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_postponed_878_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_diag_879_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = lean_st_ref_set(v___y_853_, v___x_885_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___boxed(lean_object* v_declName_895_, lean_object* v_s_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v_s_boxed_900_; lean_object* v_res_901_; 
v_s_boxed_900_ = lean_unbox(v_s_896_);
v_res_901_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_895_, v_s_boxed_900_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec(v___y_897_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(lean_object* v_declName_902_, uint8_t v_s_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_902_, v_s_903_, v___y_905_, v___y_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object* v_declName_910_, lean_object* v_s_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v_s_boxed_917_; lean_object* v_res_918_; 
v_s_boxed_917_ = lean_unbox(v_s_911_);
v_res_918_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(v_declName_910_, v_s_boxed_917_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(lean_object* v_e_919_, lean_object* v___y_920_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_Expr_hasMVar(v_e_919_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v_e_919_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; lean_object* v_mctx_925_; lean_object* v___x_926_; lean_object* v_fst_927_; lean_object* v_snd_928_; lean_object* v___x_929_; lean_object* v_cache_930_; lean_object* v_zetaDeltaFVarIds_931_; lean_object* v_postponed_932_; lean_object* v_diag_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_942_; 
v___x_924_ = lean_st_ref_get(v___y_920_);
v_mctx_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc_ref(v_mctx_925_);
lean_dec(v___x_924_);
v___x_926_ = l_Lean_instantiateMVarsCore(v_mctx_925_, v_e_919_);
v_fst_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_fst_927_);
v_snd_928_ = lean_ctor_get(v___x_926_, 1);
lean_inc(v_snd_928_);
lean_dec_ref(v___x_926_);
v___x_929_ = lean_st_ref_take(v___y_920_);
v_cache_930_ = lean_ctor_get(v___x_929_, 1);
v_zetaDeltaFVarIds_931_ = lean_ctor_get(v___x_929_, 2);
v_postponed_932_ = lean_ctor_get(v___x_929_, 3);
v_diag_933_ = lean_ctor_get(v___x_929_, 4);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_943_);
v___x_935_ = v___x_929_;
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_diag_933_);
lean_inc(v_postponed_932_);
lean_inc(v_zetaDeltaFVarIds_931_);
lean_inc(v_cache_930_);
lean_dec(v___x_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_942_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v_snd_928_);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_snd_928_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_cache_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_zetaDeltaFVarIds_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_postponed_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_diag_933_);
v___x_938_ = v_reuseFailAlloc_941_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_st_ref_set(v___y_920_, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_fst_927_);
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object* v_e_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_e_944_, v___y_945_);
lean_dec(v___y_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5(lean_object* v_e_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_e_948_, v___y_950_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object* v_e_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5(v_e_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_961_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_unsigned_to_nat(32u);
v___x_963_ = lean_mk_empty_array_with_capacity(v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_965_ = ((size_t)5ULL);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_unsigned_to_nat(32u);
v___x_968_ = lean_mk_empty_array_with_capacity(v___x_967_);
v___x_969_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__0);
v___x_970_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
lean_ctor_set(v___x_970_, 2, v___x_966_);
lean_ctor_set(v___x_970_, 3, v___x_966_);
lean_ctor_set_usize(v___x_970_, 4, v___x_965_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; lean_object* v_traceState_974_; lean_object* v_traces_975_; lean_object* v___x_976_; lean_object* v_traceState_977_; lean_object* v_env_978_; lean_object* v_nextMacroScope_979_; lean_object* v_ngen_980_; lean_object* v_auxDeclNGen_981_; lean_object* v_cache_982_; lean_object* v_messages_983_; lean_object* v_infoState_984_; lean_object* v_snapshotTasks_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1004_; 
v___x_973_ = lean_st_ref_get(v___y_971_);
v_traceState_974_ = lean_ctor_get(v___x_973_, 4);
lean_inc_ref(v_traceState_974_);
lean_dec(v___x_973_);
v_traces_975_ = lean_ctor_get(v_traceState_974_, 0);
lean_inc_ref(v_traces_975_);
lean_dec_ref(v_traceState_974_);
v___x_976_ = lean_st_ref_take(v___y_971_);
v_traceState_977_ = lean_ctor_get(v___x_976_, 4);
v_env_978_ = lean_ctor_get(v___x_976_, 0);
v_nextMacroScope_979_ = lean_ctor_get(v___x_976_, 1);
v_ngen_980_ = lean_ctor_get(v___x_976_, 2);
v_auxDeclNGen_981_ = lean_ctor_get(v___x_976_, 3);
v_cache_982_ = lean_ctor_get(v___x_976_, 5);
v_messages_983_ = lean_ctor_get(v___x_976_, 6);
v_infoState_984_ = lean_ctor_get(v___x_976_, 7);
v_snapshotTasks_985_ = lean_ctor_get(v___x_976_, 8);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_987_ = v___x_976_;
v_isShared_988_ = v_isSharedCheck_1004_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snapshotTasks_985_);
lean_inc(v_infoState_984_);
lean_inc(v_messages_983_);
lean_inc(v_cache_982_);
lean_inc(v_traceState_977_);
lean_inc(v_auxDeclNGen_981_);
lean_inc(v_ngen_980_);
lean_inc(v_nextMacroScope_979_);
lean_inc(v_env_978_);
lean_dec(v___x_976_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1004_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
uint64_t v_tid_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1002_; 
v_tid_989_ = lean_ctor_get_uint64(v_traceState_977_, sizeof(void*)*1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_traceState_977_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v_traceState_977_, 0);
lean_dec(v_unused_1003_);
v___x_991_ = v_traceState_977_;
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
else
{
lean_dec(v_traceState_977_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___closed__1);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_993_);
lean_ctor_set_uint64(v_reuseFailAlloc_1001_, sizeof(void*)*1, v_tid_989_);
v___x_995_ = v_reuseFailAlloc_1001_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 4, v___x_995_);
v___x_997_ = v___x_987_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_env_978_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_nextMacroScope_979_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_ngen_980_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_auxDeclNGen_981_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1000_, 5, v_cache_982_);
lean_ctor_set(v_reuseFailAlloc_1000_, 6, v_messages_983_);
lean_ctor_set(v_reuseFailAlloc_1000_, 7, v_infoState_984_);
lean_ctor_set(v_reuseFailAlloc_1000_, 8, v_snapshotTasks_985_);
v___x_997_ = v_reuseFailAlloc_1000_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_st_ref_set(v___y_971_, v___x_997_);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v_traces_975_);
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___y_1005_);
lean_dec(v___y_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11(lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___y_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11(v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1019_;
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Meta_wrapInstance___lam__0___closed__0));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object* v_expectedType_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = lean_obj_once(&l_Lean_Meta_wrapInstance___lam__0___closed__1, &l_Lean_Meta_wrapInstance___lam__0___closed__1_once, _init_l_Lean_Meta_wrapInstance___lam__0___closed__1);
v___x_1031_ = l_Lean_MessageData_ofExpr(v_expectedType_1023_);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object* v_expectedType_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Meta_wrapInstance___lam__0(v_expectedType_1034_, v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_x_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
if (lean_obj_tag(v_a_1042_) == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_List_reverse___redArg(v_a_1043_);
return v___x_1044_;
}
else
{
lean_object* v_head_1045_; lean_object* v_tail_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1055_; 
v_head_1045_ = lean_ctor_get(v_a_1042_, 0);
v_tail_1046_ = lean_ctor_get(v_a_1042_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_a_1042_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1048_ = v_a_1042_;
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_tail_1046_);
lean_inc(v_head_1045_);
lean_dec(v_a_1042_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = l_Lean_MessageData_ofExpr(v_head_1045_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v_a_1043_);
lean_ctor_set(v___x_1048_, 0, v___x_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_a_1043_);
v___x_1052_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
v_a_1042_ = v_tail_1046_;
v_a_1043_ = v___x_1052_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__0);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
lean_ctor_set(v___x_1061_, 2, v___x_1060_);
lean_ctor_set(v___x_1061_, 3, v___x_1060_);
lean_ctor_set(v___x_1061_, 4, v___x_1059_);
lean_ctor_set(v___x_1061_, 5, v___x_1059_);
lean_ctor_set(v___x_1061_, 6, v___x_1059_);
lean_ctor_set(v___x_1061_, 7, v___x_1059_);
lean_ctor_set(v___x_1061_, 8, v___x_1059_);
lean_ctor_set(v___x_1061_, 9, v___x_1059_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_unsigned_to_nat(32u);
v___x_1063_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1065_ = ((size_t)5ULL);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_unsigned_to_nat(32u);
v___x_1068_ = lean_mk_empty_array_with_capacity(v___x_1067_);
v___x_1069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__3);
v___x_1070_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
lean_ctor_set(v___x_1070_, 2, v___x_1066_);
lean_ctor_set(v___x_1070_, 3, v___x_1066_);
lean_ctor_set_usize(v___x_1070_, 4, v___x_1065_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1071_ = lean_box(1);
v___x_1072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__4);
v___x_1073_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__1);
v___x_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1072_);
lean_ctor_set(v___x_1074_, 2, v___x_1071_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__6));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__8));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__10));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__12));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__14));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__16));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__18));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(lean_object* v_msg_1096_, lean_object* v_declHint_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v_env_1101_; uint8_t v___x_1102_; 
v___x_1100_ = lean_st_ref_get(v___y_1098_);
v_env_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_ref(v_env_1101_);
lean_dec(v___x_1100_);
v___x_1102_ = l_Lean_Name_isAnonymous(v_declHint_1097_);
if (v___x_1102_ == 0)
{
uint8_t v_isExporting_1103_; 
v_isExporting_1103_ = lean_ctor_get_uint8(v_env_1101_, sizeof(void*)*8);
if (v_isExporting_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_dec_ref(v_env_1101_);
lean_dec(v_declHint_1097_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_msg_1096_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
lean_inc_ref(v_env_1101_);
v___x_1105_ = l_Lean_Environment_setExporting(v_env_1101_, v___x_1102_);
lean_inc(v_declHint_1097_);
lean_inc_ref(v___x_1105_);
v___x_1106_ = l_Lean_Environment_contains(v___x_1105_, v_declHint_1097_, v_isExporting_1103_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; 
lean_dec_ref(v___x_1105_);
lean_dec_ref(v_env_1101_);
lean_dec(v_declHint_1097_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_msg_1096_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_c_1113_; lean_object* v___x_1114_; 
v___x_1108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__2);
v___x_1109_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__5);
v___x_1110_ = l_Lean_Options_empty;
v___x_1111_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1105_);
lean_ctor_set(v___x_1111_, 1, v___x_1108_);
lean_ctor_set(v___x_1111_, 2, v___x_1109_);
lean_ctor_set(v___x_1111_, 3, v___x_1110_);
lean_inc(v_declHint_1097_);
v___x_1112_ = l_Lean_MessageData_ofConstName(v_declHint_1097_, v___x_1102_);
v_c_1113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1113_, 0, v___x_1111_);
lean_ctor_set(v_c_1113_, 1, v___x_1112_);
v___x_1114_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1101_, v_declHint_1097_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref(v_env_1101_);
lean_dec(v_declHint_1097_);
v___x_1115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_c_1113_);
v___x_1117_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__9);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_MessageData_note(v___x_1118_);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_msg_1096_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
else
{
lean_object* v_val_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1157_; 
v_val_1122_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1124_ = v___x_1114_;
v_isShared_1125_ = v_isSharedCheck_1157_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_val_1122_);
lean_dec(v___x_1114_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1157_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_mod_1129_; uint8_t v___x_1130_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = l_Lean_Environment_header(v_env_1101_);
lean_dec_ref(v_env_1101_);
v___x_1128_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1127_);
v_mod_1129_ = lean_array_get(v___x_1126_, v___x_1128_, v_val_1122_);
lean_dec(v_val_1122_);
lean_dec_ref(v___x_1128_);
v___x_1130_ = l_Lean_isPrivateName(v_declHint_1097_);
lean_dec(v_declHint_1097_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__11);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_c_1113_);
v___x_1133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__13);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_ofName(v_mod_1129_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__15);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_MessageData_note(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_msg_1096_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1140_);
v___x_1142_ = v___x_1124_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__7);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v_c_1113_);
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__17);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = l_Lean_MessageData_ofName(v_mod_1129_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___closed__19);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_note(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_msg_1096_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1153_);
v___x_1155_ = v___x_1124_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v_env_1101_);
lean_dec(v_declHint_1097_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v_msg_1096_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg___boxed(lean_object* v_msg_1159_, lean_object* v_declHint_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(v_msg_1159_, v_declHint_1160_, v___y_1161_);
lean_dec(v___y_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28(lean_object* v_msg_1164_, lean_object* v_declHint_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1181_; 
v___x_1171_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(v_msg_1164_, v_declHint_1165_, v___y_1169_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = l_Lean_unknownIdentifierMessageTag;
v___x_1177_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v_a_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28___boxed(lean_object* v_msg_1182_, lean_object* v_declHint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28(v_msg_1182_, v_declHint_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(lean_object* v_ref_1190_, lean_object* v_msg_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_fileName_1197_; lean_object* v_fileMap_1198_; lean_object* v_options_1199_; lean_object* v_currRecDepth_1200_; lean_object* v_maxRecDepth_1201_; lean_object* v_ref_1202_; lean_object* v_currNamespace_1203_; lean_object* v_openDecls_1204_; lean_object* v_initHeartbeats_1205_; lean_object* v_maxHeartbeats_1206_; lean_object* v_quotContext_1207_; lean_object* v_currMacroScope_1208_; uint8_t v_diag_1209_; lean_object* v_cancelTk_x3f_1210_; uint8_t v_suppressElabErrors_1211_; lean_object* v_inheritedTraceOptions_1212_; lean_object* v_ref_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_fileName_1197_ = lean_ctor_get(v___y_1194_, 0);
v_fileMap_1198_ = lean_ctor_get(v___y_1194_, 1);
v_options_1199_ = lean_ctor_get(v___y_1194_, 2);
v_currRecDepth_1200_ = lean_ctor_get(v___y_1194_, 3);
v_maxRecDepth_1201_ = lean_ctor_get(v___y_1194_, 4);
v_ref_1202_ = lean_ctor_get(v___y_1194_, 5);
v_currNamespace_1203_ = lean_ctor_get(v___y_1194_, 6);
v_openDecls_1204_ = lean_ctor_get(v___y_1194_, 7);
v_initHeartbeats_1205_ = lean_ctor_get(v___y_1194_, 8);
v_maxHeartbeats_1206_ = lean_ctor_get(v___y_1194_, 9);
v_quotContext_1207_ = lean_ctor_get(v___y_1194_, 10);
v_currMacroScope_1208_ = lean_ctor_get(v___y_1194_, 11);
v_diag_1209_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*14);
v_cancelTk_x3f_1210_ = lean_ctor_get(v___y_1194_, 12);
v_suppressElabErrors_1211_ = lean_ctor_get_uint8(v___y_1194_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1212_ = lean_ctor_get(v___y_1194_, 13);
v_ref_1213_ = l_Lean_replaceRef(v_ref_1190_, v_ref_1202_);
lean_inc_ref(v_inheritedTraceOptions_1212_);
lean_inc(v_cancelTk_x3f_1210_);
lean_inc(v_currMacroScope_1208_);
lean_inc(v_quotContext_1207_);
lean_inc(v_maxHeartbeats_1206_);
lean_inc(v_initHeartbeats_1205_);
lean_inc(v_openDecls_1204_);
lean_inc(v_currNamespace_1203_);
lean_inc(v_maxRecDepth_1201_);
lean_inc(v_currRecDepth_1200_);
lean_inc_ref(v_options_1199_);
lean_inc_ref(v_fileMap_1198_);
lean_inc_ref(v_fileName_1197_);
v___x_1214_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1214_, 0, v_fileName_1197_);
lean_ctor_set(v___x_1214_, 1, v_fileMap_1198_);
lean_ctor_set(v___x_1214_, 2, v_options_1199_);
lean_ctor_set(v___x_1214_, 3, v_currRecDepth_1200_);
lean_ctor_set(v___x_1214_, 4, v_maxRecDepth_1201_);
lean_ctor_set(v___x_1214_, 5, v_ref_1213_);
lean_ctor_set(v___x_1214_, 6, v_currNamespace_1203_);
lean_ctor_set(v___x_1214_, 7, v_openDecls_1204_);
lean_ctor_set(v___x_1214_, 8, v_initHeartbeats_1205_);
lean_ctor_set(v___x_1214_, 9, v_maxHeartbeats_1206_);
lean_ctor_set(v___x_1214_, 10, v_quotContext_1207_);
lean_ctor_set(v___x_1214_, 11, v_currMacroScope_1208_);
lean_ctor_set(v___x_1214_, 12, v_cancelTk_x3f_1210_);
lean_ctor_set(v___x_1214_, 13, v_inheritedTraceOptions_1212_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*14, v_diag_1209_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*14 + 1, v_suppressElabErrors_1211_);
v___x_1215_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v_msg_1191_, v___y_1192_, v___y_1193_, v___x_1214_, v___y_1195_);
lean_dec_ref(v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg___boxed(lean_object* v_ref_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(v_ref_1216_, v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v_ref_1216_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(lean_object* v_ref_1224_, lean_object* v_msg_1225_, lean_object* v_declHint_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; 
v___x_1232_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28(v_msg_1225_, v_declHint_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(v_ref_1224_, v_a_1233_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1235_, lean_object* v_msg_1236_, lean_object* v_declHint_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(v_ref_1235_, v_msg_1236_, v_declHint_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v_ref_1235_);
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__0));
v___x_1246_ = l_Lean_stringToMessageData(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(lean_object* v_ref_1247_, lean_object* v_constName_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1254_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___closed__1);
v___x_1255_ = 0;
lean_inc(v_constName_1248_);
v___x_1256_ = l_Lean_MessageData_ofConstName(v_constName_1248_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1254_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(v_ref_1247_, v___x_1259_, v_constName_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg___boxed(lean_object* v_ref_1261_, lean_object* v_constName_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(v_ref_1261_, v_constName_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v_ref_1261_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_ref_1275_; lean_object* v___x_1276_; 
v_ref_1275_ = lean_ctor_get(v___y_1272_, 5);
v___x_1276_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(v_ref_1275_, v_constName_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg___boxed(lean_object* v_constName_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object* v_constName_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v_env_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_st_ref_get(v___y_1288_);
v_env_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc_ref(v_env_1291_);
lean_dec(v___x_1290_);
v___x_1292_ = 0;
lean_inc(v_constName_1284_);
v___x_1293_ = l_Lean_Environment_find_x3f(v_env_1291_, v_constName_1284_, v___x_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1294_;
}
else
{
lean_object* v_val_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_constName_1284_);
v_val_1295_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1293_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_val_1295_);
lean_dec(v___x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set_tag(v___x_1297_, 0);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object* v_constName_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_constName_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(size_t v_sz_1310_, size_t v_i_1311_, lean_object* v_bs_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_lt(v_i_1311_, v_sz_1310_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_bs_1312_);
return v___x_1319_;
}
else
{
lean_object* v_v_1320_; lean_object* v___x_1321_; 
v_v_1320_ = lean_array_uget_borrowed(v_bs_1312_, v_i_1311_);
lean_inc(v_v_1320_);
v___x_1321_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_v_1320_, v___y_1314_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v_bs_x27_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1321_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v_bs_x27_1324_ = lean_array_uset(v_bs_1312_, v_i_1311_, v___x_1323_);
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_add(v_i_1311_, v___x_1325_);
v___x_1327_ = lean_array_uset(v_bs_x27_1324_, v_i_1311_, v_a_1322_);
v_i_1311_ = v___x_1326_;
v_bs_1312_ = v___x_1327_;
goto _start;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_bs_1312_);
v_a_1329_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1321_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1321_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_bs_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_boxed_1345_, v_i_boxed_1346_, v_bs_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object* v_cls_1348_, lean_object* v_msg_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_ref_1355_; lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1401_; 
v_ref_1355_ = lean_ctor_get(v___y_1352_, 5);
v___x_1356_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1401_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1401_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v_traceState_1362_; lean_object* v_env_1363_; lean_object* v_nextMacroScope_1364_; lean_object* v_ngen_1365_; lean_object* v_auxDeclNGen_1366_; lean_object* v_cache_1367_; lean_object* v_messages_1368_; lean_object* v_infoState_1369_; lean_object* v_snapshotTasks_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1400_; 
v___x_1361_ = lean_st_ref_take(v___y_1353_);
v_traceState_1362_ = lean_ctor_get(v___x_1361_, 4);
v_env_1363_ = lean_ctor_get(v___x_1361_, 0);
v_nextMacroScope_1364_ = lean_ctor_get(v___x_1361_, 1);
v_ngen_1365_ = lean_ctor_get(v___x_1361_, 2);
v_auxDeclNGen_1366_ = lean_ctor_get(v___x_1361_, 3);
v_cache_1367_ = lean_ctor_get(v___x_1361_, 5);
v_messages_1368_ = lean_ctor_get(v___x_1361_, 6);
v_infoState_1369_ = lean_ctor_get(v___x_1361_, 7);
v_snapshotTasks_1370_ = lean_ctor_get(v___x_1361_, 8);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1372_ = v___x_1361_;
v_isShared_1373_ = v_isSharedCheck_1400_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_snapshotTasks_1370_);
lean_inc(v_infoState_1369_);
lean_inc(v_messages_1368_);
lean_inc(v_cache_1367_);
lean_inc(v_traceState_1362_);
lean_inc(v_auxDeclNGen_1366_);
lean_inc(v_ngen_1365_);
lean_inc(v_nextMacroScope_1364_);
lean_inc(v_env_1363_);
lean_dec(v___x_1361_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1400_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
uint64_t v_tid_1374_; lean_object* v_traces_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1399_; 
v_tid_1374_ = lean_ctor_get_uint64(v_traceState_1362_, sizeof(void*)*1);
v_traces_1375_ = lean_ctor_get(v_traceState_1362_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_traceState_1362_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1377_ = v_traceState_1362_;
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_traces_1375_);
lean_dec(v_traceState_1362_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1399_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; double v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
v___x_1381_ = 0;
v___x_1382_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_1383_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1383_, 0, v_cls_1348_);
lean_ctor_set(v___x_1383_, 1, v___x_1379_);
lean_ctor_set(v___x_1383_, 2, v___x_1382_);
lean_ctor_set_float(v___x_1383_, sizeof(void*)*3, v___x_1380_);
lean_ctor_set_float(v___x_1383_, sizeof(void*)*3 + 8, v___x_1380_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*3 + 16, v___x_1381_);
v___x_1384_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__2));
v___x_1385_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v_a_1357_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
lean_inc(v_ref_1355_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_ref_1355_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = l_Lean_PersistentArray_push___redArg(v_traces_1375_, v___x_1386_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1387_);
v___x_1389_ = v___x_1377_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1387_);
lean_ctor_set_uint64(v_reuseFailAlloc_1398_, sizeof(void*)*1, v_tid_1374_);
v___x_1389_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___x_1389_);
v___x_1391_ = v___x_1372_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_env_1363_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_nextMacroScope_1364_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_ngen_1365_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_auxDeclNGen_1366_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v_cache_1367_);
lean_ctor_set(v_reuseFailAlloc_1397_, 6, v_messages_1368_);
lean_ctor_set(v_reuseFailAlloc_1397_, 7, v_infoState_1369_);
lean_ctor_set(v_reuseFailAlloc_1397_, 8, v_snapshotTasks_1370_);
v___x_1391_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = lean_st_ref_set(v___y_1353_, v___x_1391_);
v___x_1393_ = lean_box(0);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1393_);
v___x_1395_ = v___x_1359_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object* v_cls_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1402_, v_msg_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32___redArg(lean_object* v_x_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
lean_object* v_ks_1414_; lean_object* v_vs_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1439_; 
v_ks_1414_ = lean_ctor_get(v_x_1410_, 0);
v_vs_1415_ = lean_ctor_get(v_x_1410_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_x_1410_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1417_ = v_x_1410_;
v_isShared_1418_ = v_isSharedCheck_1439_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_vs_1415_);
lean_inc(v_ks_1414_);
lean_dec(v_x_1410_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1439_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = lean_array_get_size(v_ks_1414_);
v___x_1420_ = lean_nat_dec_lt(v_x_1411_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec(v_x_1411_);
v___x_1421_ = lean_array_push(v_ks_1414_, v_x_1412_);
v___x_1422_ = lean_array_push(v_vs_1415_, v_x_1413_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1422_);
lean_ctor_set(v___x_1417_, 0, v___x_1421_);
v___x_1424_ = v___x_1417_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
lean_object* v_k_x27_1426_; uint8_t v___x_1427_; 
v_k_x27_1426_ = lean_array_fget_borrowed(v_ks_1414_, v_x_1411_);
v___x_1427_ = l_Lean_instBEqMVarId_beq(v_x_1412_, v_k_x27_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1429_; 
if (v_isShared_1418_ == 0)
{
v___x_1429_ = v___x_1417_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_ks_1414_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_vs_1415_);
v___x_1429_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_nat_add(v_x_1411_, v___x_1430_);
lean_dec(v_x_1411_);
v_x_1410_ = v___x_1429_;
v_x_1411_ = v___x_1431_;
goto _start;
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = lean_array_fset(v_ks_1414_, v_x_1411_, v_x_1412_);
v___x_1435_ = lean_array_fset(v_vs_1415_, v_x_1411_, v_x_1413_);
lean_dec(v_x_1411_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1435_);
lean_ctor_set(v___x_1417_, 0, v___x_1434_);
v___x_1437_ = v___x_1417_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24___redArg(lean_object* v_n_1440_, lean_object* v_k_1441_, lean_object* v_v_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32___redArg(v_n_1440_, v___x_1443_, v_k_1441_, v_v_1442_);
return v___x_1444_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0(void){
_start:
{
size_t v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; 
v___x_1445_ = ((size_t)5ULL);
v___x_1446_ = ((size_t)1ULL);
v___x_1447_ = lean_usize_shift_left(v___x_1446_, v___x_1445_);
return v___x_1447_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1(void){
_start:
{
size_t v___x_1448_; size_t v___x_1449_; size_t v___x_1450_; 
v___x_1448_ = ((size_t)1ULL);
v___x_1449_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__0);
v___x_1450_ = lean_usize_sub(v___x_1449_, v___x_1448_);
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(lean_object* v_x_1452_, size_t v_x_1453_, size_t v_x_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
if (lean_obj_tag(v_x_1452_) == 0)
{
lean_object* v_es_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; lean_object* v_j_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_es_1457_ = lean_ctor_get(v_x_1452_, 0);
v___x_1458_ = ((size_t)5ULL);
v___x_1459_ = ((size_t)1ULL);
v___x_1460_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__1);
v___x_1461_ = lean_usize_land(v_x_1453_, v___x_1460_);
v_j_1462_ = lean_usize_to_nat(v___x_1461_);
v___x_1463_ = lean_array_get_size(v_es_1457_);
v___x_1464_ = lean_nat_dec_lt(v_j_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec(v_j_1462_);
lean_dec(v_x_1456_);
lean_dec(v_x_1455_);
return v_x_1452_;
}
else
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1501_; 
lean_inc_ref(v_es_1457_);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_x_1452_, 0);
lean_dec(v_unused_1502_);
v___x_1466_ = v_x_1452_;
v_isShared_1467_ = v_isSharedCheck_1501_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_x_1452_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1501_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_v_1468_; lean_object* v___x_1469_; lean_object* v_xs_x27_1470_; lean_object* v___y_1472_; 
v_v_1468_ = lean_array_fget(v_es_1457_, v_j_1462_);
v___x_1469_ = lean_box(0);
v_xs_x27_1470_ = lean_array_fset(v_es_1457_, v_j_1462_, v___x_1469_);
switch(lean_obj_tag(v_v_1468_))
{
case 0:
{
lean_object* v_key_1477_; lean_object* v_val_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1488_; 
v_key_1477_ = lean_ctor_get(v_v_1468_, 0);
v_val_1478_ = lean_ctor_get(v_v_1468_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_v_1468_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1480_ = v_v_1468_;
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_val_1478_);
lean_inc(v_key_1477_);
lean_dec(v_v_1468_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Lean_instBEqMVarId_beq(v_x_1455_, v_key_1477_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_del_object(v___x_1480_);
v___x_1483_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1477_, v_val_1478_, v_x_1455_, v_x_1456_);
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
v___y_1472_ = v___x_1484_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_val_1478_);
lean_dec(v_key_1477_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_x_1456_);
lean_ctor_set(v___x_1480_, 0, v_x_1455_);
v___x_1486_ = v___x_1480_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_x_1455_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_x_1456_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v___y_1472_ = v___x_1486_;
goto v___jp_1471_;
}
}
}
}
case 1:
{
lean_object* v_node_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1499_; 
v_node_1489_ = lean_ctor_get(v_v_1468_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_v_1468_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1491_ = v_v_1468_;
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_node_1489_);
lean_dec(v_v_1468_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1493_ = lean_usize_shift_right(v_x_1453_, v___x_1458_);
v___x_1494_ = lean_usize_add(v_x_1454_, v___x_1459_);
v___x_1495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_node_1489_, v___x_1493_, v___x_1494_, v_x_1455_, v_x_1456_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1495_);
v___x_1497_ = v___x_1491_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v___y_1472_ = v___x_1497_;
goto v___jp_1471_;
}
}
}
default: 
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_x_1455_);
lean_ctor_set(v___x_1500_, 1, v_x_1456_);
v___y_1472_ = v___x_1500_;
goto v___jp_1471_;
}
}
v___jp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_array_fset(v_xs_x27_1470_, v_j_1462_, v___y_1472_);
lean_dec(v_j_1462_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1473_);
v___x_1475_ = v___x_1466_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
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
else
{
lean_object* v_ks_1503_; lean_object* v_vs_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1524_; 
v_ks_1503_ = lean_ctor_get(v_x_1452_, 0);
v_vs_1504_ = lean_ctor_get(v_x_1452_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_x_1452_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1506_ = v_x_1452_;
v_isShared_1507_ = v_isSharedCheck_1524_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_vs_1504_);
lean_inc(v_ks_1503_);
lean_dec(v_x_1452_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1524_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_ks_1503_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_vs_1504_);
v___x_1509_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v_newNode_1510_; uint8_t v___y_1512_; size_t v___x_1518_; uint8_t v___x_1519_; 
v_newNode_1510_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24___redArg(v___x_1509_, v_x_1455_, v_x_1456_);
v___x_1518_ = ((size_t)7ULL);
v___x_1519_ = lean_usize_dec_le(v___x_1518_, v_x_1454_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1520_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1510_);
v___x_1521_ = lean_unsigned_to_nat(4u);
v___x_1522_ = lean_nat_dec_lt(v___x_1520_, v___x_1521_);
lean_dec(v___x_1520_);
v___y_1512_ = v___x_1522_;
goto v___jp_1511_;
}
else
{
v___y_1512_ = v___x_1519_;
goto v___jp_1511_;
}
v___jp_1511_:
{
if (v___y_1512_ == 0)
{
lean_object* v_ks_1513_; lean_object* v_vs_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_ks_1513_ = lean_ctor_get(v_newNode_1510_, 0);
lean_inc_ref(v_ks_1513_);
v_vs_1514_ = lean_ctor_get(v_newNode_1510_, 1);
lean_inc_ref(v_vs_1514_);
lean_dec_ref(v_newNode_1510_);
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___closed__2);
v___x_1517_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(v_x_1454_, v_ks_1513_, v_vs_1514_, v___x_1515_, v___x_1516_);
lean_dec_ref(v_vs_1514_);
lean_dec_ref(v_ks_1513_);
return v___x_1517_;
}
else
{
return v_newNode_1510_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(size_t v_depth_1525_, lean_object* v_keys_1526_, lean_object* v_vals_1527_, lean_object* v_i_1528_, lean_object* v_entries_1529_){
_start:
{
lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1530_ = lean_array_get_size(v_keys_1526_);
v___x_1531_ = lean_nat_dec_lt(v_i_1528_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_dec(v_i_1528_);
return v_entries_1529_;
}
else
{
lean_object* v_k_1532_; lean_object* v_v_1533_; uint64_t v___x_1534_; size_t v_h_1535_; size_t v___x_1536_; lean_object* v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; size_t v_h_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_k_1532_ = lean_array_fget_borrowed(v_keys_1526_, v_i_1528_);
v_v_1533_ = lean_array_fget_borrowed(v_vals_1527_, v_i_1528_);
v___x_1534_ = l_Lean_instHashableMVarId_hash(v_k_1532_);
v_h_1535_ = lean_uint64_to_usize(v___x_1534_);
v___x_1536_ = ((size_t)5ULL);
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_sub(v_depth_1525_, v___x_1538_);
v___x_1540_ = lean_usize_mul(v___x_1536_, v___x_1539_);
v_h_1541_ = lean_usize_shift_right(v_h_1535_, v___x_1540_);
v___x_1542_ = lean_nat_add(v_i_1528_, v___x_1537_);
lean_dec(v_i_1528_);
lean_inc(v_v_1533_);
lean_inc(v_k_1532_);
v___x_1543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_entries_1529_, v_h_1541_, v_depth_1525_, v_k_1532_, v_v_1533_);
v_i_1528_ = v___x_1542_;
v_entries_1529_ = v___x_1543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg___boxed(lean_object* v_depth_1545_, lean_object* v_keys_1546_, lean_object* v_vals_1547_, lean_object* v_i_1548_, lean_object* v_entries_1549_){
_start:
{
size_t v_depth_boxed_1550_; lean_object* v_res_1551_; 
v_depth_boxed_1550_ = lean_unbox_usize(v_depth_1545_);
lean_dec(v_depth_1545_);
v_res_1551_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(v_depth_boxed_1550_, v_keys_1546_, v_vals_1547_, v_i_1548_, v_entries_1549_);
lean_dec_ref(v_vals_1547_);
lean_dec_ref(v_keys_1546_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_){
_start:
{
size_t v_x_160244__boxed_1557_; size_t v_x_160245__boxed_1558_; lean_object* v_res_1559_; 
v_x_160244__boxed_1557_ = lean_unbox_usize(v_x_1553_);
lean_dec(v_x_1553_);
v_x_160245__boxed_1558_ = lean_unbox_usize(v_x_1554_);
lean_dec(v_x_1554_);
v_res_1559_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_x_1552_, v_x_160244__boxed_1557_, v_x_160245__boxed_1558_, v_x_1555_, v_x_1556_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8___redArg(lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_){
_start:
{
uint64_t v___x_1563_; size_t v___x_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v___x_1563_ = l_Lean_instHashableMVarId_hash(v_x_1561_);
v___x_1564_ = lean_uint64_to_usize(v___x_1563_);
v___x_1565_ = ((size_t)1ULL);
v___x_1566_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_x_1560_, v___x_1564_, v___x_1565_, v_x_1561_, v_x_1562_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object* v_mvarId_1567_, lean_object* v_val_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; lean_object* v_mctx_1572_; lean_object* v_cache_1573_; lean_object* v_zetaDeltaFVarIds_1574_; lean_object* v_postponed_1575_; lean_object* v_diag_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1604_; 
v___x_1571_ = lean_st_ref_take(v___y_1569_);
v_mctx_1572_ = lean_ctor_get(v___x_1571_, 0);
v_cache_1573_ = lean_ctor_get(v___x_1571_, 1);
v_zetaDeltaFVarIds_1574_ = lean_ctor_get(v___x_1571_, 2);
v_postponed_1575_ = lean_ctor_get(v___x_1571_, 3);
v_diag_1576_ = lean_ctor_get(v___x_1571_, 4);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1578_ = v___x_1571_;
v_isShared_1579_ = v_isSharedCheck_1604_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_diag_1576_);
lean_inc(v_postponed_1575_);
lean_inc(v_zetaDeltaFVarIds_1574_);
lean_inc(v_cache_1573_);
lean_inc(v_mctx_1572_);
lean_dec(v___x_1571_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1604_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_depth_1580_; lean_object* v_levelAssignDepth_1581_; lean_object* v_lmvarCounter_1582_; lean_object* v_mvarCounter_1583_; lean_object* v_lDecls_1584_; lean_object* v_decls_1585_; lean_object* v_userNames_1586_; lean_object* v_lAssignment_1587_; lean_object* v_eAssignment_1588_; lean_object* v_dAssignment_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1603_; 
v_depth_1580_ = lean_ctor_get(v_mctx_1572_, 0);
v_levelAssignDepth_1581_ = lean_ctor_get(v_mctx_1572_, 1);
v_lmvarCounter_1582_ = lean_ctor_get(v_mctx_1572_, 2);
v_mvarCounter_1583_ = lean_ctor_get(v_mctx_1572_, 3);
v_lDecls_1584_ = lean_ctor_get(v_mctx_1572_, 4);
v_decls_1585_ = lean_ctor_get(v_mctx_1572_, 5);
v_userNames_1586_ = lean_ctor_get(v_mctx_1572_, 6);
v_lAssignment_1587_ = lean_ctor_get(v_mctx_1572_, 7);
v_eAssignment_1588_ = lean_ctor_get(v_mctx_1572_, 8);
v_dAssignment_1589_ = lean_ctor_get(v_mctx_1572_, 9);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_mctx_1572_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1591_ = v_mctx_1572_;
v_isShared_1592_ = v_isSharedCheck_1603_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_dAssignment_1589_);
lean_inc(v_eAssignment_1588_);
lean_inc(v_lAssignment_1587_);
lean_inc(v_userNames_1586_);
lean_inc(v_decls_1585_);
lean_inc(v_lDecls_1584_);
lean_inc(v_mvarCounter_1583_);
lean_inc(v_lmvarCounter_1582_);
lean_inc(v_levelAssignDepth_1581_);
lean_inc(v_depth_1580_);
lean_dec(v_mctx_1572_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1603_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8___redArg(v_eAssignment_1588_, v_mvarId_1567_, v_val_1568_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 8, v___x_1593_);
v___x_1595_ = v___x_1591_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_depth_1580_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_levelAssignDepth_1581_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_lmvarCounter_1582_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_mvarCounter_1583_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_lDecls_1584_);
lean_ctor_set(v_reuseFailAlloc_1602_, 5, v_decls_1585_);
lean_ctor_set(v_reuseFailAlloc_1602_, 6, v_userNames_1586_);
lean_ctor_set(v_reuseFailAlloc_1602_, 7, v_lAssignment_1587_);
lean_ctor_set(v_reuseFailAlloc_1602_, 8, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1602_, 9, v_dAssignment_1589_);
v___x_1595_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1595_);
v___x_1597_ = v___x_1578_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_cache_1573_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_zetaDeltaFVarIds_1574_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_postponed_1575_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_diag_1576_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = lean_st_ref_set(v___y_1569_, v___x_1597_);
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object* v_mvarId_1605_, lean_object* v_val_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_mvarId_1605_, v_val_1606_, v___y_1607_);
lean_dec(v___y_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(lean_object* v_cls_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_options_1616_; uint8_t v_hasTrace_1617_; 
v_options_1616_ = lean_ctor_get(v___y_1613_, 2);
v_hasTrace_1617_ = lean_ctor_get_uint8(v_options_1616_, sizeof(void*)*1);
if (v_hasTrace_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v_cls_1610_);
v___x_1618_ = lean_box(v_hasTrace_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
else
{
lean_object* v_inheritedTraceOptions_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_inheritedTraceOptions_1620_ = lean_ctor_get(v___y_1613_, 13);
v___x_1621_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
v___x_1622_ = l_Lean_Name_append(v___x_1621_, v_cls_1610_);
v___x_1623_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1620_, v_options_1616_, v___x_1622_);
lean_dec(v___x_1622_);
v___x_1624_ = lean_box(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0___boxed(lean_object* v_cls_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(lean_object* v_a_1633_, lean_object* v___x_1634_, uint8_t v___x_1635_, lean_object* v___x_1636_, lean_object* v___f_1637_, lean_object* v_____r_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Lean_Meta_mkAuxTheorem(v_a_1633_, v___x_1634_, v___x_1635_, v___x_1644_, v___x_1635_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1636_, v_a_1646_, v___y_1640_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref(v___x_1647_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
v___x_1649_ = lean_apply_6(v___f_1637_, v_a_1648_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, lean_box(0));
return v___x_1649_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v___f_1637_);
v_a_1650_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1647_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1647_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v___f_1637_);
lean_dec(v___x_1636_);
v_a_1658_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1645_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1645_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7___boxed(lean_object* v_a_1666_, lean_object* v___x_1667_, lean_object* v___x_1668_, lean_object* v___x_1669_, lean_object* v___f_1670_, lean_object* v_____r_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v___x_160501__boxed_1677_; lean_object* v_res_1678_; 
v___x_160501__boxed_1677_ = lean_unbox(v___x_1668_);
v_res_1678_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_1666_, v___x_1667_, v___x_160501__boxed_1677_, v___x_1669_, v___f_1670_, v_____r_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(lean_object* v_snd_1679_, lean_object* v_a_1680_, lean_object* v___x_1681_, lean_object* v_____r_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_fieldName_1688_; lean_object* v___x_1689_; 
v_fieldName_1688_ = lean_ctor_get(v_snd_1679_, 0);
lean_inc(v_fieldName_1688_);
lean_dec_ref(v_snd_1679_);
v___x_1689_ = l_Lean_Meta_mkProjection(v_a_1680_, v_fieldName_1688_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1689_);
v___x_1691_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1681_, v_a_1690_, v___y_1684_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v___x_1691_, 0);
lean_dec(v_unused_1700_);
v___x_1693_ = v___x_1691_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_dec(v___x_1691_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_box(0);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_a_1701_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1691_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1691_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v___x_1681_);
v_a_1709_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1689_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1689_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2___boxed(lean_object* v_snd_1717_, lean_object* v_a_1718_, lean_object* v___x_1719_, lean_object* v_____r_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(v_snd_1717_, v_a_1718_, v___x_1719_, v_____r_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1726_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__0));
v___x_1729_ = l_Lean_stringToMessageData(v___x_1728_);
return v___x_1729_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__2));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__4));
v___x_1735_ = l_Lean_stringToMessageData(v___x_1734_);
return v___x_1735_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__6));
v___x_1738_ = l_Lean_stringToMessageData(v___x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5(lean_object* v_val_1739_, lean_object* v_fst_1740_, lean_object* v_expectedType_1741_, lean_object* v___f_1742_, lean_object* v___f_1743_, lean_object* v___x_1744_, lean_object* v_cls_1745_, lean_object* v_snd_1746_, lean_object* v___x_1747_, lean_object* v_____r_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___y_1755_; uint8_t v___y_1756_; lean_object* v_a_1789_; lean_object* v___y_1793_; lean_object* v___x_1806_; 
v___x_1806_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_val_1739_, v_fst_1740_, v_expectedType_1741_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref(v___x_1806_);
if (lean_obj_tag(v_a_1807_) == 1)
{
lean_object* v_val_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_val_1808_ = lean_ctor_get(v_a_1807_, 0);
lean_inc(v_val_1808_);
lean_dec_ref(v_a_1807_);
v___x_1809_ = lean_box(0);
v___x_1810_ = l_Lean_Meta_trySynthInstance(v_val_1808_, v___x_1809_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref(v___x_1810_);
if (lean_obj_tag(v_a_1811_) == 1)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; 
v_a_1812_ = lean_ctor_get(v_a_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_inc_ref(v___f_1742_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1813_ = lean_apply_5(v___f_1742_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; uint8_t v___x_1815_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = lean_unbox(v_a_1814_);
lean_dec(v_a_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(v_snd_1746_, v_a_1812_, v___x_1747_, v___x_1744_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
v___y_1793_ = v___x_1816_;
goto v___jp_1792_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1817_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5);
lean_inc(v_a_1812_);
v___x_1818_ = l_Lean_MessageData_ofExpr(v_a_1812_);
v___x_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
lean_inc(v_cls_1745_);
v___x_1822_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1745_, v___x_1821_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(v_snd_1746_, v_a_1812_, v___x_1747_, v_a_1823_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
v___y_1793_ = v___x_1824_;
goto v___jp_1792_;
}
else
{
lean_object* v_a_1825_; 
lean_dec(v_a_1812_);
lean_dec(v___x_1747_);
lean_dec_ref(v_snd_1746_);
v_a_1825_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1822_);
v_a_1789_ = v_a_1825_;
goto v___jp_1788_;
}
}
}
else
{
lean_object* v_a_1826_; 
lean_dec(v_a_1812_);
lean_dec(v___x_1747_);
lean_dec_ref(v_snd_1746_);
v_a_1826_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1826_);
lean_dec_ref(v___x_1813_);
v_a_1789_ = v_a_1826_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_options_1827_; uint8_t v_hasTrace_1828_; 
lean_dec(v_a_1811_);
lean_dec(v___x_1747_);
lean_dec_ref(v_snd_1746_);
v_options_1827_ = lean_ctor_get(v___y_1751_, 2);
v_hasTrace_1828_ = lean_ctor_get_uint8(v_options_1827_, sizeof(void*)*1);
if (v_hasTrace_1828_ == 0)
{
lean_object* v___x_1829_; 
lean_dec(v_cls_1745_);
lean_dec_ref(v___f_1742_);
lean_dec(v_fst_1740_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1829_ = lean_apply_6(v___f_1743_, v___x_1744_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
return v___x_1829_;
}
else
{
lean_object* v_inheritedTraceOptions_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_inheritedTraceOptions_1830_ = lean_ctor_get(v___y_1751_, 13);
v___x_1831_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
lean_inc(v_cls_1745_);
v___x_1832_ = l_Lean_Name_append(v___x_1831_, v_cls_1745_);
v___x_1833_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1830_, v_options_1827_, v___x_1832_);
lean_dec(v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec(v_cls_1745_);
lean_dec_ref(v___f_1742_);
lean_dec(v_fst_1740_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1834_ = lean_apply_6(v___f_1743_, v___x_1744_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
return v___x_1834_;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1835_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7);
lean_inc(v_fst_1740_);
v___x_1836_ = l_Lean_MessageData_ofName(v_fst_1740_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
lean_inc(v_cls_1745_);
v___x_1840_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1745_, v___x_1839_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; 
lean_dec(v_cls_1745_);
lean_dec_ref(v___f_1742_);
lean_dec(v_fst_1740_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1840_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1842_ = lean_apply_6(v___f_1743_, v_a_1841_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
return v___x_1842_;
}
else
{
lean_object* v_a_1843_; 
v_a_1843_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1843_);
lean_dec_ref(v___x_1840_);
v_a_1789_ = v_a_1843_;
goto v___jp_1788_;
}
}
}
}
}
else
{
lean_object* v_a_1844_; 
lean_dec(v___x_1747_);
lean_dec_ref(v_snd_1746_);
v_a_1844_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1810_);
v_a_1789_ = v_a_1844_;
goto v___jp_1788_;
}
}
else
{
lean_object* v___x_1845_; 
lean_dec(v_a_1807_);
lean_dec(v___x_1747_);
lean_dec_ref(v_snd_1746_);
lean_dec(v_cls_1745_);
lean_dec_ref(v___f_1742_);
lean_dec(v_fst_1740_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1845_ = lean_apply_6(v___f_1743_, v___x_1744_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
return v___x_1845_;
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v___x_1747_);
lean_dec_ref(v_snd_1746_);
lean_dec(v_cls_1745_);
lean_dec_ref(v___f_1743_);
lean_dec_ref(v___f_1742_);
lean_dec(v_fst_1740_);
v_a_1846_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1806_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1806_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
v___jp_1754_:
{
if (v___y_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1757_ = lean_apply_5(v___f_1742_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; uint8_t v___x_1759_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = lean_unbox(v_a_1758_);
lean_dec(v_a_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_dec_ref(v___y_1755_);
lean_dec(v_cls_1745_);
lean_dec(v_fst_1740_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1760_ = lean_apply_6(v___f_1743_, v___x_1744_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1761_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1);
v___x_1762_ = l_Lean_MessageData_ofName(v_fst_1740_);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_Exception_toMessageData(v___y_1755_);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1745_, v___x_1767_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1770_ = lean_apply_6(v___f_1743_, v_a_1769_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
return v___x_1770_;
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v___f_1743_);
v_a_1771_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1768_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1768_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___y_1755_);
lean_dec(v_cls_1745_);
lean_dec_ref(v___f_1743_);
lean_dec(v_fst_1740_);
v_a_1779_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1757_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1757_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v___x_1787_; 
lean_dec(v_cls_1745_);
lean_dec_ref(v___f_1743_);
lean_dec_ref(v___f_1742_);
lean_dec(v_fst_1740_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___y_1755_);
return v___x_1787_;
}
}
v___jp_1788_:
{
uint8_t v___x_1790_; 
v___x_1790_ = l_Lean_Exception_isInterrupt(v_a_1789_);
if (v___x_1790_ == 0)
{
uint8_t v___x_1791_; 
lean_inc_ref(v_a_1789_);
v___x_1791_ = l_Lean_Exception_isRuntime(v_a_1789_);
v___y_1755_ = v_a_1789_;
v___y_1756_ = v___x_1791_;
goto v___jp_1754_;
}
else
{
v___y_1755_ = v_a_1789_;
v___y_1756_ = v___x_1790_;
goto v___jp_1754_;
}
}
v___jp_1792_:
{
if (lean_obj_tag(v___y_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_cls_1745_);
lean_dec_ref(v___f_1742_);
lean_dec(v_fst_1740_);
v_a_1794_ = lean_ctor_get(v___y_1793_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___y_1793_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1796_ = v___y_1793_;
v_isShared_1797_ = v_isSharedCheck_1804_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___y_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1804_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
if (lean_obj_tag(v_a_1794_) == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
lean_dec_ref(v___f_1743_);
v___x_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1744_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1798_);
v___x_1800_ = v___x_1796_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1803_; 
lean_del_object(v___x_1796_);
v_a_1802_ = lean_ctor_get(v_a_1794_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v_a_1794_);
lean_inc(v___y_1752_);
lean_inc_ref(v___y_1751_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1749_);
v___x_1803_ = lean_apply_6(v___f_1743_, v_a_1802_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
return v___x_1803_;
}
}
}
else
{
lean_object* v_a_1805_; 
v_a_1805_ = lean_ctor_get(v___y_1793_, 0);
lean_inc(v_a_1805_);
lean_dec_ref(v___y_1793_);
v_a_1789_ = v_a_1805_;
goto v___jp_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___boxed(lean_object* v_val_1854_, lean_object* v_fst_1855_, lean_object* v_expectedType_1856_, lean_object* v___f_1857_, lean_object* v___f_1858_, lean_object* v___x_1859_, lean_object* v_cls_1860_, lean_object* v_snd_1861_, lean_object* v___x_1862_, lean_object* v_____r_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5(v_val_1854_, v_fst_1855_, v_expectedType_1856_, v___f_1857_, v___f_1858_, v___x_1859_, v_cls_1860_, v_snd_1861_, v___x_1862_, v_____r_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(lean_object* v___x_1870_, lean_object* v_____r_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1870_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6___boxed(lean_object* v___x_1879_, lean_object* v_____r_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_1879_, v_____r_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(lean_object* v___x_1890_, lean_object* v___x_1891_, lean_object* v___x_1892_, lean_object* v_a_1893_, uint8_t v___x_1894_, uint8_t v___x_1895_, uint8_t v_compile_1896_, uint8_t v_logCompileErrors_1897_, uint8_t v_isMeta_1898_, lean_object* v_____r_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v_options_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v_options_1905_ = lean_ctor_get(v___y_1902_, 2);
v___x_1906_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_1907_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_1905_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
lean_dec_ref(v_a_1893_);
v___x_1908_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1890_, v___x_1891_, v___y_1901_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1916_; 
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v___x_1908_, 0);
lean_dec(v_unused_1917_);
v___x_1910_ = v___x_1908_;
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
else
{
lean_dec(v___x_1908_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1916_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1892_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_a_1918_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1908_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1908_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
else
{
lean_object* v___x_1926_; 
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1900_);
lean_inc_ref(v___x_1891_);
v___x_1926_ = lean_infer_type(v___x_1891_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref(v___x_1926_);
lean_inc_ref(v_a_1893_);
v___x_1928_ = l_Lean_Meta_isExprDefEq(v_a_1893_, v_a_1927_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; uint8_t v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = lean_unbox(v_a_1929_);
lean_dec(v_a_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_1932_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_1931_, v___y_1903_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___x_1970_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc_n(v_a_1933_, 2);
lean_dec_ref(v___x_1932_);
v___x_1970_ = l_Lean_Meta_mkAuxDefinition(v_a_1933_, v_a_1893_, v___x_1891_, v___x_1894_, v___x_1894_, v___x_1895_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1970_);
v___x_1972_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1890_, v_a_1971_, v___y_1901_);
if (lean_obj_tag(v___x_1972_) == 0)
{
uint8_t v___x_1973_; lean_object* v___x_1974_; 
lean_dec_ref(v___x_1972_);
v___x_1973_ = 0;
lean_inc(v_a_1933_);
v___x_1974_ = l_Lean_Meta_setInlineAttribute(v_a_1933_, v___x_1973_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_dec_ref(v___x_1974_);
if (v_isMeta_1898_ == 0)
{
v___y_1956_ = v___y_1902_;
v___y_1957_ = v___y_1903_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1975_; lean_object* v_env_1976_; lean_object* v_nextMacroScope_1977_; lean_object* v_ngen_1978_; lean_object* v_auxDeclNGen_1979_; lean_object* v_traceState_1980_; lean_object* v_messages_1981_; lean_object* v_infoState_1982_; lean_object* v_snapshotTasks_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2008_; 
v___x_1975_ = lean_st_ref_take(v___y_1903_);
v_env_1976_ = lean_ctor_get(v___x_1975_, 0);
v_nextMacroScope_1977_ = lean_ctor_get(v___x_1975_, 1);
v_ngen_1978_ = lean_ctor_get(v___x_1975_, 2);
v_auxDeclNGen_1979_ = lean_ctor_get(v___x_1975_, 3);
v_traceState_1980_ = lean_ctor_get(v___x_1975_, 4);
v_messages_1981_ = lean_ctor_get(v___x_1975_, 6);
v_infoState_1982_ = lean_ctor_get(v___x_1975_, 7);
v_snapshotTasks_1983_ = lean_ctor_get(v___x_1975_, 8);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_1975_, 5);
lean_dec(v_unused_2009_);
v___x_1985_ = v___x_1975_;
v_isShared_1986_ = v_isSharedCheck_2008_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snapshotTasks_1983_);
lean_inc(v_infoState_1982_);
lean_inc(v_messages_1981_);
lean_inc(v_traceState_1980_);
lean_inc(v_auxDeclNGen_1979_);
lean_inc(v_ngen_1978_);
lean_inc(v_nextMacroScope_1977_);
lean_inc(v_env_1976_);
lean_dec(v___x_1975_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2008_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_inc(v_a_1933_);
v___x_1987_ = l_Lean_markMeta(v_env_1976_, v_a_1933_);
v___x_1988_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 5, v___x_1988_);
lean_ctor_set(v___x_1985_, 0, v___x_1987_);
v___x_1990_ = v___x_1985_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_nextMacroScope_1977_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_ngen_1978_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_auxDeclNGen_1979_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_traceState_1980_);
lean_ctor_set(v_reuseFailAlloc_2007_, 5, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_2007_, 6, v_messages_1981_);
lean_ctor_set(v_reuseFailAlloc_2007_, 7, v_infoState_1982_);
lean_ctor_set(v_reuseFailAlloc_2007_, 8, v_snapshotTasks_1983_);
v___x_1990_ = v_reuseFailAlloc_2007_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v_mctx_1993_; lean_object* v_zetaDeltaFVarIds_1994_; lean_object* v_postponed_1995_; lean_object* v_diag_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2005_; 
v___x_1991_ = lean_st_ref_set(v___y_1903_, v___x_1990_);
v___x_1992_ = lean_st_ref_take(v___y_1901_);
v_mctx_1993_ = lean_ctor_get(v___x_1992_, 0);
v_zetaDeltaFVarIds_1994_ = lean_ctor_get(v___x_1992_, 2);
v_postponed_1995_ = lean_ctor_get(v___x_1992_, 3);
v_diag_1996_ = lean_ctor_get(v___x_1992_, 4);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1992_, 1);
lean_dec(v_unused_2006_);
v___x_1998_ = v___x_1992_;
v_isShared_1999_ = v_isSharedCheck_2005_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_diag_1996_);
lean_inc(v_postponed_1995_);
lean_inc(v_zetaDeltaFVarIds_1994_);
lean_inc(v_mctx_1993_);
lean_dec(v___x_1992_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2005_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 1, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_mctx_1993_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_zetaDeltaFVarIds_1994_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_postponed_1995_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v_diag_1996_);
v___x_2002_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_st_ref_set(v___y_1901_, v___x_2002_);
v___y_1956_ = v___y_1902_;
v___y_1957_ = v___y_1903_;
goto v___jp_1955_;
}
}
}
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v_a_1933_);
v_a_2010_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1974_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1974_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_a_1933_);
v_a_2018_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1972_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1972_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_a_1933_);
lean_dec(v___x_1890_);
v_a_2026_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1970_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1970_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
v___jp_1934_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_enableRealizationsForConst(v_a_1933_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1945_; 
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1937_, 0);
lean_dec(v_unused_1946_);
v___x_1939_ = v___x_1937_;
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v___x_1937_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1892_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1937_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1937_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
v___jp_1955_:
{
if (v_compile_1896_ == 0)
{
v___y_1935_ = v___y_1956_;
v___y_1936_ = v___y_1957_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1958_ = lean_unsigned_to_nat(1u);
v___x_1959_ = lean_mk_empty_array_with_capacity(v___x_1958_);
lean_inc(v_a_1933_);
v___x_1960_ = lean_array_push(v___x_1959_, v_a_1933_);
v___x_1961_ = l_Lean_compileDecls(v___x_1960_, v_logCompileErrors_1897_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec_ref(v___x_1961_);
v___y_1935_ = v___y_1956_;
v___y_1936_ = v___y_1957_;
goto v___jp_1934_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_a_1933_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_a_1893_);
lean_dec_ref(v___x_1891_);
lean_dec(v___x_1890_);
v_a_2034_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_1932_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_1932_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v___x_2042_; 
lean_dec_ref(v_a_1893_);
v___x_2042_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_1890_, v___x_1891_, v___y_1901_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2042_, 0);
lean_dec(v_unused_2051_);
v___x_2044_ = v___x_2042_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_dec(v___x_2042_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_1892_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
v_a_2052_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2042_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2042_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v_a_1893_);
lean_dec_ref(v___x_1891_);
lean_dec(v___x_1890_);
v_a_2060_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_1928_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_1928_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref(v_a_1893_);
lean_dec_ref(v___x_1891_);
lean_dec(v___x_1890_);
v_a_2068_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_1926_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_1926_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed(lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v___x_2078_, lean_object* v_a_2079_, lean_object* v___x_2080_, lean_object* v___x_2081_, lean_object* v_compile_2082_, lean_object* v_logCompileErrors_2083_, lean_object* v_isMeta_2084_, lean_object* v_____r_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v___x_160987__boxed_2091_; uint8_t v___x_160988__boxed_2092_; uint8_t v_compile_boxed_2093_; uint8_t v_logCompileErrors_boxed_2094_; uint8_t v_isMeta_boxed_2095_; lean_object* v_res_2096_; 
v___x_160987__boxed_2091_ = lean_unbox(v___x_2080_);
v___x_160988__boxed_2092_ = lean_unbox(v___x_2081_);
v_compile_boxed_2093_ = lean_unbox(v_compile_2082_);
v_logCompileErrors_boxed_2094_ = lean_unbox(v_logCompileErrors_2083_);
v_isMeta_boxed_2095_ = lean_unbox(v_isMeta_2084_);
v_res_2096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_2076_, v___x_2077_, v___x_2078_, v_a_2079_, v___x_160987__boxed_2091_, v___x_160988__boxed_2092_, v_compile_boxed_2093_, v_logCompileErrors_boxed_2094_, v_isMeta_boxed_2095_, v_____r_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(lean_object* v_val_2097_, lean_object* v_fst_2098_, lean_object* v_expectedType_2099_, lean_object* v___f_2100_, lean_object* v___f_2101_, lean_object* v___x_2102_, lean_object* v_cls_2103_, lean_object* v_snd_2104_, lean_object* v___x_2105_, lean_object* v_____r_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___y_2113_; uint8_t v___y_2114_; lean_object* v_a_2147_; lean_object* v___y_2151_; lean_object* v___x_2164_; 
v___x_2164_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f(v_val_2097_, v_fst_2098_, v_expectedType_2099_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
if (lean_obj_tag(v_a_2165_) == 1)
{
lean_object* v_val_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_val_2166_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_val_2166_);
lean_dec_ref(v_a_2165_);
v___x_2167_ = lean_box(0);
v___x_2168_ = l_Lean_Meta_trySynthInstance(v_val_2166_, v___x_2167_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2168_);
if (lean_obj_tag(v_a_2169_) == 1)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
v_a_2170_ = lean_ctor_get(v_a_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_inc_ref(v___f_2100_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2171_ = lean_apply_5(v___f_2100_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; uint8_t v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = lean_unbox(v_a_2172_);
lean_dec(v_a_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
v___x_2174_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(v_snd_2104_, v_a_2170_, v___x_2105_, v___x_2102_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
v___y_2151_ = v___x_2174_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2175_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__5);
lean_inc(v_a_2170_);
v___x_2176_ = l_Lean_MessageData_ofExpr(v_a_2170_);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
lean_inc(v_cls_2103_);
v___x_2180_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2103_, v___x_2179_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
v___x_2182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__2(v_snd_2104_, v_a_2170_, v___x_2105_, v_a_2181_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
v___y_2151_ = v___x_2182_;
goto v___jp_2150_;
}
else
{
lean_object* v_a_2183_; 
lean_dec(v_a_2170_);
lean_dec(v___x_2105_);
lean_dec_ref(v_snd_2104_);
v_a_2183_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2183_);
lean_dec_ref(v___x_2180_);
v_a_2147_ = v_a_2183_;
goto v___jp_2146_;
}
}
}
else
{
lean_object* v_a_2184_; 
lean_dec(v_a_2170_);
lean_dec(v___x_2105_);
lean_dec_ref(v_snd_2104_);
v_a_2184_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2184_);
lean_dec_ref(v___x_2171_);
v_a_2147_ = v_a_2184_;
goto v___jp_2146_;
}
}
else
{
lean_object* v_options_2185_; uint8_t v_hasTrace_2186_; 
lean_dec(v_a_2169_);
lean_dec(v___x_2105_);
lean_dec_ref(v_snd_2104_);
v_options_2185_ = lean_ctor_get(v___y_2109_, 2);
v_hasTrace_2186_ = lean_ctor_get_uint8(v_options_2185_, sizeof(void*)*1);
if (v_hasTrace_2186_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v_cls_2103_);
lean_dec_ref(v___f_2100_);
lean_dec(v_fst_2098_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2187_ = lean_apply_6(v___f_2101_, v___x_2102_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
return v___x_2187_;
}
else
{
lean_object* v_inheritedTraceOptions_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_inheritedTraceOptions_2188_ = lean_ctor_get(v___y_2109_, 13);
v___x_2189_ = ((lean_object*)(l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__2));
lean_inc(v_cls_2103_);
v___x_2190_ = l_Lean_Name_append(v___x_2189_, v_cls_2103_);
v___x_2191_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2188_, v_options_2185_, v___x_2190_);
lean_dec(v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
lean_dec(v_cls_2103_);
lean_dec_ref(v___f_2100_);
lean_dec(v_fst_2098_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2192_ = lean_apply_6(v___f_2101_, v___x_2102_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2193_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__7);
lean_inc(v_fst_2098_);
v___x_2194_ = l_Lean_MessageData_ofName(v_fst_2098_);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2193_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
lean_inc(v_cls_2103_);
v___x_2198_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2103_, v___x_2197_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
lean_dec(v_cls_2103_);
lean_dec_ref(v___f_2100_);
lean_dec(v_fst_2098_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2200_ = lean_apply_6(v___f_2101_, v_a_2199_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
return v___x_2200_;
}
else
{
lean_object* v_a_2201_; 
v_a_2201_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2198_);
v_a_2147_ = v_a_2201_;
goto v___jp_2146_;
}
}
}
}
}
else
{
lean_object* v_a_2202_; 
lean_dec(v___x_2105_);
lean_dec_ref(v_snd_2104_);
v_a_2202_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2168_);
v_a_2147_ = v_a_2202_;
goto v___jp_2146_;
}
}
else
{
lean_object* v___x_2203_; 
lean_dec(v_a_2165_);
lean_dec(v___x_2105_);
lean_dec_ref(v_snd_2104_);
lean_dec(v_cls_2103_);
lean_dec_ref(v___f_2100_);
lean_dec(v_fst_2098_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2203_ = lean_apply_6(v___f_2101_, v___x_2102_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
return v___x_2203_;
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v___x_2105_);
lean_dec_ref(v_snd_2104_);
lean_dec(v_cls_2103_);
lean_dec_ref(v___f_2101_);
lean_dec_ref(v___f_2100_);
lean_dec(v_fst_2098_);
v_a_2204_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2164_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2164_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
v___jp_2112_:
{
if (v___y_2114_ == 0)
{
lean_object* v___x_2115_; 
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2115_ = lean_apply_5(v___f_2100_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; uint8_t v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = lean_unbox(v_a_2116_);
lean_dec(v_a_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref(v___y_2113_);
lean_dec(v_cls_2103_);
lean_dec(v_fst_2098_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2118_ = lean_apply_6(v___f_2101_, v___x_2102_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2119_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__1);
v___x_2120_ = l_Lean_MessageData_ofName(v_fst_2098_);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2121_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = l_Lean_Exception_toMessageData(v___y_2113_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2103_, v___x_2125_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2128_ = lean_apply_6(v___f_2101_, v_a_2127_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
return v___x_2128_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v___f_2101_);
v_a_2129_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2126_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2126_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v___y_2113_);
lean_dec(v_cls_2103_);
lean_dec_ref(v___f_2101_);
lean_dec(v_fst_2098_);
v_a_2137_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2115_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2115_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v___x_2145_; 
lean_dec(v_cls_2103_);
lean_dec_ref(v___f_2101_);
lean_dec_ref(v___f_2100_);
lean_dec(v_fst_2098_);
v___x_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___y_2113_);
return v___x_2145_;
}
}
v___jp_2146_:
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Lean_Exception_isInterrupt(v_a_2147_);
if (v___x_2148_ == 0)
{
uint8_t v___x_2149_; 
lean_inc_ref(v_a_2147_);
v___x_2149_ = l_Lean_Exception_isRuntime(v_a_2147_);
v___y_2113_ = v_a_2147_;
v___y_2114_ = v___x_2149_;
goto v___jp_2112_;
}
else
{
v___y_2113_ = v_a_2147_;
v___y_2114_ = v___x_2148_;
goto v___jp_2112_;
}
}
v___jp_2150_:
{
if (lean_obj_tag(v___y_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_cls_2103_);
lean_dec_ref(v___f_2100_);
lean_dec(v_fst_2098_);
v_a_2152_ = lean_ctor_get(v___y_2151_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___y_2151_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2154_ = v___y_2151_;
v_isShared_2155_ = v_isSharedCheck_2162_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___y_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2162_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
if (lean_obj_tag(v_a_2152_) == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_dec_ref(v___f_2101_);
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2102_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2161_; 
lean_del_object(v___x_2154_);
v_a_2160_ = lean_ctor_get(v_a_2152_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v_a_2152_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
v___x_2161_ = lean_apply_6(v___f_2101_, v_a_2160_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, lean_box(0));
return v___x_2161_;
}
}
}
else
{
lean_object* v_a_2163_; 
v_a_2163_ = lean_ctor_get(v___y_2151_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___y_2151_);
v_a_2147_ = v_a_2163_;
goto v___jp_2146_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3___boxed(lean_object* v_val_2212_, lean_object* v_fst_2213_, lean_object* v_expectedType_2214_, lean_object* v___f_2215_, lean_object* v___f_2216_, lean_object* v___x_2217_, lean_object* v_cls_2218_, lean_object* v_snd_2219_, lean_object* v___x_2220_, lean_object* v_____r_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_2212_, v_fst_2213_, v_expectedType_2214_, v___f_2215_, v___f_2216_, v___x_2217_, v_cls_2218_, v_snd_2219_, v___x_2220_, v_____r_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(lean_object* v___x_2228_, lean_object* v___x_2229_, lean_object* v___x_2230_, lean_object* v_a_2231_, uint8_t v___x_2232_, uint8_t v_compile_2233_, uint8_t v_logCompileErrors_2234_, uint8_t v_isMeta_2235_, lean_object* v_____r_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_options_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_options_2242_ = lean_ctor_get(v___y_2239_, 2);
v___x_2243_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2244_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2242_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; 
lean_dec_ref(v_a_2231_);
v___x_2245_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2228_, v___x_2229_, v___y_2238_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2253_; 
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v___x_2245_, 0);
lean_dec(v_unused_2254_);
v___x_2247_ = v___x_2245_;
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
else
{
lean_dec(v___x_2245_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2230_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
v_a_2255_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2245_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2245_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v___x_2263_; 
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
lean_inc_ref(v___x_2229_);
v___x_2263_ = lean_infer_type(v___x_2229_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
lean_inc_ref(v_a_2231_);
v___x_2265_ = l_Lean_Meta_isExprDefEq(v_a_2231_, v_a_2264_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; uint8_t v___x_2267_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = lean_unbox(v_a_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_2269_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2268_, v___y_2240_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2293_; lean_object* v___y_2294_; uint8_t v___x_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc_n(v_a_2270_, 2);
lean_dec_ref(v___x_2269_);
v___x_2307_ = lean_unbox(v_a_2266_);
v___x_2308_ = lean_unbox(v_a_2266_);
lean_dec(v_a_2266_);
v___x_2309_ = l_Lean_Meta_mkAuxDefinition(v_a_2270_, v_a_2231_, v___x_2229_, v___x_2307_, v___x_2308_, v___x_2232_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2228_, v_a_2310_, v___y_2238_);
if (lean_obj_tag(v___x_2311_) == 0)
{
uint8_t v___x_2312_; lean_object* v___x_2313_; 
lean_dec_ref(v___x_2311_);
v___x_2312_ = 0;
lean_inc(v_a_2270_);
v___x_2313_ = l_Lean_Meta_setInlineAttribute(v_a_2270_, v___x_2312_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_dec_ref(v___x_2313_);
if (v_isMeta_2235_ == 0)
{
v___y_2293_ = v___y_2239_;
v___y_2294_ = v___y_2240_;
goto v___jp_2292_;
}
else
{
lean_object* v___x_2314_; lean_object* v_env_2315_; lean_object* v_nextMacroScope_2316_; lean_object* v_ngen_2317_; lean_object* v_auxDeclNGen_2318_; lean_object* v_traceState_2319_; lean_object* v_messages_2320_; lean_object* v_infoState_2321_; lean_object* v_snapshotTasks_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2347_; 
v___x_2314_ = lean_st_ref_take(v___y_2240_);
v_env_2315_ = lean_ctor_get(v___x_2314_, 0);
v_nextMacroScope_2316_ = lean_ctor_get(v___x_2314_, 1);
v_ngen_2317_ = lean_ctor_get(v___x_2314_, 2);
v_auxDeclNGen_2318_ = lean_ctor_get(v___x_2314_, 3);
v_traceState_2319_ = lean_ctor_get(v___x_2314_, 4);
v_messages_2320_ = lean_ctor_get(v___x_2314_, 6);
v_infoState_2321_ = lean_ctor_get(v___x_2314_, 7);
v_snapshotTasks_2322_ = lean_ctor_get(v___x_2314_, 8);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2314_, 5);
lean_dec(v_unused_2348_);
v___x_2324_ = v___x_2314_;
v_isShared_2325_ = v_isSharedCheck_2347_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snapshotTasks_2322_);
lean_inc(v_infoState_2321_);
lean_inc(v_messages_2320_);
lean_inc(v_traceState_2319_);
lean_inc(v_auxDeclNGen_2318_);
lean_inc(v_ngen_2317_);
lean_inc(v_nextMacroScope_2316_);
lean_inc(v_env_2315_);
lean_dec(v___x_2314_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2347_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_inc(v_a_2270_);
v___x_2326_ = l_Lean_markMeta(v_env_2315_, v_a_2270_);
v___x_2327_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 5, v___x_2327_);
lean_ctor_set(v___x_2324_, 0, v___x_2326_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_nextMacroScope_2316_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_ngen_2317_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_auxDeclNGen_2318_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_traceState_2319_);
lean_ctor_set(v_reuseFailAlloc_2346_, 5, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2346_, 6, v_messages_2320_);
lean_ctor_set(v_reuseFailAlloc_2346_, 7, v_infoState_2321_);
lean_ctor_set(v_reuseFailAlloc_2346_, 8, v_snapshotTasks_2322_);
v___x_2329_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v_mctx_2332_; lean_object* v_zetaDeltaFVarIds_2333_; lean_object* v_postponed_2334_; lean_object* v_diag_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2344_; 
v___x_2330_ = lean_st_ref_set(v___y_2240_, v___x_2329_);
v___x_2331_ = lean_st_ref_take(v___y_2238_);
v_mctx_2332_ = lean_ctor_get(v___x_2331_, 0);
v_zetaDeltaFVarIds_2333_ = lean_ctor_get(v___x_2331_, 2);
v_postponed_2334_ = lean_ctor_get(v___x_2331_, 3);
v_diag_2335_ = lean_ctor_get(v___x_2331_, 4);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v___x_2331_, 1);
lean_dec(v_unused_2345_);
v___x_2337_ = v___x_2331_;
v_isShared_2338_ = v_isSharedCheck_2344_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_diag_2335_);
lean_inc(v_postponed_2334_);
lean_inc(v_zetaDeltaFVarIds_2333_);
lean_inc(v_mctx_2332_);
lean_dec(v___x_2331_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2344_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2339_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___x_2339_);
v___x_2341_ = v___x_2337_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_mctx_2332_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_zetaDeltaFVarIds_2333_);
lean_ctor_set(v_reuseFailAlloc_2343_, 3, v_postponed_2334_);
lean_ctor_set(v_reuseFailAlloc_2343_, 4, v_diag_2335_);
v___x_2341_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_st_ref_set(v___y_2238_, v___x_2341_);
v___y_2293_ = v___y_2239_;
v___y_2294_ = v___y_2240_;
goto v___jp_2292_;
}
}
}
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2270_);
v_a_2349_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2313_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2313_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2270_);
v_a_2357_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2311_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2311_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_a_2270_);
lean_dec(v___x_2228_);
v_a_2365_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2309_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2309_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
v___jp_2271_:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_enableRealizationsForConst(v_a_2270_, v___y_2272_, v___y_2273_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v___x_2274_, 0);
lean_dec(v_unused_2283_);
v___x_2276_ = v___x_2274_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_dec(v___x_2274_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2230_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
v_a_2284_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2274_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2274_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
v___jp_2292_:
{
if (v_compile_2233_ == 0)
{
v___y_2272_ = v___y_2293_;
v___y_2273_ = v___y_2294_;
goto v___jp_2271_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2296_ = lean_mk_empty_array_with_capacity(v___x_2295_);
lean_inc(v_a_2270_);
v___x_2297_ = lean_array_push(v___x_2296_, v_a_2270_);
v___x_2298_ = l_Lean_compileDecls(v___x_2297_, v_logCompileErrors_2234_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_dec_ref(v___x_2298_);
v___y_2272_ = v___y_2293_;
v___y_2273_ = v___y_2294_;
goto v___jp_2271_;
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_a_2270_);
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2231_);
lean_dec_ref(v___x_2229_);
lean_dec(v___x_2228_);
v_a_2373_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2269_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2269_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v___x_2381_; 
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2231_);
v___x_2381_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2228_, v___x_2229_, v___y_2238_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2389_; 
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2381_, 0);
lean_dec(v_unused_2390_);
v___x_2383_ = v___x_2381_;
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
else
{
lean_dec(v___x_2381_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2230_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2385_);
v___x_2387_ = v___x_2383_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v_a_2391_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2381_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2381_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v_a_2231_);
lean_dec_ref(v___x_2229_);
lean_dec(v___x_2228_);
v_a_2399_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2265_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2265_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v_a_2231_);
lean_dec_ref(v___x_2229_);
lean_dec(v___x_2228_);
v_a_2407_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2263_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2263_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1___boxed(lean_object* v___x_2415_, lean_object* v___x_2416_, lean_object* v___x_2417_, lean_object* v_a_2418_, lean_object* v___x_2419_, lean_object* v_compile_2420_, lean_object* v_logCompileErrors_2421_, lean_object* v_isMeta_2422_, lean_object* v_____r_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
uint8_t v___x_161625__boxed_2429_; uint8_t v_compile_boxed_2430_; uint8_t v_logCompileErrors_boxed_2431_; uint8_t v_isMeta_boxed_2432_; lean_object* v_res_2433_; 
v___x_161625__boxed_2429_ = lean_unbox(v___x_2419_);
v_compile_boxed_2430_ = lean_unbox(v_compile_2420_);
v_logCompileErrors_boxed_2431_ = lean_unbox(v_logCompileErrors_2421_);
v_isMeta_boxed_2432_ = lean_unbox(v_isMeta_2422_);
v_res_2433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(v___x_2415_, v___x_2416_, v___x_2417_, v_a_2418_, v___x_161625__boxed_2429_, v_compile_boxed_2430_, v_logCompileErrors_boxed_2431_, v_isMeta_boxed_2432_, v_____r_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(lean_object* v___x_2434_, lean_object* v_a_2435_, lean_object* v_____r_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2434_, v_a_2435_, v___y_2438_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2450_; 
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v___x_2442_, 0);
lean_dec(v_unused_2451_);
v___x_2444_ = v___x_2442_;
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
else
{
lean_dec(v___x_2442_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2450_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_box(0);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2446_);
v___x_2448_ = v___x_2444_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2442_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2442_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5___boxed(lean_object* v___x_2460_, lean_object* v_a_2461_, lean_object* v_____r_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_2460_, v_a_2461_, v_____r_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(lean_object* v_opts_2469_, lean_object* v_opt_2470_){
_start:
{
lean_object* v_name_2471_; lean_object* v_defValue_2472_; lean_object* v_map_2473_; lean_object* v___x_2474_; 
v_name_2471_ = lean_ctor_get(v_opt_2470_, 0);
v_defValue_2472_ = lean_ctor_get(v_opt_2470_, 1);
v_map_2473_ = lean_ctor_get(v_opts_2469_, 0);
v___x_2474_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2473_, v_name_2471_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_inc(v_defValue_2472_);
return v_defValue_2472_;
}
else
{
lean_object* v_val_2475_; 
v_val_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_val_2475_);
lean_dec_ref(v___x_2474_);
if (lean_obj_tag(v_val_2475_) == 3)
{
lean_object* v_v_2476_; 
v_v_2476_ = lean_ctor_get(v_val_2475_, 0);
lean_inc(v_v_2476_);
lean_dec_ref(v_val_2475_);
return v_v_2476_;
}
else
{
lean_dec(v_val_2475_);
lean_inc(v_defValue_2472_);
return v_defValue_2472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18___boxed(lean_object* v_opts_2477_, lean_object* v_opt_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(v_opts_2477_, v_opt_2478_);
lean_dec_ref(v_opt_2478_);
lean_dec_ref(v_opts_2477_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(lean_object* v_x_2480_){
_start:
{
if (lean_obj_tag(v_x_2480_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_a_2482_ = lean_ctor_get(v_x_2480_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_x_2480_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v_x_2480_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v_x_2480_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set_tag(v___x_2484_, 1);
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_a_2490_ = lean_ctor_get(v_x_2480_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_x_2480_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v_x_2480_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v_x_2480_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 0);
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg___boxed(lean_object* v_x_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(v_x_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19(size_t v_sz_2501_, size_t v_i_2502_, lean_object* v_bs_2503_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_usize_dec_lt(v_i_2502_, v_sz_2501_);
if (v___x_2504_ == 0)
{
return v_bs_2503_;
}
else
{
lean_object* v_v_2505_; lean_object* v_msg_2506_; lean_object* v___x_2507_; lean_object* v_bs_x27_2508_; size_t v___x_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
v_v_2505_ = lean_array_uget_borrowed(v_bs_2503_, v_i_2502_);
v_msg_2506_ = lean_ctor_get(v_v_2505_, 1);
lean_inc_ref(v_msg_2506_);
v___x_2507_ = lean_unsigned_to_nat(0u);
v_bs_x27_2508_ = lean_array_uset(v_bs_2503_, v_i_2502_, v___x_2507_);
v___x_2509_ = ((size_t)1ULL);
v___x_2510_ = lean_usize_add(v_i_2502_, v___x_2509_);
v___x_2511_ = lean_array_uset(v_bs_x27_2508_, v_i_2502_, v_msg_2506_);
v_i_2502_ = v___x_2510_;
v_bs_2503_ = v___x_2511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19___boxed(lean_object* v_sz_2513_, lean_object* v_i_2514_, lean_object* v_bs_2515_){
_start:
{
size_t v_sz_boxed_2516_; size_t v_i_boxed_2517_; lean_object* v_res_2518_; 
v_sz_boxed_2516_ = lean_unbox_usize(v_sz_2513_);
lean_dec(v_sz_2513_);
v_i_boxed_2517_ = lean_unbox_usize(v_i_2514_);
lean_dec(v_i_2514_);
v_res_2518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19(v_sz_boxed_2516_, v_i_boxed_2517_, v_bs_2515_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16(lean_object* v_oldTraces_2519_, lean_object* v_data_2520_, lean_object* v_ref_2521_, lean_object* v_msg_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_fileName_2528_; lean_object* v_fileMap_2529_; lean_object* v_options_2530_; lean_object* v_currRecDepth_2531_; lean_object* v_maxRecDepth_2532_; lean_object* v_ref_2533_; lean_object* v_currNamespace_2534_; lean_object* v_openDecls_2535_; lean_object* v_initHeartbeats_2536_; lean_object* v_maxHeartbeats_2537_; lean_object* v_quotContext_2538_; lean_object* v_currMacroScope_2539_; uint8_t v_diag_2540_; lean_object* v_cancelTk_x3f_2541_; uint8_t v_suppressElabErrors_2542_; lean_object* v_inheritedTraceOptions_2543_; lean_object* v___x_2544_; lean_object* v_traceState_2545_; lean_object* v_traces_2546_; lean_object* v_ref_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; size_t v_sz_2550_; size_t v___x_2551_; lean_object* v___x_2552_; lean_object* v_msg_2553_; lean_object* v___x_2554_; lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2592_; 
v_fileName_2528_ = lean_ctor_get(v___y_2525_, 0);
v_fileMap_2529_ = lean_ctor_get(v___y_2525_, 1);
v_options_2530_ = lean_ctor_get(v___y_2525_, 2);
v_currRecDepth_2531_ = lean_ctor_get(v___y_2525_, 3);
v_maxRecDepth_2532_ = lean_ctor_get(v___y_2525_, 4);
v_ref_2533_ = lean_ctor_get(v___y_2525_, 5);
v_currNamespace_2534_ = lean_ctor_get(v___y_2525_, 6);
v_openDecls_2535_ = lean_ctor_get(v___y_2525_, 7);
v_initHeartbeats_2536_ = lean_ctor_get(v___y_2525_, 8);
v_maxHeartbeats_2537_ = lean_ctor_get(v___y_2525_, 9);
v_quotContext_2538_ = lean_ctor_get(v___y_2525_, 10);
v_currMacroScope_2539_ = lean_ctor_get(v___y_2525_, 11);
v_diag_2540_ = lean_ctor_get_uint8(v___y_2525_, sizeof(void*)*14);
v_cancelTk_x3f_2541_ = lean_ctor_get(v___y_2525_, 12);
v_suppressElabErrors_2542_ = lean_ctor_get_uint8(v___y_2525_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2543_ = lean_ctor_get(v___y_2525_, 13);
v___x_2544_ = lean_st_ref_get(v___y_2526_);
v_traceState_2545_ = lean_ctor_get(v___x_2544_, 4);
lean_inc_ref(v_traceState_2545_);
lean_dec(v___x_2544_);
v_traces_2546_ = lean_ctor_get(v_traceState_2545_, 0);
lean_inc_ref(v_traces_2546_);
lean_dec_ref(v_traceState_2545_);
v_ref_2547_ = l_Lean_replaceRef(v_ref_2521_, v_ref_2533_);
lean_inc_ref(v_inheritedTraceOptions_2543_);
lean_inc(v_cancelTk_x3f_2541_);
lean_inc(v_currMacroScope_2539_);
lean_inc(v_quotContext_2538_);
lean_inc(v_maxHeartbeats_2537_);
lean_inc(v_initHeartbeats_2536_);
lean_inc(v_openDecls_2535_);
lean_inc(v_currNamespace_2534_);
lean_inc(v_maxRecDepth_2532_);
lean_inc(v_currRecDepth_2531_);
lean_inc_ref(v_options_2530_);
lean_inc_ref(v_fileMap_2529_);
lean_inc_ref(v_fileName_2528_);
v___x_2548_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2548_, 0, v_fileName_2528_);
lean_ctor_set(v___x_2548_, 1, v_fileMap_2529_);
lean_ctor_set(v___x_2548_, 2, v_options_2530_);
lean_ctor_set(v___x_2548_, 3, v_currRecDepth_2531_);
lean_ctor_set(v___x_2548_, 4, v_maxRecDepth_2532_);
lean_ctor_set(v___x_2548_, 5, v_ref_2547_);
lean_ctor_set(v___x_2548_, 6, v_currNamespace_2534_);
lean_ctor_set(v___x_2548_, 7, v_openDecls_2535_);
lean_ctor_set(v___x_2548_, 8, v_initHeartbeats_2536_);
lean_ctor_set(v___x_2548_, 9, v_maxHeartbeats_2537_);
lean_ctor_set(v___x_2548_, 10, v_quotContext_2538_);
lean_ctor_set(v___x_2548_, 11, v_currMacroScope_2539_);
lean_ctor_set(v___x_2548_, 12, v_cancelTk_x3f_2541_);
lean_ctor_set(v___x_2548_, 13, v_inheritedTraceOptions_2543_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*14, v_diag_2540_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*14 + 1, v_suppressElabErrors_2542_);
v___x_2549_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2546_);
lean_dec_ref(v_traces_2546_);
v_sz_2550_ = lean_array_size(v___x_2549_);
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16_spec__19(v_sz_2550_, v___x_2551_, v___x_2549_);
v_msg_2553_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2553_, 0, v_data_2520_);
lean_ctor_set(v_msg_2553_, 1, v_msg_2522_);
lean_ctor_set(v_msg_2553_, 2, v___x_2552_);
v___x_2554_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1_spec__1(v_msg_2553_, v___y_2523_, v___y_2524_, v___x_2548_, v___y_2526_);
lean_dec_ref(v___x_2548_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2592_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2592_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v_traceState_2560_; lean_object* v_env_2561_; lean_object* v_nextMacroScope_2562_; lean_object* v_ngen_2563_; lean_object* v_auxDeclNGen_2564_; lean_object* v_cache_2565_; lean_object* v_messages_2566_; lean_object* v_infoState_2567_; lean_object* v_snapshotTasks_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2591_; 
v___x_2559_ = lean_st_ref_take(v___y_2526_);
v_traceState_2560_ = lean_ctor_get(v___x_2559_, 4);
v_env_2561_ = lean_ctor_get(v___x_2559_, 0);
v_nextMacroScope_2562_ = lean_ctor_get(v___x_2559_, 1);
v_ngen_2563_ = lean_ctor_get(v___x_2559_, 2);
v_auxDeclNGen_2564_ = lean_ctor_get(v___x_2559_, 3);
v_cache_2565_ = lean_ctor_get(v___x_2559_, 5);
v_messages_2566_ = lean_ctor_get(v___x_2559_, 6);
v_infoState_2567_ = lean_ctor_get(v___x_2559_, 7);
v_snapshotTasks_2568_ = lean_ctor_get(v___x_2559_, 8);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2570_ = v___x_2559_;
v_isShared_2571_ = v_isSharedCheck_2591_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snapshotTasks_2568_);
lean_inc(v_infoState_2567_);
lean_inc(v_messages_2566_);
lean_inc(v_cache_2565_);
lean_inc(v_traceState_2560_);
lean_inc(v_auxDeclNGen_2564_);
lean_inc(v_ngen_2563_);
lean_inc(v_nextMacroScope_2562_);
lean_inc(v_env_2561_);
lean_dec(v___x_2559_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2591_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
uint64_t v_tid_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2589_; 
v_tid_2572_ = lean_ctor_get_uint64(v_traceState_2560_, sizeof(void*)*1);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_traceState_2560_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v_traceState_2560_, 0);
lean_dec(v_unused_2590_);
v___x_2574_ = v_traceState_2560_;
v_isShared_2575_ = v_isSharedCheck_2589_;
goto v_resetjp_2573_;
}
else
{
lean_dec(v_traceState_2560_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2589_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_ref_2521_);
lean_ctor_set(v___x_2576_, 1, v_a_2555_);
v___x_2577_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2519_, v___x_2576_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2577_);
v___x_2579_ = v___x_2574_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2577_);
lean_ctor_set_uint64(v_reuseFailAlloc_2588_, sizeof(void*)*1, v_tid_2572_);
v___x_2579_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 4, v___x_2579_);
v___x_2581_ = v___x_2570_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_env_2561_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_nextMacroScope_2562_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_ngen_2563_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_auxDeclNGen_2564_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v_cache_2565_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v_messages_2566_);
lean_ctor_set(v_reuseFailAlloc_2587_, 7, v_infoState_2567_);
lean_ctor_set(v_reuseFailAlloc_2587_, 8, v_snapshotTasks_2568_);
v___x_2581_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2582_ = lean_st_ref_set(v___y_2526_, v___x_2581_);
v___x_2583_ = lean_box(0);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2583_);
v___x_2585_ = v___x_2557_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16___boxed(lean_object* v_oldTraces_2593_, lean_object* v_data_2594_, lean_object* v_ref_2595_, lean_object* v_msg_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16(v_oldTraces_2593_, v_data_2594_, v_ref_2595_, v_msg_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2602_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15(lean_object* v_e_2603_){
_start:
{
if (lean_obj_tag(v_e_2603_) == 0)
{
uint8_t v___x_2604_; 
v___x_2604_ = 2;
return v___x_2604_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = 0;
return v___x_2605_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15___boxed(lean_object* v_e_2606_){
_start:
{
uint8_t v_res_2607_; lean_object* v_r_2608_; 
v_res_2607_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15(v_e_2606_);
lean_dec_ref(v_e_2606_);
v_r_2608_ = lean_box(v_res_2607_);
return v_r_2608_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__0));
v___x_2611_ = l_Lean_stringToMessageData(v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__2));
v___x_2614_ = l_Lean_stringToMessageData(v___x_2613_);
return v___x_2614_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4(void){
_start:
{
lean_object* v___x_2615_; double v___x_2616_; 
v___x_2615_ = lean_unsigned_to_nat(1000u);
v___x_2616_ = lean_float_of_nat(v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(lean_object* v_cls_2617_, uint8_t v_collapsed_2618_, lean_object* v_tag_2619_, lean_object* v_opts_2620_, uint8_t v_clsEnabled_2621_, lean_object* v_oldTraces_2622_, lean_object* v_msg_2623_, lean_object* v_resStartStop_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2729_; 
v_fst_2630_ = lean_ctor_get(v_resStartStop_2624_, 0);
v_snd_2631_ = lean_ctor_get(v_resStartStop_2624_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_resStartStop_2624_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2633_ = v_resStartStop_2624_;
v_isShared_2634_ = v_isSharedCheck_2729_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_snd_2631_);
lean_inc(v_fst_2630_);
lean_dec(v_resStartStop_2624_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2729_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v_data_2638_; lean_object* v_fst_2649_; lean_object* v_snd_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2728_; 
v_fst_2649_ = lean_ctor_get(v_snd_2631_, 0);
v_snd_2650_ = lean_ctor_get(v_snd_2631_, 1);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_snd_2631_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2652_ = v_snd_2631_;
v_isShared_2653_ = v_isSharedCheck_2728_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_snd_2650_);
lean_inc(v_fst_2649_);
lean_dec(v_snd_2631_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2728_;
goto v_resetjp_2651_;
}
v___jp_2635_:
{
lean_object* v___x_2639_; 
lean_inc(v___y_2637_);
v___x_2639_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__16(v_oldTraces_2622_, v_data_2638_, v___y_2637_, v___y_2636_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref(v___x_2639_);
v___x_2640_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(v_fst_2630_);
return v___x_2640_;
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_fst_2630_);
v_a_2641_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2639_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2639_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; uint8_t v___x_2655_; lean_object* v___y_2657_; lean_object* v_a_2658_; uint8_t v___y_2682_; double v___y_2713_; 
v___x_2654_ = l_Lean_trace_profiler;
v___x_2655_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_2620_, v___x_2654_);
if (v___x_2655_ == 0)
{
v___y_2682_ = v___x_2655_;
goto v___jp_2681_;
}
else
{
lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2718_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2719_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_2620_, v___x_2718_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; lean_object* v___x_2721_; double v___x_2722_; double v___x_2723_; double v___x_2724_; 
v___x_2720_ = l_Lean_trace_profiler_threshold;
v___x_2721_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(v_opts_2620_, v___x_2720_);
v___x_2722_ = lean_float_of_nat(v___x_2721_);
v___x_2723_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__4);
v___x_2724_ = lean_float_div(v___x_2722_, v___x_2723_);
v___y_2713_ = v___x_2724_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2726_; double v___x_2727_; 
v___x_2725_ = l_Lean_trace_profiler_threshold;
v___x_2726_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__18(v_opts_2620_, v___x_2725_);
v___x_2727_ = lean_float_of_nat(v___x_2726_);
v___y_2713_ = v___x_2727_;
goto v___jp_2712_;
}
}
v___jp_2656_:
{
uint8_t v_result_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v_result_2659_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__15(v_fst_2630_);
v___x_2660_ = l_Lean_TraceResult_toEmoji(v_result_2659_);
v___x_2661_ = l_Lean_stringToMessageData(v___x_2660_);
v___x_2662_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__1);
if (v_isShared_2653_ == 0)
{
lean_ctor_set_tag(v___x_2652_, 7);
lean_ctor_set(v___x_2652_, 1, v___x_2662_);
lean_ctor_set(v___x_2652_, 0, v___x_2661_);
v___x_2664_ = v___x_2652_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v_m_2666_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set_tag(v___x_2633_, 7);
lean_ctor_set(v___x_2633_, 1, v_a_2658_);
lean_ctor_set(v___x_2633_, 0, v___x_2664_);
v_m_2666_ = v___x_2633_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_a_2658_);
v_m_2666_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; double v___x_2669_; lean_object* v_data_2670_; 
v___x_2667_ = lean_box(v_result_2659_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
v___x_2669_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__0);
lean_inc_ref(v_tag_2619_);
lean_inc_ref(v___x_2668_);
lean_inc(v_cls_2617_);
v_data_2670_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2670_, 0, v_cls_2617_);
lean_ctor_set(v_data_2670_, 1, v___x_2668_);
lean_ctor_set(v_data_2670_, 2, v_tag_2619_);
lean_ctor_set_float(v_data_2670_, sizeof(void*)*3, v___x_2669_);
lean_ctor_set_float(v_data_2670_, sizeof(void*)*3 + 8, v___x_2669_);
lean_ctor_set_uint8(v_data_2670_, sizeof(void*)*3 + 16, v_collapsed_2618_);
if (v___x_2655_ == 0)
{
lean_dec_ref(v___x_2668_);
lean_dec(v_snd_2650_);
lean_dec(v_fst_2649_);
lean_dec_ref(v_tag_2619_);
lean_dec(v_cls_2617_);
v___y_2636_ = v_m_2666_;
v___y_2637_ = v___y_2657_;
v_data_2638_ = v_data_2670_;
goto v___jp_2635_;
}
else
{
lean_object* v_data_2671_; double v___x_2672_; double v___x_2673_; 
lean_dec_ref(v_data_2670_);
v_data_2671_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2671_, 0, v_cls_2617_);
lean_ctor_set(v_data_2671_, 1, v___x_2668_);
lean_ctor_set(v_data_2671_, 2, v_tag_2619_);
v___x_2672_ = lean_unbox_float(v_fst_2649_);
lean_dec(v_fst_2649_);
lean_ctor_set_float(v_data_2671_, sizeof(void*)*3, v___x_2672_);
v___x_2673_ = lean_unbox_float(v_snd_2650_);
lean_dec(v_snd_2650_);
lean_ctor_set_float(v_data_2671_, sizeof(void*)*3 + 8, v___x_2673_);
lean_ctor_set_uint8(v_data_2671_, sizeof(void*)*3 + 16, v_collapsed_2618_);
v___y_2636_ = v_m_2666_;
v___y_2637_ = v___y_2657_;
v_data_2638_ = v_data_2671_;
goto v___jp_2635_;
}
}
}
}
v___jp_2676_:
{
lean_object* v_ref_2677_; lean_object* v___x_2678_; 
v_ref_2677_ = lean_ctor_get(v___y_2627_, 5);
lean_inc(v___y_2628_);
lean_inc_ref(v___y_2627_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v_fst_2630_);
v___x_2678_ = lean_apply_6(v_msg_2623_, v_fst_2630_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, lean_box(0));
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2678_);
v___y_2657_ = v_ref_2677_;
v_a_2658_ = v_a_2679_;
goto v___jp_2656_;
}
else
{
lean_object* v___x_2680_; 
lean_dec_ref(v___x_2678_);
v___x_2680_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___closed__3);
v___y_2657_ = v_ref_2677_;
v_a_2658_ = v___x_2680_;
goto v___jp_2656_;
}
}
v___jp_2681_:
{
if (v_clsEnabled_2621_ == 0)
{
if (v___y_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v_traceState_2684_; lean_object* v_env_2685_; lean_object* v_nextMacroScope_2686_; lean_object* v_ngen_2687_; lean_object* v_auxDeclNGen_2688_; lean_object* v_cache_2689_; lean_object* v_messages_2690_; lean_object* v_infoState_2691_; lean_object* v_snapshotTasks_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2711_; 
lean_del_object(v___x_2652_);
lean_dec(v_snd_2650_);
lean_dec(v_fst_2649_);
lean_del_object(v___x_2633_);
lean_dec_ref(v_msg_2623_);
lean_dec_ref(v_tag_2619_);
lean_dec(v_cls_2617_);
v___x_2683_ = lean_st_ref_take(v___y_2628_);
v_traceState_2684_ = lean_ctor_get(v___x_2683_, 4);
v_env_2685_ = lean_ctor_get(v___x_2683_, 0);
v_nextMacroScope_2686_ = lean_ctor_get(v___x_2683_, 1);
v_ngen_2687_ = lean_ctor_get(v___x_2683_, 2);
v_auxDeclNGen_2688_ = lean_ctor_get(v___x_2683_, 3);
v_cache_2689_ = lean_ctor_get(v___x_2683_, 5);
v_messages_2690_ = lean_ctor_get(v___x_2683_, 6);
v_infoState_2691_ = lean_ctor_get(v___x_2683_, 7);
v_snapshotTasks_2692_ = lean_ctor_get(v___x_2683_, 8);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2694_ = v___x_2683_;
v_isShared_2695_ = v_isSharedCheck_2711_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_snapshotTasks_2692_);
lean_inc(v_infoState_2691_);
lean_inc(v_messages_2690_);
lean_inc(v_cache_2689_);
lean_inc(v_traceState_2684_);
lean_inc(v_auxDeclNGen_2688_);
lean_inc(v_ngen_2687_);
lean_inc(v_nextMacroScope_2686_);
lean_inc(v_env_2685_);
lean_dec(v___x_2683_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2711_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
uint64_t v_tid_2696_; lean_object* v_traces_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2710_; 
v_tid_2696_ = lean_ctor_get_uint64(v_traceState_2684_, sizeof(void*)*1);
v_traces_2697_ = lean_ctor_get(v_traceState_2684_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_traceState_2684_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2699_ = v_traceState_2684_;
v_isShared_2700_ = v_isSharedCheck_2710_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_traces_2697_);
lean_dec(v_traceState_2684_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2710_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2622_, v_traces_2697_);
lean_dec_ref(v_traces_2697_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2701_);
v___x_2703_ = v___x_2699_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2701_);
lean_ctor_set_uint64(v_reuseFailAlloc_2709_, sizeof(void*)*1, v_tid_2696_);
v___x_2703_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 4, v___x_2703_);
v___x_2705_ = v___x_2694_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_env_2685_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_nextMacroScope_2686_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_ngen_2687_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_auxDeclNGen_2688_);
lean_ctor_set(v_reuseFailAlloc_2708_, 4, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2708_, 5, v_cache_2689_);
lean_ctor_set(v_reuseFailAlloc_2708_, 6, v_messages_2690_);
lean_ctor_set(v_reuseFailAlloc_2708_, 7, v_infoState_2691_);
lean_ctor_set(v_reuseFailAlloc_2708_, 8, v_snapshotTasks_2692_);
v___x_2705_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_st_ref_set(v___y_2628_, v___x_2705_);
v___x_2707_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(v_fst_2630_);
return v___x_2707_;
}
}
}
}
}
else
{
goto v___jp_2676_;
}
}
else
{
goto v___jp_2676_;
}
}
v___jp_2712_:
{
double v___x_2714_; double v___x_2715_; double v___x_2716_; uint8_t v___x_2717_; 
v___x_2714_ = lean_unbox_float(v_snd_2650_);
v___x_2715_ = lean_unbox_float(v_fst_2649_);
v___x_2716_ = lean_float_sub(v___x_2714_, v___x_2715_);
v___x_2717_ = lean_float_decLt(v___y_2713_, v___x_2716_);
v___y_2682_ = v___x_2717_;
goto v___jp_2681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object* v_cls_2730_, lean_object* v_collapsed_2731_, lean_object* v_tag_2732_, lean_object* v_opts_2733_, lean_object* v_clsEnabled_2734_, lean_object* v_oldTraces_2735_, lean_object* v_msg_2736_, lean_object* v_resStartStop_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
uint8_t v_collapsed_boxed_2743_; uint8_t v_clsEnabled_boxed_2744_; lean_object* v_res_2745_; 
v_collapsed_boxed_2743_ = lean_unbox(v_collapsed_2731_);
v_clsEnabled_boxed_2744_ = lean_unbox(v_clsEnabled_2734_);
v_res_2745_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(v_cls_2730_, v_collapsed_boxed_2743_, v_tag_2732_, v_opts_2733_, v_clsEnabled_boxed_2744_, v_oldTraces_2735_, v_msg_2736_, v_resStartStop_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v_opts_2733_);
return v_res_2745_;
}
}
static uint64_t _init_l_Lean_Meta_wrapInstance___closed__0(void){
_start:
{
uint8_t v___x_2746_; uint64_t v___x_2747_; 
v___x_2746_ = 3;
v___x_2747_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2746_);
return v___x_2747_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__0));
v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
return v___x_2750_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__3));
v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
return v___x_2755_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__5));
v___x_2758_ = l_Lean_stringToMessageData(v___x_2757_);
return v___x_2758_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__1));
v___x_2761_ = l_Lean_stringToMessageData(v___x_2760_);
return v___x_2761_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__8));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__10));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__12));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__14));
v___x_2775_ = l_Lean_stringToMessageData(v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(lean_object* v_upperBound_2776_, lean_object* v_fst_2777_, lean_object* v_args_2778_, uint8_t v_compile_2779_, uint8_t v_logCompileErrors_2780_, uint8_t v___x_2781_, uint8_t v_isMeta_2782_, lean_object* v_val_2783_, lean_object* v_expectedType_2784_, lean_object* v_a_2785_, lean_object* v_b_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_a_2793_; lean_object* v___y_2798_; uint8_t v___x_2817_; 
v___x_2817_ = lean_nat_dec_lt(v_a_2785_, v_upperBound_2776_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v_b_2786_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = lean_array_fget_borrowed(v_fst_2777_, v_a_2785_);
v___x_2820_ = l_Lean_Expr_mvarId_x21(v___x_2819_);
lean_inc(v___x_2820_);
v___x_2821_ = l_Lean_MVarId_getDecl(v___x_2820_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v_userName_2823_; lean_object* v_type_2824_; lean_object* v___x_2825_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref(v___x_2821_);
v_userName_2823_ = lean_ctor_get(v_a_2822_, 0);
lean_inc(v_userName_2823_);
v_type_2824_ = lean_ctor_get(v_a_2822_, 2);
lean_inc_ref(v_type_2824_);
lean_dec(v_a_2822_);
v___x_2825_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_type_2824_, v___y_2788_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_n(v_a_2826_, 2);
lean_dec_ref(v___x_2825_);
v___x_2827_ = l_Lean_Meta_isProp(v_a_2826_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v_cls_2830_; lean_object* v___f_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref(v___x_2827_);
v___x_2829_ = lean_box(0);
v_cls_2830_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_2831_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0));
v___x_2832_ = lean_array_fget_borrowed(v_args_2778_, v_a_2785_);
v___x_2833_ = lean_unbox(v_a_2828_);
lean_dec(v_a_2828_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
lean_inc(v_a_2826_);
v___x_2834_ = l_Lean_Meta_isClass_x3f(v_a_2826_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2933_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2933_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2933_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
if (lean_obj_tag(v_a_2835_) == 0)
{
lean_object* v_options_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___f_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
lean_del_object(v___x_2837_);
v_options_2839_ = lean_ctor_get(v___y_2789_, 2);
v___x_2840_ = lean_box(v___x_2781_);
v___x_2841_ = lean_box(v___x_2817_);
v___x_2842_ = lean_box(v_compile_2779_);
v___x_2843_ = lean_box(v_logCompileErrors_2780_);
v___x_2844_ = lean_box(v_isMeta_2782_);
lean_inc(v_a_2826_);
lean_inc(v___x_2832_);
lean_inc(v___x_2820_);
v___f_2845_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_2845_, 0, v___x_2820_);
lean_closure_set(v___f_2845_, 1, v___x_2832_);
lean_closure_set(v___f_2845_, 2, v___x_2829_);
lean_closure_set(v___f_2845_, 3, v_a_2826_);
lean_closure_set(v___f_2845_, 4, v___x_2840_);
lean_closure_set(v___f_2845_, 5, v___x_2841_);
lean_closure_set(v___f_2845_, 6, v___x_2842_);
lean_closure_set(v___f_2845_, 7, v___x_2843_);
lean_closure_set(v___f_2845_, 8, v___x_2844_);
v___x_2846_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2847_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2839_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
lean_dec_ref(v___f_2845_);
lean_dec(v_userName_2823_);
lean_inc(v___x_2832_);
v___x_2848_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_2820_, v___x_2832_, v___x_2829_, v_a_2826_, v___x_2781_, v___x_2817_, v_compile_2779_, v_logCompileErrors_2780_, v_isMeta_2782_, v___x_2829_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2848_;
goto v___jp_2797_;
}
else
{
lean_object* v___x_2849_; 
lean_inc(v_userName_2823_);
lean_inc(v_val_2783_);
v___x_2849_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_2783_, v_userName_2823_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v_fst_2853_; lean_object* v_snd_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2885_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v_fst_2853_ = lean_ctor_get(v_a_2850_, 0);
v_snd_2854_ = lean_ctor_get(v_a_2850_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_a_2850_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2856_ = v_a_2850_;
v_isShared_2857_ = v_isSharedCheck_2885_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_snd_2854_);
lean_inc(v_fst_2853_);
lean_dec(v_a_2850_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2885_;
goto v_resetjp_2855_;
}
v___jp_2851_:
{
lean_object* v___x_2852_; 
lean_inc(v___x_2832_);
v___x_2852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_2820_, v___x_2832_, v___x_2829_, v_a_2826_, v___x_2781_, v___x_2817_, v_compile_2779_, v_logCompileErrors_2780_, v_isMeta_2782_, v___x_2829_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2852_;
goto v___jp_2797_;
}
v_resetjp_2855_:
{
uint8_t v___x_2858_; 
v___x_2858_ = lean_name_eq(v_fst_2853_, v_val_2783_);
if (v___x_2858_ == 0)
{
if (v___x_2847_ == 0)
{
lean_del_object(v___x_2856_);
lean_dec(v_snd_2854_);
lean_dec(v_fst_2853_);
lean_dec_ref(v___f_2845_);
lean_dec(v_userName_2823_);
goto v___jp_2851_;
}
else
{
lean_object* v___x_2859_; 
lean_dec(v_a_2826_);
v___x_2859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_2830_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; uint8_t v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref(v___x_2859_);
v___x_2861_ = lean_unbox(v_a_2860_);
lean_dec(v_a_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_del_object(v___x_2856_);
lean_dec(v_userName_2823_);
lean_inc_ref(v_expectedType_2784_);
lean_inc(v_val_2783_);
v___x_2862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_2783_, v_fst_2853_, v_expectedType_2784_, v___f_2831_, v___f_2845_, v___x_2829_, v_cls_2830_, v_snd_2854_, v___x_2820_, v___x_2829_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2862_;
goto v___jp_2797_;
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2863_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4);
v___x_2864_ = l_Lean_MessageData_ofName(v_userName_2823_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 7);
lean_ctor_set(v___x_2856_, 1, v___x_2864_);
lean_ctor_set(v___x_2856_, 0, v___x_2863_);
v___x_2866_ = v___x_2856_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2863_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2867_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
lean_inc(v_fst_2853_);
v___x_2869_ = l_Lean_MessageData_ofName(v_fst_2853_);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_2872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2830_, v___x_2872_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref(v___x_2873_);
lean_inc_ref(v_expectedType_2784_);
lean_inc(v_val_2783_);
v___x_2875_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_2783_, v_fst_2853_, v_expectedType_2784_, v___f_2831_, v___f_2845_, v___x_2829_, v_cls_2830_, v_snd_2854_, v___x_2820_, v_a_2874_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2875_;
goto v___jp_2797_;
}
else
{
lean_dec(v_snd_2854_);
lean_dec(v_fst_2853_);
lean_dec_ref(v___f_2845_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_del_object(v___x_2856_);
lean_dec(v_snd_2854_);
lean_dec(v_fst_2853_);
lean_dec_ref(v___f_2845_);
lean_dec(v_userName_2823_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2877_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2859_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2859_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
else
{
lean_del_object(v___x_2856_);
lean_dec(v_snd_2854_);
lean_dec(v_fst_2853_);
lean_dec_ref(v___f_2845_);
lean_dec(v_userName_2823_);
goto v___jp_2851_;
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref(v___f_2845_);
lean_dec(v_a_2826_);
lean_dec(v_userName_2823_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2886_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2849_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2849_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_object* v_options_2894_; lean_object* v_a_2896_; lean_object* v___y_2899_; uint8_t v___y_2900_; lean_object* v_a_2905_; lean_object* v___y_2909_; lean_object* v___x_2913_; uint8_t v___x_2914_; 
lean_dec_ref(v_a_2835_);
lean_dec(v_userName_2823_);
v_options_2894_ = lean_ctor_get(v___y_2789_, 2);
v___x_2913_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2914_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2894_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; 
lean_del_object(v___x_2837_);
lean_inc(v___x_2832_);
v___x_2915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_2832_, v_a_2826_, v_compile_2779_, v_logCompileErrors_2780_, v_isMeta_2782_, v___x_2820_, v___x_2829_, v___x_2829_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2915_;
goto v___jp_2797_;
}
else
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_box(0);
lean_inc(v_a_2826_);
v___x_2917_ = l_Lean_Meta_trySynthInstance(v_a_2826_, v___x_2916_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref(v___x_2917_);
if (lean_obj_tag(v_a_2918_) == 1)
{
lean_object* v_a_2919_; lean_object* v___x_2920_; 
v_a_2919_ = lean_ctor_get(v_a_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref(v_a_2918_);
v___x_2920_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_2830_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; uint8_t v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
v___x_2922_ = lean_unbox(v_a_2921_);
lean_dec(v_a_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; 
lean_inc(v___x_2820_);
v___x_2923_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_2820_, v_a_2919_, v___x_2829_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2909_ = v___x_2923_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2924_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2);
lean_inc(v_a_2919_);
v___x_2925_ = l_Lean_MessageData_ofExpr(v_a_2919_);
v___x_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2830_, v___x_2926_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref(v___x_2927_);
lean_inc(v___x_2820_);
v___x_2929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_2820_, v_a_2919_, v_a_2928_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2909_ = v___x_2929_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_2930_; 
lean_dec(v_a_2919_);
v_a_2930_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2927_);
v_a_2905_ = v_a_2930_;
goto v___jp_2904_;
}
}
}
else
{
lean_object* v_a_2931_; 
lean_dec(v_a_2919_);
v_a_2931_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2931_);
lean_dec_ref(v___x_2920_);
v_a_2905_ = v_a_2931_;
goto v___jp_2904_;
}
}
else
{
lean_dec(v_a_2918_);
lean_del_object(v___x_2837_);
v_a_2896_ = v___x_2829_;
goto v___jp_2895_;
}
}
else
{
lean_object* v_a_2932_; 
v_a_2932_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2917_);
v_a_2905_ = v_a_2932_;
goto v___jp_2904_;
}
}
v___jp_2895_:
{
lean_object* v___x_2897_; 
lean_inc(v___x_2832_);
v___x_2897_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_2832_, v_a_2826_, v_compile_2779_, v_logCompileErrors_2780_, v_isMeta_2782_, v___x_2820_, v___x_2829_, v_a_2896_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2897_;
goto v___jp_2797_;
}
v___jp_2898_:
{
if (v___y_2900_ == 0)
{
lean_dec_ref(v___y_2899_);
lean_del_object(v___x_2837_);
v_a_2896_ = v___x_2829_;
goto v___jp_2895_;
}
else
{
lean_object* v___x_2902_; 
lean_dec(v_a_2826_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set_tag(v___x_2837_, 1);
lean_ctor_set(v___x_2837_, 0, v___y_2899_);
v___x_2902_ = v___x_2837_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___y_2899_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
v___jp_2904_:
{
uint8_t v___x_2906_; 
v___x_2906_ = l_Lean_Exception_isInterrupt(v_a_2905_);
if (v___x_2906_ == 0)
{
uint8_t v___x_2907_; 
lean_inc_ref(v_a_2905_);
v___x_2907_ = l_Lean_Exception_isRuntime(v_a_2905_);
v___y_2899_ = v_a_2905_;
v___y_2900_ = v___x_2907_;
goto v___jp_2898_;
}
else
{
v___y_2899_ = v_a_2905_;
v___y_2900_ = v___x_2906_;
goto v___jp_2898_;
}
}
v___jp_2908_:
{
if (lean_obj_tag(v___y_2909_) == 0)
{
lean_object* v_a_2910_; 
lean_del_object(v___x_2837_);
v_a_2910_ = lean_ctor_get(v___y_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v___y_2909_);
if (lean_obj_tag(v_a_2910_) == 0)
{
lean_dec(v_a_2826_);
lean_dec(v___x_2820_);
v_a_2793_ = v___x_2829_;
goto v___jp_2792_;
}
else
{
lean_object* v_a_2911_; 
v_a_2911_ = lean_ctor_get(v_a_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v_a_2910_);
v_a_2896_ = v_a_2911_;
goto v___jp_2895_;
}
}
else
{
lean_object* v_a_2912_; 
v_a_2912_ = lean_ctor_get(v___y_2909_, 0);
lean_inc(v_a_2912_);
lean_dec_ref(v___y_2909_);
v_a_2905_ = v_a_2912_;
goto v___jp_2904_;
}
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_a_2826_);
lean_dec(v_userName_2823_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2934_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2834_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2834_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v___x_2942_; 
lean_dec(v_userName_2823_);
lean_inc(v___y_2790_);
lean_inc_ref(v___y_2789_);
lean_inc(v___y_2788_);
lean_inc_ref(v___y_2787_);
lean_inc(v___x_2832_);
v___x_2942_ = lean_infer_type(v___x_2832_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc_n(v_a_2943_, 2);
lean_dec_ref(v___x_2942_);
lean_inc(v_a_2826_);
v___x_2944_ = l_Lean_Meta_isExprDefEq(v_a_2826_, v_a_2943_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___f_2946_; uint8_t v___x_2947_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
v___f_2946_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7));
v___x_2947_ = lean_unbox(v_a_2945_);
lean_dec(v_a_2945_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; 
v___x_2948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_2830_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; uint8_t v___x_2950_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v___x_2950_ = lean_unbox(v_a_2949_);
lean_dec(v_a_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec(v_a_2943_);
lean_inc(v___x_2832_);
v___x_2951_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_2826_, v___x_2832_, v___x_2817_, v___x_2820_, v___f_2946_, v___x_2829_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2951_;
goto v___jp_2797_;
}
else
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2952_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9);
lean_inc(v_a_2785_);
v___x_2953_ = l_Nat_reprFast(v_a_2785_);
v___x_2954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
v___x_2955_ = l_Lean_MessageData_ofFormat(v___x_2954_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2952_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
lean_inc(v_a_2826_);
v___x_2959_ = l_Lean_MessageData_ofExpr(v_a_2826_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = l_Lean_MessageData_ofExpr(v_a_2943_);
v___x_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15);
v___x_2966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
lean_inc(v___x_2832_);
v___x_2967_ = l_Lean_MessageData_ofExpr(v___x_2832_);
v___x_2968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2830_, v___x_2968_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref(v___x_2969_);
lean_inc(v___x_2832_);
v___x_2971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_2826_, v___x_2832_, v___x_2817_, v___x_2820_, v___f_2946_, v_a_2970_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2971_;
goto v___jp_2797_;
}
else
{
lean_dec(v_a_2826_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
return v___x_2969_;
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_a_2943_);
lean_dec(v_a_2826_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2972_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2948_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2948_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v___x_2980_; 
lean_dec(v_a_2943_);
lean_dec(v_a_2826_);
lean_inc(v___x_2832_);
v___x_2980_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2820_, v___x_2832_, v___y_2788_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_2829_, v_a_2981_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v___y_2798_ = v___x_2982_;
goto v___jp_2797_;
}
else
{
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
return v___x_2980_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_a_2943_);
lean_dec(v_a_2826_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2983_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2944_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2944_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_a_2826_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2991_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2942_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2942_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_a_2826_);
lean_dec(v_userName_2823_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2999_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2827_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2827_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v_userName_2823_);
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_3007_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2825_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2825_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v___x_2820_);
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_3015_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2821_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2821_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
v___jp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_nat_add(v_a_2785_, v___x_2794_);
lean_dec(v_a_2785_);
v_a_2785_ = v___x_2795_;
v_b_2786_ = v_a_2793_;
goto _start;
}
v___jp_2797_:
{
if (lean_obj_tag(v___y_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2808_; 
v_a_2799_ = lean_ctor_get(v___y_2798_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___y_2798_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2801_ = v___y_2798_;
v_isShared_2802_ = v_isSharedCheck_2808_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___y_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2808_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
if (lean_obj_tag(v_a_2799_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; 
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2803_ = lean_ctor_get(v_a_2799_, 0);
lean_inc(v_a_2803_);
lean_dec_ref(v_a_2799_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v_a_2803_);
v___x_2805_ = v___x_2801_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
else
{
lean_object* v_a_2807_; 
lean_del_object(v___x_2801_);
v_a_2807_ = lean_ctor_get(v_a_2799_, 0);
lean_inc(v_a_2807_);
lean_dec_ref(v_a_2799_);
v_a_2793_ = v_a_2807_;
goto v___jp_2792_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2785_);
lean_dec_ref(v_expectedType_2784_);
lean_dec(v_val_2783_);
v_a_2809_ = lean_ctor_get(v___y_2798_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___y_2798_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___y_2798_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___y_2798_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__2));
v___x_3025_ = l_Lean_stringToMessageData(v___x_3024_);
return v___x_3025_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__4));
v___x_3028_ = l_Lean_stringToMessageData(v___x_3027_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__6));
v___x_3031_ = l_Lean_stringToMessageData(v___x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12(lean_object* v_inst_3032_, lean_object* v_expectedType_3033_, uint8_t v___x_3034_, uint8_t v_compile_3035_, uint8_t v_logCompileErrors_3036_, uint8_t v_isMeta_3037_, lean_object* v_val_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; 
if (lean_obj_tag(v_x_3039_) == 5)
{
lean_object* v_fn_3086_; lean_object* v_arg_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_fn_3086_ = lean_ctor_get(v_x_3039_, 0);
lean_inc_ref(v_fn_3086_);
v_arg_3087_ = lean_ctor_get(v_x_3039_, 1);
lean_inc_ref(v_arg_3087_);
lean_dec_ref(v_x_3039_);
v___x_3088_ = lean_array_set(v_x_3040_, v_x_3041_, v_arg_3087_);
v___x_3089_ = lean_unsigned_to_nat(1u);
v___x_3090_ = lean_nat_sub(v_x_3041_, v___x_3089_);
lean_dec(v_x_3041_);
v_x_3039_ = v_fn_3086_;
v_x_3040_ = v___x_3088_;
v_x_3041_ = v___x_3090_;
goto _start;
}
else
{
uint8_t v___x_3092_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v_options_3097_; lean_object* v___y_3098_; lean_object* v_cls_3164_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___x_3187_; 
lean_dec(v_x_3041_);
v___x_3092_ = 1;
v_cls_3164_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3187_ = l_Lean_Expr_constName_x3f(v_x_3039_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_x_3039_);
lean_dec(v_val_3038_);
v___y_3166_ = v___y_3042_;
v___y_3167_ = v___y_3043_;
v___y_3168_ = v___y_3044_;
v___y_3169_ = v___y_3045_;
goto v___jp_3165_;
}
else
{
lean_object* v_val_3188_; lean_object* v___x_3189_; 
v_val_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_val_3188_);
lean_dec_ref(v___x_3187_);
v___x_3189_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3188_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref(v___x_3189_);
if (lean_obj_tag(v_a_3190_) == 6)
{
lean_object* v_val_3191_; lean_object* v___x_3192_; 
lean_dec_ref(v_inst_3032_);
v_val_3191_ = lean_ctor_get(v_a_3190_, 0);
lean_inc_ref(v_val_3191_);
lean_dec_ref(v_a_3190_);
lean_inc(v___y_3045_);
lean_inc_ref(v___y_3044_);
lean_inc(v___y_3043_);
lean_inc_ref(v___y_3042_);
lean_inc_ref(v_x_3039_);
v___x_3192_ = lean_infer_type(v_x_3039_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref(v___x_3192_);
v___x_3194_ = 0;
v___x_3195_ = l_Lean_Meta_forallMetaTelescope(v_a_3193_, v___x_3194_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v_snd_3197_; lean_object* v_fst_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3297_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref(v___x_3195_);
v_snd_3197_ = lean_ctor_get(v_a_3196_, 1);
v_fst_3198_ = lean_ctor_get(v_a_3196_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_a_3196_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3200_ = v_a_3196_;
v_isShared_3201_ = v_isSharedCheck_3297_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_snd_3197_);
lean_inc(v_fst_3198_);
lean_dec(v_a_3196_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3297_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v_snd_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3295_; 
v_snd_3202_ = lean_ctor_get(v_snd_3197_, 1);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_snd_3197_);
if (v_isSharedCheck_3295_ == 0)
{
lean_object* v_unused_3296_; 
v_unused_3296_ = lean_ctor_get(v_snd_3197_, 0);
lean_dec(v_unused_3296_);
v___x_3204_ = v_snd_3197_;
v_isShared_3205_ = v_isSharedCheck_3295_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snd_3202_);
lean_dec(v_snd_3197_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3295_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3206_ = lean_array_get_size(v_x_3040_);
v___x_3243_ = lean_array_get_size(v_fst_3198_);
v___x_3244_ = lean_nat_dec_eq(v___x_3206_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
lean_dec(v_snd_3202_);
lean_dec(v_fst_3198_);
lean_dec_ref(v_val_3191_);
lean_dec(v_val_3038_);
lean_dec_ref(v_expectedType_3033_);
v___x_3245_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_3246_ = l_Lean_MessageData_ofExpr(v_x_3039_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 7);
lean_ctor_set(v___x_3204_, 1, v___x_3246_);
lean_ctor_set(v___x_3204_, 0, v___x_3245_);
v___x_3248_ = v___x_3204_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3);
if (v_isShared_3201_ == 0)
{
lean_ctor_set_tag(v___x_3200_, 7);
lean_ctor_set(v___x_3200_, 1, v___x_3249_);
lean_ctor_set(v___x_3200_, 0, v___x_3248_);
v___x_3251_ = v___x_3200_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3248_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3252_ = lean_array_to_list(v_x_3040_);
v___x_3253_ = lean_box(0);
v___x_3254_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_3252_, v___x_3253_);
v___x_3255_ = l_Lean_MessageData_ofList(v___x_3254_);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3251_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3256_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
return v___x_3257_;
}
}
}
else
{
lean_object* v___x_3260_; 
lean_inc_ref(v_expectedType_3033_);
v___x_3260_ = l_Lean_Meta_isExprDefEq(v_expectedType_3033_, v_snd_3202_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; uint8_t v___x_3262_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = lean_unbox(v_a_3261_);
lean_dec(v_a_3261_);
if (v___x_3262_ == 0)
{
lean_object* v_toConstantVal_3263_; lean_object* v_name_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
lean_dec(v_fst_3198_);
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_x_3039_);
lean_dec(v_val_3038_);
v_toConstantVal_3263_ = lean_ctor_get(v_val_3191_, 0);
lean_inc_ref(v_toConstantVal_3263_);
lean_dec_ref(v_val_3191_);
v_name_3264_ = lean_ctor_get(v_toConstantVal_3263_, 0);
lean_inc(v_name_3264_);
lean_dec_ref(v_toConstantVal_3263_);
v___x_3265_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_3266_ = l_Lean_MessageData_ofExpr(v_expectedType_3033_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 7);
lean_ctor_set(v___x_3204_, 1, v___x_3266_);
lean_ctor_set(v___x_3204_, 0, v___x_3265_);
v___x_3268_ = v___x_3204_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3271_; 
v___x_3269_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_3201_ == 0)
{
lean_ctor_set_tag(v___x_3200_, 7);
lean_ctor_set(v___x_3200_, 1, v___x_3269_);
lean_ctor_set(v___x_3200_, 0, v___x_3268_);
v___x_3271_ = v___x_3200_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3268_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v___x_3269_);
v___x_3271_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
v___x_3272_ = l_Lean_MessageData_ofConstName(v_name_3264_, v___x_3034_);
v___x_3273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3271_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3275_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3276_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3276_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
else
{
lean_del_object(v___x_3204_);
lean_del_object(v___x_3200_);
v___y_3208_ = v___y_3042_;
v___y_3209_ = v___y_3043_;
v___y_3210_ = v___y_3044_;
v___y_3211_ = v___y_3045_;
goto v___jp_3207_;
}
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_del_object(v___x_3204_);
lean_del_object(v___x_3200_);
lean_dec(v_fst_3198_);
lean_dec_ref(v_val_3191_);
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_x_3039_);
lean_dec(v_val_3038_);
lean_dec_ref(v_expectedType_3033_);
v_a_3287_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3260_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3260_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
v___jp_3207_:
{
lean_object* v_numParams_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_numParams_3212_ = lean_ctor_get(v_val_3191_, 3);
lean_inc(v_numParams_3212_);
lean_dec_ref(v_val_3191_);
v___x_3213_ = lean_box(0);
v___x_3214_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(v___x_3206_, v_fst_3198_, v_x_3040_, v_compile_3035_, v_logCompileErrors_3036_, v___x_3034_, v_isMeta_3037_, v_val_3038_, v_expectedType_3033_, v_numParams_3212_, v___x_3213_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec_ref(v_x_3040_);
if (lean_obj_tag(v___x_3214_) == 0)
{
size_t v_sz_3215_; size_t v___x_3216_; lean_object* v___x_3217_; 
lean_dec_ref(v___x_3214_);
v_sz_3215_ = lean_array_size(v_fst_3198_);
v___x_3216_ = ((size_t)0ULL);
v___x_3217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_3215_, v___x_3216_, v_fst_3198_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3226_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = l_Lean_mkAppN(v_x_3039_, v_a_3218_);
lean_dec(v_a_3218_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3222_);
v___x_3224_ = v___x_3220_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v_x_3039_);
v_a_3227_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3217_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3217_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec(v_fst_3198_);
lean_dec_ref(v_x_3039_);
v_a_3235_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3214_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3214_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v_val_3191_);
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_x_3039_);
lean_dec(v_val_3038_);
lean_dec_ref(v_expectedType_3033_);
v_a_3298_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3195_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3195_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_dec_ref(v_val_3191_);
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_x_3039_);
lean_dec(v_val_3038_);
lean_dec_ref(v_expectedType_3033_);
return v___x_3192_;
}
}
else
{
lean_dec(v_a_3190_);
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_x_3039_);
lean_dec(v_val_3038_);
v___y_3166_ = v___y_3042_;
v___y_3167_ = v___y_3043_;
v___y_3168_ = v___y_3044_;
v___y_3169_ = v___y_3045_;
goto v___jp_3165_;
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec_ref(v_x_3040_);
lean_dec_ref(v_x_3039_);
lean_dec(v_val_3038_);
lean_dec_ref(v_expectedType_3033_);
lean_dec_ref(v_inst_3032_);
v_a_3306_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3189_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3189_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
v___jp_3093_:
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3100_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3097_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; 
lean_dec_ref(v_expectedType_3033_);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_inst_3032_);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; 
lean_inc(v___y_3098_);
lean_inc_ref(v___y_3096_);
lean_inc(v___y_3095_);
lean_inc_ref(v___y_3094_);
lean_inc_ref(v_inst_3032_);
v___x_3102_ = lean_infer_type(v_inst_3032_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3098_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3104_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref(v___x_3102_);
lean_inc_ref(v_expectedType_3033_);
v___x_3104_ = l_Lean_Meta_isExprDefEq(v_expectedType_3033_, v_a_3103_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3098_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3155_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3155_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3155_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
uint8_t v___x_3109_; 
v___x_3109_ = lean_unbox(v_a_3105_);
lean_dec(v_a_3105_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v_a_3112_; lean_object* v___x_3113_; 
lean_del_object(v___x_3107_);
v___x_3110_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_3111_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3110_, v___y_3098_);
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc_n(v_a_3112_, 2);
lean_dec_ref(v___x_3111_);
v___x_3113_ = l_Lean_Meta_mkAuxDefinition(v_a_3112_, v_expectedType_3033_, v_inst_3032_, v___x_3034_, v___x_3034_, v___x_3092_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3098_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref(v___x_3113_);
v___x_3115_ = 3;
lean_inc(v_a_3112_);
v___x_3116_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3112_, v___x_3115_, v___y_3095_, v___y_3098_);
lean_dec_ref(v___x_3116_);
if (v_isMeta_3037_ == 0)
{
v___y_3070_ = v_a_3114_;
v___y_3071_ = v_a_3112_;
v___y_3072_ = v___y_3096_;
v___y_3073_ = v___y_3098_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3117_; lean_object* v_env_3118_; lean_object* v_nextMacroScope_3119_; lean_object* v_ngen_3120_; lean_object* v_auxDeclNGen_3121_; lean_object* v_traceState_3122_; lean_object* v_messages_3123_; lean_object* v_infoState_3124_; lean_object* v_snapshotTasks_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3150_; 
v___x_3117_ = lean_st_ref_take(v___y_3098_);
v_env_3118_ = lean_ctor_get(v___x_3117_, 0);
v_nextMacroScope_3119_ = lean_ctor_get(v___x_3117_, 1);
v_ngen_3120_ = lean_ctor_get(v___x_3117_, 2);
v_auxDeclNGen_3121_ = lean_ctor_get(v___x_3117_, 3);
v_traceState_3122_ = lean_ctor_get(v___x_3117_, 4);
v_messages_3123_ = lean_ctor_get(v___x_3117_, 6);
v_infoState_3124_ = lean_ctor_get(v___x_3117_, 7);
v_snapshotTasks_3125_ = lean_ctor_get(v___x_3117_, 8);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v___x_3117_, 5);
lean_dec(v_unused_3151_);
v___x_3127_ = v___x_3117_;
v_isShared_3128_ = v_isSharedCheck_3150_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_snapshotTasks_3125_);
lean_inc(v_infoState_3124_);
lean_inc(v_messages_3123_);
lean_inc(v_traceState_3122_);
lean_inc(v_auxDeclNGen_3121_);
lean_inc(v_ngen_3120_);
lean_inc(v_nextMacroScope_3119_);
lean_inc(v_env_3118_);
lean_dec(v___x_3117_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3150_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
lean_inc(v_a_3112_);
v___x_3129_ = l_Lean_markMeta(v_env_3118_, v_a_3112_);
v___x_3130_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 5, v___x_3130_);
lean_ctor_set(v___x_3127_, 0, v___x_3129_);
v___x_3132_ = v___x_3127_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_nextMacroScope_3119_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_ngen_3120_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v_auxDeclNGen_3121_);
lean_ctor_set(v_reuseFailAlloc_3149_, 4, v_traceState_3122_);
lean_ctor_set(v_reuseFailAlloc_3149_, 5, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3149_, 6, v_messages_3123_);
lean_ctor_set(v_reuseFailAlloc_3149_, 7, v_infoState_3124_);
lean_ctor_set(v_reuseFailAlloc_3149_, 8, v_snapshotTasks_3125_);
v___x_3132_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v_mctx_3135_; lean_object* v_zetaDeltaFVarIds_3136_; lean_object* v_postponed_3137_; lean_object* v_diag_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3147_; 
v___x_3133_ = lean_st_ref_set(v___y_3098_, v___x_3132_);
v___x_3134_ = lean_st_ref_take(v___y_3095_);
v_mctx_3135_ = lean_ctor_get(v___x_3134_, 0);
v_zetaDeltaFVarIds_3136_ = lean_ctor_get(v___x_3134_, 2);
v_postponed_3137_ = lean_ctor_get(v___x_3134_, 3);
v_diag_3138_ = lean_ctor_get(v___x_3134_, 4);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v___x_3134_, 1);
lean_dec(v_unused_3148_);
v___x_3140_ = v___x_3134_;
v_isShared_3141_ = v_isSharedCheck_3147_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_diag_3138_);
lean_inc(v_postponed_3137_);
lean_inc(v_zetaDeltaFVarIds_3136_);
lean_inc(v_mctx_3135_);
lean_dec(v___x_3134_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3147_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v___x_3142_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_mctx_3135_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_zetaDeltaFVarIds_3136_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v_postponed_3137_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v_diag_3138_);
v___x_3144_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; 
v___x_3145_ = lean_st_ref_set(v___y_3095_, v___x_3144_);
v___y_3070_ = v_a_3114_;
v___y_3071_ = v_a_3112_;
v___y_3072_ = v___y_3096_;
v___y_3073_ = v___y_3098_;
goto v___jp_3069_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3112_);
return v___x_3113_;
}
}
else
{
lean_object* v___x_3153_; 
lean_dec_ref(v_expectedType_3033_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v_inst_3032_);
v___x_3153_ = v___x_3107_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_inst_3032_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v_expectedType_3033_);
lean_dec_ref(v_inst_3032_);
v_a_3156_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3104_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3104_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3033_);
lean_dec_ref(v_inst_3032_);
return v___x_3102_;
}
}
}
v___jp_3165_:
{
lean_object* v_options_3170_; uint8_t v_hasTrace_3171_; 
v_options_3170_ = lean_ctor_get(v___y_3168_, 2);
v_hasTrace_3171_ = lean_ctor_get_uint8(v_options_3170_, sizeof(void*)*1);
if (v_hasTrace_3171_ == 0)
{
v___y_3094_ = v___y_3166_;
v___y_3095_ = v___y_3167_;
v___y_3096_ = v___y_3168_;
v_options_3097_ = v_options_3170_;
v___y_3098_ = v___y_3169_;
goto v___jp_3093_;
}
else
{
lean_object* v_inheritedTraceOptions_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_inheritedTraceOptions_3172_ = lean_ctor_get(v___y_3168_, 13);
v___x_3173_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_3174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3172_, v_options_3170_, v___x_3173_);
if (v___x_3174_ == 0)
{
v___y_3094_ = v___y_3166_;
v___y_3095_ = v___y_3167_;
v___y_3096_ = v___y_3168_;
v_options_3097_ = v_options_3170_;
v___y_3098_ = v___y_3169_;
goto v___jp_3093_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3175_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_3032_);
v___x_3176_ = l_Lean_MessageData_ofExpr(v_inst_3032_);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3164_, v___x_3177_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_dec_ref(v___x_3178_);
v___y_3094_ = v___y_3166_;
v___y_3095_ = v___y_3167_;
v___y_3096_ = v___y_3168_;
v_options_3097_ = v_options_3170_;
v___y_3098_ = v___y_3169_;
goto v___jp_3093_;
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec_ref(v_expectedType_3033_);
lean_dec_ref(v_inst_3032_);
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
}
}
v___jp_3047_:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_enableRealizationsForConst(v___y_3049_, v___y_3050_, v___y_3051_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; 
v_unused_3060_ = lean_ctor_get(v___x_3052_, 0);
lean_dec(v_unused_3060_);
v___x_3054_ = v___x_3052_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v___x_3052_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___y_3048_);
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___y_3048_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v___y_3048_);
v_a_3061_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3052_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3052_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
v___jp_3069_:
{
if (v_compile_3035_ == 0)
{
v___y_3048_ = v___y_3070_;
v___y_3049_ = v___y_3071_;
v___y_3050_ = v___y_3072_;
v___y_3051_ = v___y_3073_;
goto v___jp_3047_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3074_ = lean_unsigned_to_nat(1u);
v___x_3075_ = lean_mk_empty_array_with_capacity(v___x_3074_);
lean_inc(v___y_3071_);
v___x_3076_ = lean_array_push(v___x_3075_, v___y_3071_);
v___x_3077_ = l_Lean_compileDecls(v___x_3076_, v_logCompileErrors_3036_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_dec_ref(v___x_3077_);
v___y_3048_ = v___y_3070_;
v___y_3049_ = v___y_3071_;
v___y_3050_ = v___y_3072_;
v___y_3051_ = v___y_3073_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10(lean_object* v_inst_3314_, lean_object* v_expectedType_3315_, uint8_t v___x_3316_, uint8_t v_compile_3317_, uint8_t v_logCompileErrors_3318_, uint8_t v_isMeta_3319_, lean_object* v_val_3320_, lean_object* v_x_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; 
if (lean_obj_tag(v_x_3321_) == 5)
{
lean_object* v_fn_3368_; lean_object* v_arg_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_fn_3368_ = lean_ctor_get(v_x_3321_, 0);
lean_inc_ref(v_fn_3368_);
v_arg_3369_ = lean_ctor_get(v_x_3321_, 1);
lean_inc_ref(v_arg_3369_);
lean_dec_ref(v_x_3321_);
v___x_3370_ = lean_array_set(v_x_3322_, v_x_3323_, v_arg_3369_);
v___x_3371_ = lean_unsigned_to_nat(1u);
v___x_3372_ = lean_nat_sub(v_x_3323_, v___x_3371_);
v___x_3373_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12(v_inst_3314_, v_expectedType_3315_, v___x_3316_, v_compile_3317_, v_logCompileErrors_3318_, v_isMeta_3319_, v_val_3320_, v_fn_3368_, v___x_3370_, v___x_3372_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
return v___x_3373_;
}
else
{
uint8_t v___x_3374_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v_options_3379_; lean_object* v___y_3380_; lean_object* v_cls_3446_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___x_3469_; 
v___x_3374_ = 1;
v_cls_3446_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3469_ = l_Lean_Expr_constName_x3f(v_x_3321_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_dec_ref(v_x_3322_);
lean_dec_ref(v_x_3321_);
lean_dec(v_val_3320_);
v___y_3448_ = v___y_3324_;
v___y_3449_ = v___y_3325_;
v___y_3450_ = v___y_3326_;
v___y_3451_ = v___y_3327_;
goto v___jp_3447_;
}
else
{
lean_object* v_val_3470_; lean_object* v___x_3471_; 
v_val_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_val_3470_);
lean_dec_ref(v___x_3469_);
v___x_3471_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3470_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref(v___x_3471_);
if (lean_obj_tag(v_a_3472_) == 6)
{
lean_object* v_val_3473_; lean_object* v___x_3474_; 
lean_dec_ref(v_inst_3314_);
v_val_3473_ = lean_ctor_get(v_a_3472_, 0);
lean_inc_ref(v_val_3473_);
lean_dec_ref(v_a_3472_);
lean_inc(v___y_3327_);
lean_inc_ref(v___y_3326_);
lean_inc(v___y_3325_);
lean_inc_ref(v___y_3324_);
lean_inc_ref(v_x_3321_);
v___x_3474_ = lean_infer_type(v_x_3321_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; uint8_t v___x_3476_; lean_object* v___x_3477_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = 0;
v___x_3477_ = l_Lean_Meta_forallMetaTelescope(v_a_3475_, v___x_3476_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v_snd_3479_; lean_object* v_fst_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3579_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v_snd_3479_ = lean_ctor_get(v_a_3478_, 1);
v_fst_3480_ = lean_ctor_get(v_a_3478_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_a_3478_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3482_ = v_a_3478_;
v_isShared_3483_ = v_isSharedCheck_3579_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_snd_3479_);
lean_inc(v_fst_3480_);
lean_dec(v_a_3478_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3579_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_snd_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3577_; 
v_snd_3484_ = lean_ctor_get(v_snd_3479_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_snd_3479_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v_snd_3479_, 0);
lean_dec(v_unused_3578_);
v___x_3486_ = v_snd_3479_;
v_isShared_3487_ = v_isSharedCheck_3577_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_snd_3484_);
lean_dec(v_snd_3479_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3577_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3488_ = lean_array_get_size(v_x_3322_);
v___x_3525_ = lean_array_get_size(v_fst_3480_);
v___x_3526_ = lean_nat_dec_eq(v___x_3488_, v___x_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
lean_dec(v_snd_3484_);
lean_dec(v_fst_3480_);
lean_dec_ref(v_val_3473_);
lean_dec(v_val_3320_);
lean_dec_ref(v_expectedType_3315_);
v___x_3527_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_3528_ = l_Lean_MessageData_ofExpr(v_x_3321_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set_tag(v___x_3486_, 7);
lean_ctor_set(v___x_3486_, 1, v___x_3528_);
lean_ctor_set(v___x_3486_, 0, v___x_3527_);
v___x_3530_ = v___x_3486_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3531_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3);
if (v_isShared_3483_ == 0)
{
lean_ctor_set_tag(v___x_3482_, 7);
lean_ctor_set(v___x_3482_, 1, v___x_3531_);
lean_ctor_set(v___x_3482_, 0, v___x_3530_);
v___x_3533_ = v___x_3482_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3534_ = lean_array_to_list(v_x_3322_);
v___x_3535_ = lean_box(0);
v___x_3536_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_3534_, v___x_3535_);
v___x_3537_ = l_Lean_MessageData_ofList(v___x_3536_);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3533_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3538_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
return v___x_3539_;
}
}
}
else
{
lean_object* v___x_3542_; 
lean_inc_ref(v_expectedType_3315_);
v___x_3542_ = l_Lean_Meta_isExprDefEq(v_expectedType_3315_, v_snd_3484_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; uint8_t v___x_3544_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref(v___x_3542_);
v___x_3544_ = lean_unbox(v_a_3543_);
lean_dec(v_a_3543_);
if (v___x_3544_ == 0)
{
lean_object* v_toConstantVal_3545_; lean_object* v_name_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; 
lean_dec(v_fst_3480_);
lean_dec_ref(v_x_3322_);
lean_dec_ref(v_x_3321_);
lean_dec(v_val_3320_);
v_toConstantVal_3545_ = lean_ctor_get(v_val_3473_, 0);
lean_inc_ref(v_toConstantVal_3545_);
lean_dec_ref(v_val_3473_);
v_name_3546_ = lean_ctor_get(v_toConstantVal_3545_, 0);
lean_inc(v_name_3546_);
lean_dec_ref(v_toConstantVal_3545_);
v___x_3547_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_3548_ = l_Lean_MessageData_ofExpr(v_expectedType_3315_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set_tag(v___x_3486_, 7);
lean_ctor_set(v___x_3486_, 1, v___x_3548_);
lean_ctor_set(v___x_3486_, 0, v___x_3547_);
v___x_3550_ = v___x_3486_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3551_; lean_object* v___x_3553_; 
v___x_3551_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_3483_ == 0)
{
lean_ctor_set_tag(v___x_3482_, 7);
lean_ctor_set(v___x_3482_, 1, v___x_3551_);
lean_ctor_set(v___x_3482_, 0, v___x_3550_);
v___x_3553_ = v___x_3482_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
v___x_3554_ = l_Lean_MessageData_ofConstName(v_name_3546_, v___x_3316_);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3553_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_3557_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
else
{
lean_del_object(v___x_3486_);
lean_del_object(v___x_3482_);
v___y_3490_ = v___y_3324_;
v___y_3491_ = v___y_3325_;
v___y_3492_ = v___y_3326_;
v___y_3493_ = v___y_3327_;
goto v___jp_3489_;
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_del_object(v___x_3486_);
lean_del_object(v___x_3482_);
lean_dec(v_fst_3480_);
lean_dec_ref(v_val_3473_);
lean_dec_ref(v_x_3322_);
lean_dec_ref(v_x_3321_);
lean_dec(v_val_3320_);
lean_dec_ref(v_expectedType_3315_);
v_a_3569_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3542_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3542_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
v___jp_3489_:
{
lean_object* v_numParams_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_numParams_3494_ = lean_ctor_get(v_val_3473_, 3);
lean_inc(v_numParams_3494_);
lean_dec_ref(v_val_3473_);
v___x_3495_ = lean_box(0);
v___x_3496_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(v___x_3488_, v_fst_3480_, v_x_3322_, v_compile_3317_, v_logCompileErrors_3318_, v___x_3316_, v_isMeta_3319_, v_val_3320_, v_expectedType_3315_, v_numParams_3494_, v___x_3495_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec_ref(v_x_3322_);
if (lean_obj_tag(v___x_3496_) == 0)
{
size_t v_sz_3497_; size_t v___x_3498_; lean_object* v___x_3499_; 
lean_dec_ref(v___x_3496_);
v_sz_3497_ = lean_array_size(v_fst_3480_);
v___x_3498_ = ((size_t)0ULL);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_3497_, v___x_3498_, v_fst_3480_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3508_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v___x_3506_; 
v___x_3504_ = l_Lean_mkAppN(v_x_3321_, v_a_3500_);
lean_dec(v_a_3500_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3504_);
v___x_3506_ = v___x_3502_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec_ref(v_x_3321_);
v_a_3509_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3499_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3499_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec(v_fst_3480_);
lean_dec_ref(v_x_3321_);
v_a_3517_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3496_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3496_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v_val_3473_);
lean_dec_ref(v_x_3322_);
lean_dec_ref(v_x_3321_);
lean_dec(v_val_3320_);
lean_dec_ref(v_expectedType_3315_);
v_a_3580_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3477_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3477_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_dec_ref(v_val_3473_);
lean_dec_ref(v_x_3322_);
lean_dec_ref(v_x_3321_);
lean_dec(v_val_3320_);
lean_dec_ref(v_expectedType_3315_);
return v___x_3474_;
}
}
else
{
lean_dec(v_a_3472_);
lean_dec_ref(v_x_3322_);
lean_dec_ref(v_x_3321_);
lean_dec(v_val_3320_);
v___y_3448_ = v___y_3324_;
v___y_3449_ = v___y_3325_;
v___y_3450_ = v___y_3326_;
v___y_3451_ = v___y_3327_;
goto v___jp_3447_;
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v_x_3322_);
lean_dec_ref(v_x_3321_);
lean_dec(v_val_3320_);
lean_dec_ref(v_expectedType_3315_);
lean_dec_ref(v_inst_3314_);
v_a_3588_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3471_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3471_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
v___jp_3375_:
{
lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3381_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3382_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3379_, v___x_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; 
lean_dec_ref(v_expectedType_3315_);
v___x_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3383_, 0, v_inst_3314_);
return v___x_3383_;
}
else
{
lean_object* v___x_3384_; 
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3378_);
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
lean_inc_ref(v_inst_3314_);
v___x_3384_ = lean_infer_type(v_inst_3314_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3380_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v___x_3384_);
lean_inc_ref(v_expectedType_3315_);
v___x_3386_ = l_Lean_Meta_isExprDefEq(v_expectedType_3315_, v_a_3385_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3380_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3437_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3437_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3437_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
uint8_t v___x_3391_; 
v___x_3391_ = lean_unbox(v_a_3387_);
lean_dec(v_a_3387_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v_a_3394_; lean_object* v___x_3395_; 
lean_del_object(v___x_3389_);
v___x_3392_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_3393_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3392_, v___y_3380_);
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc_n(v_a_3394_, 2);
lean_dec_ref(v___x_3393_);
v___x_3395_ = l_Lean_Meta_mkAuxDefinition(v_a_3394_, v_expectedType_3315_, v_inst_3314_, v___x_3316_, v___x_3316_, v___x_3374_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3380_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v_a_3396_; uint8_t v___x_3397_; lean_object* v___x_3398_; 
v_a_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_a_3396_);
lean_dec_ref(v___x_3395_);
v___x_3397_ = 3;
lean_inc(v_a_3394_);
v___x_3398_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3394_, v___x_3397_, v___y_3377_, v___y_3380_);
lean_dec_ref(v___x_3398_);
if (v_isMeta_3319_ == 0)
{
v___y_3352_ = v_a_3396_;
v___y_3353_ = v_a_3394_;
v___y_3354_ = v___y_3378_;
v___y_3355_ = v___y_3380_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3399_; lean_object* v_env_3400_; lean_object* v_nextMacroScope_3401_; lean_object* v_ngen_3402_; lean_object* v_auxDeclNGen_3403_; lean_object* v_traceState_3404_; lean_object* v_messages_3405_; lean_object* v_infoState_3406_; lean_object* v_snapshotTasks_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3432_; 
v___x_3399_ = lean_st_ref_take(v___y_3380_);
v_env_3400_ = lean_ctor_get(v___x_3399_, 0);
v_nextMacroScope_3401_ = lean_ctor_get(v___x_3399_, 1);
v_ngen_3402_ = lean_ctor_get(v___x_3399_, 2);
v_auxDeclNGen_3403_ = lean_ctor_get(v___x_3399_, 3);
v_traceState_3404_ = lean_ctor_get(v___x_3399_, 4);
v_messages_3405_ = lean_ctor_get(v___x_3399_, 6);
v_infoState_3406_ = lean_ctor_get(v___x_3399_, 7);
v_snapshotTasks_3407_ = lean_ctor_get(v___x_3399_, 8);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; 
v_unused_3433_ = lean_ctor_get(v___x_3399_, 5);
lean_dec(v_unused_3433_);
v___x_3409_ = v___x_3399_;
v_isShared_3410_ = v_isSharedCheck_3432_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_snapshotTasks_3407_);
lean_inc(v_infoState_3406_);
lean_inc(v_messages_3405_);
lean_inc(v_traceState_3404_);
lean_inc(v_auxDeclNGen_3403_);
lean_inc(v_ngen_3402_);
lean_inc(v_nextMacroScope_3401_);
lean_inc(v_env_3400_);
lean_dec(v___x_3399_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3432_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
lean_inc(v_a_3394_);
v___x_3411_ = l_Lean_markMeta(v_env_3400_, v_a_3394_);
v___x_3412_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 5, v___x_3412_);
lean_ctor_set(v___x_3409_, 0, v___x_3411_);
v___x_3414_ = v___x_3409_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_nextMacroScope_3401_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_ngen_3402_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_auxDeclNGen_3403_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v_traceState_3404_);
lean_ctor_set(v_reuseFailAlloc_3431_, 5, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3431_, 6, v_messages_3405_);
lean_ctor_set(v_reuseFailAlloc_3431_, 7, v_infoState_3406_);
lean_ctor_set(v_reuseFailAlloc_3431_, 8, v_snapshotTasks_3407_);
v___x_3414_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v_mctx_3417_; lean_object* v_zetaDeltaFVarIds_3418_; lean_object* v_postponed_3419_; lean_object* v_diag_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3429_; 
v___x_3415_ = lean_st_ref_set(v___y_3380_, v___x_3414_);
v___x_3416_ = lean_st_ref_take(v___y_3377_);
v_mctx_3417_ = lean_ctor_get(v___x_3416_, 0);
v_zetaDeltaFVarIds_3418_ = lean_ctor_get(v___x_3416_, 2);
v_postponed_3419_ = lean_ctor_get(v___x_3416_, 3);
v_diag_3420_ = lean_ctor_get(v___x_3416_, 4);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; 
v_unused_3430_ = lean_ctor_get(v___x_3416_, 1);
lean_dec(v_unused_3430_);
v___x_3422_ = v___x_3416_;
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_diag_3420_);
lean_inc(v_postponed_3419_);
lean_inc(v_zetaDeltaFVarIds_3418_);
lean_inc(v_mctx_3417_);
lean_dec(v___x_3416_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3424_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v___x_3424_);
v___x_3426_ = v___x_3422_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_mctx_3417_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3428_, 2, v_zetaDeltaFVarIds_3418_);
lean_ctor_set(v_reuseFailAlloc_3428_, 3, v_postponed_3419_);
lean_ctor_set(v_reuseFailAlloc_3428_, 4, v_diag_3420_);
v___x_3426_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_st_ref_set(v___y_3377_, v___x_3426_);
v___y_3352_ = v_a_3396_;
v___y_3353_ = v_a_3394_;
v___y_3354_ = v___y_3378_;
v___y_3355_ = v___y_3380_;
goto v___jp_3351_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3394_);
return v___x_3395_;
}
}
else
{
lean_object* v___x_3435_; 
lean_dec_ref(v_expectedType_3315_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v_inst_3314_);
v___x_3435_ = v___x_3389_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_inst_3314_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_expectedType_3315_);
lean_dec_ref(v_inst_3314_);
v_a_3438_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3386_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3386_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3315_);
lean_dec_ref(v_inst_3314_);
return v___x_3384_;
}
}
}
v___jp_3447_:
{
lean_object* v_options_3452_; uint8_t v_hasTrace_3453_; 
v_options_3452_ = lean_ctor_get(v___y_3450_, 2);
v_hasTrace_3453_ = lean_ctor_get_uint8(v_options_3452_, sizeof(void*)*1);
if (v_hasTrace_3453_ == 0)
{
v___y_3376_ = v___y_3448_;
v___y_3377_ = v___y_3449_;
v___y_3378_ = v___y_3450_;
v_options_3379_ = v_options_3452_;
v___y_3380_ = v___y_3451_;
goto v___jp_3375_;
}
else
{
lean_object* v_inheritedTraceOptions_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v_inheritedTraceOptions_3454_ = lean_ctor_get(v___y_3450_, 13);
v___x_3455_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_3456_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3454_, v_options_3452_, v___x_3455_);
if (v___x_3456_ == 0)
{
v___y_3376_ = v___y_3448_;
v___y_3377_ = v___y_3449_;
v___y_3378_ = v___y_3450_;
v_options_3379_ = v_options_3452_;
v___y_3380_ = v___y_3451_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3457_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_3314_);
v___x_3458_ = l_Lean_MessageData_ofExpr(v_inst_3314_);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3446_, v___x_3459_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_dec_ref(v___x_3460_);
v___y_3376_ = v___y_3448_;
v___y_3377_ = v___y_3449_;
v___y_3378_ = v___y_3450_;
v_options_3379_ = v_options_3452_;
v___y_3380_ = v___y_3451_;
goto v___jp_3375_;
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v_expectedType_3315_);
lean_dec_ref(v_inst_3314_);
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3460_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3460_);
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
}
}
}
v___jp_3329_:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_enableRealizationsForConst(v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; 
v_unused_3342_ = lean_ctor_get(v___x_3334_, 0);
lean_dec(v_unused_3342_);
v___x_3336_ = v___x_3334_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v___x_3334_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___y_3330_);
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___y_3330_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec_ref(v___y_3330_);
v_a_3343_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3334_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3334_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
v___jp_3351_:
{
if (v_compile_3317_ == 0)
{
v___y_3330_ = v___y_3352_;
v___y_3331_ = v___y_3353_;
v___y_3332_ = v___y_3354_;
v___y_3333_ = v___y_3355_;
goto v___jp_3329_;
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_mk_empty_array_with_capacity(v___x_3356_);
lean_inc(v___y_3353_);
v___x_3358_ = lean_array_push(v___x_3357_, v___y_3353_);
v___x_3359_ = l_Lean_compileDecls(v___x_3358_, v_logCompileErrors_3318_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_dec_ref(v___x_3359_);
v___y_3330_ = v___y_3352_;
v___y_3331_ = v___y_3353_;
v___y_3332_ = v___y_3354_;
v___y_3333_ = v___y_3355_;
goto v___jp_3329_;
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3359_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3359_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
}
}
static double _init_l_Lean_Meta_wrapInstance___closed__1(void){
_start:
{
lean_object* v___x_3596_; double v___x_3597_; 
v___x_3596_ = lean_unsigned_to_nat(1000000000u);
v___x_3597_ = lean_float_of_nat(v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(lean_object* v_upperBound_3598_, lean_object* v_fst_3599_, lean_object* v_args_3600_, uint8_t v___x_3601_, uint8_t v_compile_3602_, uint8_t v_logCompileErrors_3603_, uint8_t v___x_3604_, uint8_t v_isMeta_3605_, lean_object* v_val_3606_, lean_object* v_expectedType_3607_, lean_object* v_a_3608_, lean_object* v_b_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_a_3616_; lean_object* v___y_3621_; uint8_t v___x_3640_; 
v___x_3640_ = lean_nat_dec_lt(v_a_3608_, v_upperBound_3598_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; 
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v___x_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3641_, 0, v_b_3609_);
return v___x_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_array_fget_borrowed(v_fst_3599_, v_a_3608_);
v___x_3643_ = l_Lean_Expr_mvarId_x21(v___x_3642_);
lean_inc(v___x_3643_);
v___x_3644_ = l_Lean_MVarId_getDecl(v___x_3643_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v_userName_3646_; lean_object* v_type_3647_; lean_object* v___x_3648_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3644_);
v_userName_3646_ = lean_ctor_get(v_a_3645_, 0);
lean_inc(v_userName_3646_);
v_type_3647_ = lean_ctor_get(v_a_3645_, 2);
lean_inc_ref(v_type_3647_);
lean_dec(v_a_3645_);
v___x_3648_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_type_3647_, v___y_3611_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc_n(v_a_3649_, 2);
lean_dec_ref(v___x_3648_);
v___x_3650_ = l_Lean_Meta_isProp(v_a_3649_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v_cls_3653_; lean_object* v___f_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = lean_box(0);
v_cls_3653_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_3654_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0));
v___x_3655_ = lean_array_fget_borrowed(v_args_3600_, v_a_3608_);
v___x_3656_ = lean_unbox(v_a_3651_);
lean_dec(v_a_3651_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
lean_inc(v_a_3649_);
v___x_3657_ = l_Lean_Meta_isClass_x3f(v_a_3649_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3756_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3756_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3756_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v_a_3663_; lean_object* v___y_3666_; uint8_t v___y_3667_; lean_object* v_a_3672_; lean_object* v___y_3676_; 
if (lean_obj_tag(v_a_3658_) == 0)
{
if (v___x_3604_ == 0)
{
lean_object* v_options_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___f_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
lean_del_object(v___x_3660_);
v_options_3702_ = lean_ctor_get(v___y_3612_, 2);
v___x_3703_ = lean_box(v___x_3604_);
v___x_3704_ = lean_box(v___x_3601_);
v___x_3705_ = lean_box(v_compile_3602_);
v___x_3706_ = lean_box(v_logCompileErrors_3603_);
v___x_3707_ = lean_box(v_isMeta_3605_);
lean_inc(v_a_3649_);
lean_inc(v___x_3655_);
lean_inc(v___x_3643_);
v___f_3708_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_3708_, 0, v___x_3643_);
lean_closure_set(v___f_3708_, 1, v___x_3655_);
lean_closure_set(v___f_3708_, 2, v___x_3652_);
lean_closure_set(v___f_3708_, 3, v_a_3649_);
lean_closure_set(v___f_3708_, 4, v___x_3703_);
lean_closure_set(v___f_3708_, 5, v___x_3704_);
lean_closure_set(v___f_3708_, 6, v___x_3705_);
lean_closure_set(v___f_3708_, 7, v___x_3706_);
lean_closure_set(v___f_3708_, 8, v___x_3707_);
v___x_3709_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3710_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3702_, v___x_3709_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; 
lean_dec_ref(v___f_3708_);
lean_dec(v_userName_3646_);
lean_inc(v___x_3655_);
v___x_3711_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_3643_, v___x_3655_, v___x_3652_, v_a_3649_, v___x_3604_, v___x_3601_, v_compile_3602_, v_logCompileErrors_3603_, v_isMeta_3605_, v___x_3652_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3711_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3712_; 
lean_inc(v_userName_3646_);
lean_inc(v_val_3606_);
v___x_3712_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_3606_, v_userName_3646_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v_fst_3714_; lean_object* v_snd_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3747_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3712_);
v_fst_3714_ = lean_ctor_get(v_a_3713_, 0);
v_snd_3715_ = lean_ctor_get(v_a_3713_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_a_3713_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3717_ = v_a_3713_;
v_isShared_3718_ = v_isSharedCheck_3747_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_snd_3715_);
lean_inc(v_fst_3714_);
lean_dec(v_a_3713_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3747_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
uint8_t v___x_3719_; 
v___x_3719_ = lean_name_eq(v_fst_3714_, v_val_3606_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
lean_dec(v_a_3649_);
v___x_3720_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3653_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; uint8_t v___x_3722_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref(v___x_3720_);
v___x_3722_ = lean_unbox(v_a_3721_);
lean_dec(v_a_3721_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; 
lean_del_object(v___x_3717_);
lean_dec(v_userName_3646_);
lean_inc_ref(v_expectedType_3607_);
lean_inc(v_val_3606_);
v___x_3723_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_3606_, v_fst_3714_, v_expectedType_3607_, v___f_3654_, v___f_3708_, v___x_3652_, v_cls_3653_, v_snd_3715_, v___x_3643_, v___x_3652_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3723_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3724_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4);
v___x_3725_ = l_Lean_MessageData_ofName(v_userName_3646_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set_tag(v___x_3717_, 7);
lean_ctor_set(v___x_3717_, 1, v___x_3725_);
lean_ctor_set(v___x_3717_, 0, v___x_3724_);
v___x_3727_ = v___x_3717_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3728_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
lean_inc(v_fst_3714_);
v___x_3730_ = l_Lean_MessageData_ofName(v_fst_3714_);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3653_, v___x_3733_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3736_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref(v___x_3734_);
lean_inc_ref(v_expectedType_3607_);
lean_inc(v_val_3606_);
v___x_3736_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__3(v_val_3606_, v_fst_3714_, v_expectedType_3607_, v___f_3654_, v___f_3708_, v___x_3652_, v_cls_3653_, v_snd_3715_, v___x_3643_, v_a_3735_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3736_;
goto v___jp_3620_;
}
else
{
lean_dec(v_snd_3715_);
lean_dec(v_fst_3714_);
lean_dec_ref(v___f_3708_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_del_object(v___x_3717_);
lean_dec(v_snd_3715_);
lean_dec(v_fst_3714_);
lean_dec_ref(v___f_3708_);
lean_dec(v_userName_3646_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3738_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3720_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3720_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v___x_3746_; 
lean_del_object(v___x_3717_);
lean_dec(v_snd_3715_);
lean_dec(v_fst_3714_);
lean_dec_ref(v___f_3708_);
lean_dec(v_userName_3646_);
lean_inc(v___x_3655_);
v___x_3746_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_3643_, v___x_3655_, v___x_3652_, v_a_3649_, v___x_3604_, v___x_3601_, v_compile_3602_, v_logCompileErrors_3603_, v_isMeta_3605_, v___x_3652_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3746_;
goto v___jp_3620_;
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec_ref(v___f_3708_);
lean_dec(v_a_3649_);
lean_dec(v_userName_3646_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3748_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3712_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3712_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
else
{
lean_dec(v_userName_3646_);
goto v___jp_3680_;
}
}
else
{
lean_dec_ref(v_a_3658_);
lean_dec(v_userName_3646_);
goto v___jp_3680_;
}
v___jp_3662_:
{
lean_object* v___x_3664_; 
lean_inc(v___x_3655_);
v___x_3664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_3655_, v_a_3649_, v_compile_3602_, v_logCompileErrors_3603_, v_isMeta_3605_, v___x_3643_, v___x_3652_, v_a_3663_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3664_;
goto v___jp_3620_;
}
v___jp_3665_:
{
if (v___y_3667_ == 0)
{
lean_dec_ref(v___y_3666_);
lean_del_object(v___x_3660_);
v_a_3663_ = v___x_3652_;
goto v___jp_3662_;
}
else
{
lean_object* v___x_3669_; 
lean_dec(v_a_3649_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set_tag(v___x_3660_, 1);
lean_ctor_set(v___x_3660_, 0, v___y_3666_);
v___x_3669_ = v___x_3660_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___y_3666_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
v___jp_3671_:
{
uint8_t v___x_3673_; 
v___x_3673_ = l_Lean_Exception_isInterrupt(v_a_3672_);
if (v___x_3673_ == 0)
{
uint8_t v___x_3674_; 
lean_inc_ref(v_a_3672_);
v___x_3674_ = l_Lean_Exception_isRuntime(v_a_3672_);
v___y_3666_ = v_a_3672_;
v___y_3667_ = v___x_3674_;
goto v___jp_3665_;
}
else
{
v___y_3666_ = v_a_3672_;
v___y_3667_ = v___x_3673_;
goto v___jp_3665_;
}
}
v___jp_3675_:
{
if (lean_obj_tag(v___y_3676_) == 0)
{
lean_object* v_a_3677_; 
lean_del_object(v___x_3660_);
v_a_3677_ = lean_ctor_get(v___y_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref(v___y_3676_);
if (lean_obj_tag(v_a_3677_) == 0)
{
lean_dec(v_a_3649_);
lean_dec(v___x_3643_);
v_a_3616_ = v___x_3652_;
goto v___jp_3615_;
}
else
{
lean_object* v_a_3678_; 
v_a_3678_ = lean_ctor_get(v_a_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v_a_3677_);
v_a_3663_ = v_a_3678_;
goto v___jp_3662_;
}
}
else
{
lean_object* v_a_3679_; 
v_a_3679_ = lean_ctor_get(v___y_3676_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___y_3676_);
v_a_3672_ = v_a_3679_;
goto v___jp_3671_;
}
}
v___jp_3680_:
{
lean_object* v_options_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v_options_3681_ = lean_ctor_get(v___y_3612_, 2);
v___x_3682_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3683_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3681_, v___x_3682_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; 
lean_del_object(v___x_3660_);
lean_inc(v___x_3655_);
v___x_3684_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_3655_, v_a_3649_, v_compile_3602_, v_logCompileErrors_3603_, v_isMeta_3605_, v___x_3643_, v___x_3652_, v___x_3652_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3684_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = lean_box(0);
lean_inc(v_a_3649_);
v___x_3686_ = l_Lean_Meta_trySynthInstance(v_a_3649_, v___x_3685_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref(v___x_3686_);
if (lean_obj_tag(v_a_3687_) == 1)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
v_a_3688_ = lean_ctor_get(v_a_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref(v_a_3687_);
v___x_3689_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3653_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; uint8_t v___x_3691_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref(v___x_3689_);
v___x_3691_ = lean_unbox(v_a_3690_);
lean_dec(v_a_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; 
lean_inc(v___x_3643_);
v___x_3692_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_3643_, v_a_3688_, v___x_3652_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3676_ = v___x_3692_;
goto v___jp_3675_;
}
else
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3693_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2);
lean_inc(v_a_3688_);
v___x_3694_ = l_Lean_MessageData_ofExpr(v_a_3688_);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3653_, v___x_3695_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3698_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref(v___x_3696_);
lean_inc(v___x_3643_);
v___x_3698_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_3643_, v_a_3688_, v_a_3697_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3676_ = v___x_3698_;
goto v___jp_3675_;
}
else
{
lean_object* v_a_3699_; 
lean_dec(v_a_3688_);
v_a_3699_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3699_);
lean_dec_ref(v___x_3696_);
v_a_3672_ = v_a_3699_;
goto v___jp_3671_;
}
}
}
else
{
lean_object* v_a_3700_; 
lean_dec(v_a_3688_);
v_a_3700_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3700_);
lean_dec_ref(v___x_3689_);
v_a_3672_ = v_a_3700_;
goto v___jp_3671_;
}
}
else
{
lean_dec(v_a_3687_);
lean_del_object(v___x_3660_);
v_a_3663_ = v___x_3652_;
goto v___jp_3662_;
}
}
else
{
lean_object* v_a_3701_; 
v_a_3701_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3701_);
lean_dec_ref(v___x_3686_);
v_a_3672_ = v_a_3701_;
goto v___jp_3671_;
}
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_a_3649_);
lean_dec(v_userName_3646_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3757_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3657_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3657_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v___x_3765_; 
lean_dec(v_userName_3646_);
lean_inc(v___y_3613_);
lean_inc_ref(v___y_3612_);
lean_inc(v___y_3611_);
lean_inc_ref(v___y_3610_);
lean_inc(v___x_3655_);
v___x_3765_ = lean_infer_type(v___x_3655_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3767_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc_n(v_a_3766_, 2);
lean_dec_ref(v___x_3765_);
lean_inc(v_a_3649_);
v___x_3767_ = l_Lean_Meta_isExprDefEq(v_a_3649_, v_a_3766_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___f_3769_; uint8_t v___x_3770_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref(v___x_3767_);
v___f_3769_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7));
v___x_3770_ = lean_unbox(v_a_3768_);
lean_dec(v_a_3768_);
if (v___x_3770_ == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3653_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; uint8_t v___x_3773_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref(v___x_3771_);
v___x_3773_ = lean_unbox(v_a_3772_);
lean_dec(v_a_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; 
lean_dec(v_a_3766_);
lean_inc(v___x_3655_);
v___x_3774_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_3649_, v___x_3655_, v___x_3601_, v___x_3643_, v___f_3769_, v___x_3652_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3774_;
goto v___jp_3620_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3775_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9);
lean_inc(v_a_3608_);
v___x_3776_ = l_Nat_reprFast(v_a_3608_);
v___x_3777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
v___x_3778_ = l_Lean_MessageData_ofFormat(v___x_3777_);
v___x_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3775_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11);
v___x_3781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3779_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
lean_inc(v_a_3649_);
v___x_3782_ = l_Lean_MessageData_ofExpr(v_a_3649_);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = l_Lean_MessageData_ofExpr(v_a_3766_);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15);
v___x_3789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
lean_inc(v___x_3655_);
v___x_3790_ = l_Lean_MessageData_ofExpr(v___x_3655_);
v___x_3791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3653_, v___x_3791_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3792_);
lean_inc(v___x_3655_);
v___x_3794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_3649_, v___x_3655_, v___x_3601_, v___x_3643_, v___f_3769_, v_a_3793_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3794_;
goto v___jp_3620_;
}
else
{
lean_dec(v_a_3649_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
return v___x_3792_;
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec(v_a_3766_);
lean_dec(v_a_3649_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3795_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3771_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3771_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
else
{
lean_object* v___x_3803_; 
lean_dec(v_a_3766_);
lean_dec(v_a_3649_);
lean_inc(v___x_3655_);
v___x_3803_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3643_, v___x_3655_, v___y_3611_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_3652_, v_a_3804_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
v___y_3621_ = v___x_3805_;
goto v___jp_3620_;
}
else
{
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
return v___x_3803_;
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v_a_3766_);
lean_dec(v_a_3649_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3806_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3767_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3767_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_a_3649_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3814_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3765_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3765_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec(v_a_3649_);
lean_dec(v_userName_3646_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3822_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3650_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3650_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_dec(v_userName_3646_);
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3830_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3648_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3648_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec(v___x_3643_);
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3838_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3644_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3644_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
v___jp_3615_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = lean_unsigned_to_nat(1u);
v___x_3618_ = lean_nat_add(v_a_3608_, v___x_3617_);
lean_dec(v_a_3608_);
v_a_3608_ = v___x_3618_;
v_b_3609_ = v_a_3616_;
goto _start;
}
v___jp_3620_:
{
if (lean_obj_tag(v___y_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3631_; 
v_a_3622_ = lean_ctor_get(v___y_3621_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___y_3621_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3624_ = v___y_3621_;
v_isShared_3625_ = v_isSharedCheck_3631_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___y_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3631_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
if (lean_obj_tag(v_a_3622_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3628_; 
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3626_ = lean_ctor_get(v_a_3622_, 0);
lean_inc(v_a_3626_);
lean_dec_ref(v_a_3622_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v_a_3626_);
v___x_3628_ = v___x_3624_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
else
{
lean_object* v_a_3630_; 
lean_del_object(v___x_3624_);
v_a_3630_ = lean_ctor_get(v_a_3622_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v_a_3622_);
v_a_3616_ = v_a_3630_;
goto v___jp_3615_;
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_a_3608_);
lean_dec_ref(v_expectedType_3607_);
lean_dec(v_val_3606_);
v_a_3632_ = lean_ctor_get(v___y_3621_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___y_3621_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___y_3621_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___y_3621_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object* v_upperBound_3846_, lean_object* v_fst_3847_, lean_object* v_args_3848_, uint8_t v___x_3849_, uint8_t v_compile_3850_, uint8_t v_logCompileErrors_3851_, uint8_t v___x_3852_, uint8_t v_isMeta_3853_, lean_object* v_val_3854_, lean_object* v_expectedType_3855_, lean_object* v_a_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_a_3864_; lean_object* v___y_3869_; uint8_t v___x_3888_; 
v___x_3888_ = lean_nat_dec_lt(v_a_3856_, v_upperBound_3846_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v_b_3857_);
return v___x_3889_;
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3890_ = lean_array_fget_borrowed(v_fst_3847_, v_a_3856_);
v___x_3891_ = l_Lean_Expr_mvarId_x21(v___x_3890_);
lean_inc(v___x_3891_);
v___x_3892_ = l_Lean_MVarId_getDecl(v___x_3891_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v_userName_3894_; lean_object* v_type_3895_; lean_object* v___x_3896_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref(v___x_3892_);
v_userName_3894_ = lean_ctor_get(v_a_3893_, 0);
lean_inc(v_userName_3894_);
v_type_3895_ = lean_ctor_get(v_a_3893_, 2);
lean_inc_ref(v_type_3895_);
lean_dec(v_a_3893_);
v___x_3896_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_type_3895_, v___y_3859_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc_n(v_a_3897_, 2);
lean_dec_ref(v___x_3896_);
v___x_3898_ = l_Lean_Meta_isProp(v_a_3897_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; lean_object* v_cls_3901_; lean_object* v___f_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3898_);
v___x_3900_ = lean_box(0);
v_cls_3901_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_3902_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0));
v___x_3903_ = lean_array_fget_borrowed(v_args_3848_, v_a_3856_);
v___x_3904_ = lean_unbox(v_a_3899_);
lean_dec(v_a_3899_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; 
lean_inc(v_a_3897_);
v___x_3905_ = l_Lean_Meta_isClass_x3f(v_a_3897_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_4004_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3908_ = v___x_3905_;
v_isShared_3909_ = v_isSharedCheck_4004_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3905_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_4004_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v_a_3911_; lean_object* v___y_3914_; uint8_t v___y_3915_; lean_object* v_a_3920_; lean_object* v___y_3924_; 
if (lean_obj_tag(v_a_3906_) == 0)
{
if (v___x_3852_ == 0)
{
lean_object* v_options_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___f_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
lean_del_object(v___x_3908_);
v_options_3950_ = lean_ctor_get(v___y_3860_, 2);
v___x_3951_ = lean_box(v___x_3852_);
v___x_3952_ = lean_box(v___x_3849_);
v___x_3953_ = lean_box(v_compile_3850_);
v___x_3954_ = lean_box(v_logCompileErrors_3851_);
v___x_3955_ = lean_box(v_isMeta_3853_);
lean_inc(v_a_3897_);
lean_inc(v___x_3903_);
lean_inc(v___x_3891_);
v___f_3956_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___boxed), 15, 9);
lean_closure_set(v___f_3956_, 0, v___x_3891_);
lean_closure_set(v___f_3956_, 1, v___x_3903_);
lean_closure_set(v___f_3956_, 2, v___x_3900_);
lean_closure_set(v___f_3956_, 3, v_a_3897_);
lean_closure_set(v___f_3956_, 4, v___x_3951_);
lean_closure_set(v___f_3956_, 5, v___x_3952_);
lean_closure_set(v___f_3956_, 6, v___x_3953_);
lean_closure_set(v___f_3956_, 7, v___x_3954_);
lean_closure_set(v___f_3956_, 8, v___x_3955_);
v___x_3957_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3958_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3950_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
lean_dec_ref(v___f_3956_);
lean_dec(v_userName_3894_);
lean_inc(v___x_3903_);
v___x_3959_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_3891_, v___x_3903_, v___x_3900_, v_a_3897_, v___x_3852_, v___x_3849_, v_compile_3850_, v_logCompileErrors_3851_, v_isMeta_3853_, v___x_3900_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_3959_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3960_; 
lean_inc(v_userName_3894_);
lean_inc(v_val_3854_);
v___x_3960_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_3854_, v_userName_3894_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v_fst_3962_; lean_object* v_snd_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3995_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref(v___x_3960_);
v_fst_3962_ = lean_ctor_get(v_a_3961_, 0);
v_snd_3963_ = lean_ctor_get(v_a_3961_, 1);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_a_3961_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3965_ = v_a_3961_;
v_isShared_3966_ = v_isSharedCheck_3995_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_snd_3963_);
lean_inc(v_fst_3962_);
lean_dec(v_a_3961_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3995_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
uint8_t v___x_3967_; 
v___x_3967_ = lean_name_eq(v_fst_3962_, v_val_3854_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
lean_dec(v_a_3897_);
v___x_3968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3901_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; uint8_t v___x_3970_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref(v___x_3968_);
v___x_3970_ = lean_unbox(v_a_3969_);
lean_dec(v_a_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; 
lean_del_object(v___x_3965_);
lean_dec(v_userName_3894_);
lean_inc_ref(v_expectedType_3855_);
lean_inc(v_val_3854_);
v___x_3971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5(v_val_3854_, v_fst_3962_, v_expectedType_3855_, v___f_3902_, v___f_3956_, v___x_3900_, v_cls_3901_, v_snd_3963_, v___x_3891_, v___x_3900_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_3971_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3972_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4);
v___x_3973_ = l_Lean_MessageData_ofName(v_userName_3894_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set_tag(v___x_3965_, 7);
lean_ctor_set(v___x_3965_, 1, v___x_3973_);
lean_ctor_set(v___x_3965_, 0, v___x_3972_);
v___x_3975_ = v___x_3965_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3976_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6);
v___x_3977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
lean_inc(v_fst_3962_);
v___x_3978_ = l_Lean_MessageData_ofName(v_fst_3962_);
v___x_3979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_3981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3979_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v___x_3982_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3901_, v___x_3981_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v___x_3984_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref(v___x_3982_);
lean_inc_ref(v_expectedType_3855_);
lean_inc(v_val_3854_);
v___x_3984_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5(v_val_3854_, v_fst_3962_, v_expectedType_3855_, v___f_3902_, v___f_3956_, v___x_3900_, v_cls_3901_, v_snd_3963_, v___x_3891_, v_a_3983_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_3984_;
goto v___jp_3868_;
}
else
{
lean_dec(v_snd_3963_);
lean_dec(v_fst_3962_);
lean_dec_ref(v___f_3956_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
return v___x_3982_;
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_del_object(v___x_3965_);
lean_dec(v_snd_3963_);
lean_dec(v_fst_3962_);
lean_dec_ref(v___f_3956_);
lean_dec(v_userName_3894_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_3986_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3968_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3968_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
lean_object* v___x_3994_; 
lean_del_object(v___x_3965_);
lean_dec(v_snd_3963_);
lean_dec(v_fst_3962_);
lean_dec_ref(v___f_3956_);
lean_dec(v_userName_3894_);
lean_inc(v___x_3903_);
v___x_3994_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1(v___x_3891_, v___x_3903_, v___x_3900_, v_a_3897_, v___x_3852_, v___x_3849_, v_compile_3850_, v_logCompileErrors_3851_, v_isMeta_3853_, v___x_3900_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_3994_;
goto v___jp_3868_;
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec_ref(v___f_3956_);
lean_dec(v_a_3897_);
lean_dec(v_userName_3894_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_3996_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3960_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3960_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
else
{
lean_dec(v_userName_3894_);
goto v___jp_3928_;
}
}
else
{
lean_dec_ref(v_a_3906_);
lean_dec(v_userName_3894_);
goto v___jp_3928_;
}
v___jp_3910_:
{
lean_object* v___x_3912_; 
lean_inc(v___x_3903_);
v___x_3912_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_3903_, v_a_3897_, v_compile_3850_, v_logCompileErrors_3851_, v_isMeta_3853_, v___x_3891_, v___x_3900_, v_a_3911_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_3912_;
goto v___jp_3868_;
}
v___jp_3913_:
{
if (v___y_3915_ == 0)
{
lean_dec_ref(v___y_3914_);
lean_del_object(v___x_3908_);
v_a_3911_ = v___x_3900_;
goto v___jp_3910_;
}
else
{
lean_object* v___x_3917_; 
lean_dec(v_a_3897_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set_tag(v___x_3908_, 1);
lean_ctor_set(v___x_3908_, 0, v___y_3914_);
v___x_3917_ = v___x_3908_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___y_3914_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
v___jp_3919_:
{
uint8_t v___x_3921_; 
v___x_3921_ = l_Lean_Exception_isInterrupt(v_a_3920_);
if (v___x_3921_ == 0)
{
uint8_t v___x_3922_; 
lean_inc_ref(v_a_3920_);
v___x_3922_ = l_Lean_Exception_isRuntime(v_a_3920_);
v___y_3914_ = v_a_3920_;
v___y_3915_ = v___x_3922_;
goto v___jp_3913_;
}
else
{
v___y_3914_ = v_a_3920_;
v___y_3915_ = v___x_3921_;
goto v___jp_3913_;
}
}
v___jp_3923_:
{
if (lean_obj_tag(v___y_3924_) == 0)
{
lean_object* v_a_3925_; 
lean_del_object(v___x_3908_);
v_a_3925_ = lean_ctor_get(v___y_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref(v___y_3924_);
if (lean_obj_tag(v_a_3925_) == 0)
{
lean_dec(v_a_3897_);
lean_dec(v___x_3891_);
v_a_3864_ = v___x_3900_;
goto v___jp_3863_;
}
else
{
lean_object* v_a_3926_; 
v_a_3926_ = lean_ctor_get(v_a_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v_a_3925_);
v_a_3911_ = v_a_3926_;
goto v___jp_3910_;
}
}
else
{
lean_object* v_a_3927_; 
v_a_3927_ = lean_ctor_get(v___y_3924_, 0);
lean_inc(v_a_3927_);
lean_dec_ref(v___y_3924_);
v_a_3920_ = v_a_3927_;
goto v___jp_3919_;
}
}
v___jp_3928_:
{
lean_object* v_options_3929_; lean_object* v___x_3930_; uint8_t v___x_3931_; 
v_options_3929_ = lean_ctor_get(v___y_3860_, 2);
v___x_3930_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3931_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3929_, v___x_3930_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; 
lean_del_object(v___x_3908_);
lean_inc(v___x_3903_);
v___x_3932_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_3903_, v_a_3897_, v_compile_3850_, v_logCompileErrors_3851_, v_isMeta_3853_, v___x_3891_, v___x_3900_, v___x_3900_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_3932_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_box(0);
lean_inc(v_a_3897_);
v___x_3934_ = l_Lean_Meta_trySynthInstance(v_a_3897_, v___x_3933_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref(v___x_3934_);
if (lean_obj_tag(v_a_3935_) == 1)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; 
v_a_3936_ = lean_ctor_get(v_a_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref(v_a_3935_);
v___x_3937_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3901_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; uint8_t v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref(v___x_3937_);
v___x_3939_ = lean_unbox(v_a_3938_);
lean_dec(v_a_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; 
lean_inc(v___x_3891_);
v___x_3940_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_3891_, v_a_3936_, v___x_3900_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3924_ = v___x_3940_;
goto v___jp_3923_;
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3941_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2);
lean_inc(v_a_3936_);
v___x_3942_ = l_Lean_MessageData_ofExpr(v_a_3936_);
v___x_3943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3901_, v___x_3943_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v___x_3946_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref(v___x_3944_);
lean_inc(v___x_3891_);
v___x_3946_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_3891_, v_a_3936_, v_a_3945_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3924_ = v___x_3946_;
goto v___jp_3923_;
}
else
{
lean_object* v_a_3947_; 
lean_dec(v_a_3936_);
v_a_3947_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3947_);
lean_dec_ref(v___x_3944_);
v_a_3920_ = v_a_3947_;
goto v___jp_3919_;
}
}
}
else
{
lean_object* v_a_3948_; 
lean_dec(v_a_3936_);
v_a_3948_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3948_);
lean_dec_ref(v___x_3937_);
v_a_3920_ = v_a_3948_;
goto v___jp_3919_;
}
}
else
{
lean_dec(v_a_3935_);
lean_del_object(v___x_3908_);
v_a_3911_ = v___x_3900_;
goto v___jp_3910_;
}
}
else
{
lean_object* v_a_3949_; 
v_a_3949_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3949_);
lean_dec_ref(v___x_3934_);
v_a_3920_ = v_a_3949_;
goto v___jp_3919_;
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_dec(v_a_3897_);
lean_dec(v_userName_3894_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_4005_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3905_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3905_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
else
{
lean_object* v___x_4013_; 
lean_dec(v_userName_3894_);
lean_inc(v___y_3861_);
lean_inc_ref(v___y_3860_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___x_3903_);
v___x_4013_ = lean_infer_type(v___x_3903_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc_n(v_a_4014_, 2);
lean_dec_ref(v___x_4013_);
lean_inc(v_a_3897_);
v___x_4015_ = l_Lean_Meta_isExprDefEq(v_a_3897_, v_a_4014_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___f_4017_; uint8_t v___x_4018_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref(v___x_4015_);
v___f_4017_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7));
v___x_4018_ = lean_unbox(v_a_4016_);
lean_dec(v_a_4016_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4019_; 
v___x_4019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_3901_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; uint8_t v___x_4021_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref(v___x_4019_);
v___x_4021_ = lean_unbox(v_a_4020_);
lean_dec(v_a_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; 
lean_dec(v_a_4014_);
lean_inc(v___x_3903_);
v___x_4022_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_3897_, v___x_3903_, v___x_3849_, v___x_3891_, v___f_4017_, v___x_3900_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_4022_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4023_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9);
lean_inc(v_a_3856_);
v___x_4024_ = l_Nat_reprFast(v_a_3856_);
v___x_4025_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
v___x_4026_ = l_Lean_MessageData_ofFormat(v___x_4025_);
v___x_4027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4023_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11);
v___x_4029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4027_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
lean_inc(v_a_3897_);
v___x_4030_ = l_Lean_MessageData_ofExpr(v_a_3897_);
v___x_4031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13);
v___x_4033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = l_Lean_MessageData_ofExpr(v_a_4014_);
v___x_4035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4033_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15);
v___x_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4035_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
lean_inc(v___x_3903_);
v___x_4038_ = l_Lean_MessageData_ofExpr(v___x_3903_);
v___x_4039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3901_, v___x_4039_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref(v___x_4040_);
lean_inc(v___x_3903_);
v___x_4042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_3897_, v___x_3903_, v___x_3849_, v___x_3891_, v___f_4017_, v_a_4041_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_4042_;
goto v___jp_3868_;
}
else
{
lean_dec(v_a_3897_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
return v___x_4040_;
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec(v_a_4014_);
lean_dec(v_a_3897_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_4043_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4019_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4019_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
else
{
lean_object* v___x_4051_; 
lean_dec(v_a_4014_);
lean_dec(v_a_3897_);
lean_inc(v___x_3903_);
v___x_4051_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3891_, v___x_3903_, v___y_3859_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4053_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
lean_dec_ref(v___x_4051_);
v___x_4053_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_3900_, v_a_4052_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
v___y_3869_ = v___x_4053_;
goto v___jp_3868_;
}
else
{
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
return v___x_4051_;
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec(v_a_4014_);
lean_dec(v_a_3897_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_4054_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4015_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4015_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec(v_a_3897_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_4062_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4013_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4013_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec(v_a_3897_);
lean_dec(v_userName_3894_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_4070_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_3898_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_3898_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec(v_userName_3894_);
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_4078_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_3896_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_3896_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v___x_3891_);
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_4086_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_3892_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_3892_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
v___jp_3863_:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = lean_unsigned_to_nat(1u);
v___x_3866_ = lean_nat_add(v_a_3856_, v___x_3865_);
lean_dec(v_a_3856_);
v___x_3867_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(v_upperBound_3846_, v_fst_3847_, v_args_3848_, v___x_3849_, v_compile_3850_, v_logCompileErrors_3851_, v___x_3852_, v_isMeta_3853_, v_val_3854_, v_expectedType_3855_, v___x_3866_, v_a_3864_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3867_;
}
v___jp_3868_:
{
if (lean_obj_tag(v___y_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3879_; 
v_a_3870_ = lean_ctor_get(v___y_3869_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___y_3869_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3872_ = v___y_3869_;
v_isShared_3873_ = v_isSharedCheck_3879_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___y_3869_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3879_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
if (lean_obj_tag(v_a_3870_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; 
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_3874_ = lean_ctor_get(v_a_3870_, 0);
lean_inc(v_a_3874_);
lean_dec_ref(v_a_3870_);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 0, v_a_3874_);
v___x_3876_ = v___x_3872_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
else
{
lean_object* v_a_3878_; 
lean_del_object(v___x_3872_);
v_a_3878_ = lean_ctor_get(v_a_3870_, 0);
lean_inc(v_a_3878_);
lean_dec_ref(v_a_3870_);
v_a_3864_ = v_a_3878_;
goto v___jp_3863_;
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_a_3856_);
lean_dec_ref(v_expectedType_3855_);
lean_dec(v_val_3854_);
v_a_3880_ = lean_ctor_get(v___y_3869_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___y_3869_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___y_3869_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___y_3869_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(lean_object* v_inst_4094_, lean_object* v_expectedType_4095_, uint8_t v___x_4096_, uint8_t v___x_4097_, uint8_t v_compile_4098_, uint8_t v_logCompileErrors_4099_, uint8_t v_isMeta_4100_, lean_object* v_val_4101_, lean_object* v_x_4102_, lean_object* v_x_4103_, lean_object* v_x_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v_options_4153_; lean_object* v___y_4154_; 
if (lean_obj_tag(v_x_4102_) == 5)
{
lean_object* v_fn_4220_; lean_object* v_arg_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v_fn_4220_ = lean_ctor_get(v_x_4102_, 0);
lean_inc_ref(v_fn_4220_);
v_arg_4221_ = lean_ctor_get(v_x_4102_, 1);
lean_inc_ref(v_arg_4221_);
lean_dec_ref(v_x_4102_);
v___x_4222_ = lean_array_set(v_x_4103_, v_x_4104_, v_arg_4221_);
v___x_4223_ = lean_unsigned_to_nat(1u);
v___x_4224_ = lean_nat_sub(v_x_4104_, v___x_4223_);
lean_dec(v_x_4104_);
v_x_4102_ = v_fn_4220_;
v_x_4103_ = v___x_4222_;
v_x_4104_ = v___x_4224_;
goto _start;
}
else
{
lean_object* v_cls_4226_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___x_4249_; 
lean_dec(v_x_4104_);
v_cls_4226_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4249_ = l_Lean_Expr_constName_x3f(v_x_4102_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_dec_ref(v_x_4103_);
lean_dec_ref(v_x_4102_);
lean_dec(v_val_4101_);
v___y_4228_ = v___y_4105_;
v___y_4229_ = v___y_4106_;
v___y_4230_ = v___y_4107_;
v___y_4231_ = v___y_4108_;
goto v___jp_4227_;
}
else
{
lean_object* v_val_4250_; lean_object* v___x_4251_; 
v_val_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_val_4250_);
lean_dec_ref(v___x_4249_);
v___x_4251_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4250_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref(v___x_4251_);
if (lean_obj_tag(v_a_4252_) == 6)
{
lean_object* v_val_4253_; lean_object* v___x_4254_; 
lean_dec_ref(v_inst_4094_);
v_val_4253_ = lean_ctor_get(v_a_4252_, 0);
lean_inc_ref(v_val_4253_);
lean_dec_ref(v_a_4252_);
lean_inc(v___y_4108_);
lean_inc_ref(v___y_4107_);
lean_inc(v___y_4106_);
lean_inc_ref(v___y_4105_);
lean_inc_ref(v_x_4102_);
v___x_4254_ = lean_infer_type(v_x_4102_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref(v___x_4254_);
v___x_4256_ = 0;
v___x_4257_ = l_Lean_Meta_forallMetaTelescope(v_a_4255_, v___x_4256_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v_snd_4259_; lean_object* v_fst_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4359_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref(v___x_4257_);
v_snd_4259_ = lean_ctor_get(v_a_4258_, 1);
v_fst_4260_ = lean_ctor_get(v_a_4258_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v_a_4258_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4262_ = v_a_4258_;
v_isShared_4263_ = v_isSharedCheck_4359_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_snd_4259_);
lean_inc(v_fst_4260_);
lean_dec(v_a_4258_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4359_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v_snd_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4357_; 
v_snd_4264_ = lean_ctor_get(v_snd_4259_, 1);
v_isSharedCheck_4357_ = !lean_is_exclusive(v_snd_4259_);
if (v_isSharedCheck_4357_ == 0)
{
lean_object* v_unused_4358_; 
v_unused_4358_ = lean_ctor_get(v_snd_4259_, 0);
lean_dec(v_unused_4358_);
v___x_4266_ = v_snd_4259_;
v_isShared_4267_ = v_isSharedCheck_4357_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_snd_4264_);
lean_dec(v_snd_4259_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4357_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4268_ = lean_array_get_size(v_x_4103_);
v___x_4305_ = lean_array_get_size(v_fst_4260_);
v___x_4306_ = lean_nat_dec_eq(v___x_4268_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
lean_dec(v_snd_4264_);
lean_dec(v_fst_4260_);
lean_dec_ref(v_val_4253_);
lean_dec(v_val_4101_);
lean_dec_ref(v_expectedType_4095_);
v___x_4307_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_4308_ = l_Lean_MessageData_ofExpr(v_x_4102_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set_tag(v___x_4266_, 7);
lean_ctor_set(v___x_4266_, 1, v___x_4308_);
lean_ctor_set(v___x_4266_, 0, v___x_4307_);
v___x_4310_ = v___x_4266_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4307_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4311_; lean_object* v___x_4313_; 
v___x_4311_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3);
if (v_isShared_4263_ == 0)
{
lean_ctor_set_tag(v___x_4262_, 7);
lean_ctor_set(v___x_4262_, 1, v___x_4311_);
lean_ctor_set(v___x_4262_, 0, v___x_4310_);
v___x_4313_ = v___x_4262_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4310_);
lean_ctor_set(v_reuseFailAlloc_4320_, 1, v___x_4311_);
v___x_4313_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4314_ = lean_array_to_list(v_x_4103_);
v___x_4315_ = lean_box(0);
v___x_4316_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_4314_, v___x_4315_);
v___x_4317_ = l_Lean_MessageData_ofList(v___x_4316_);
v___x_4318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4313_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
v___x_4319_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4318_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
return v___x_4319_;
}
}
}
else
{
lean_object* v___x_4322_; 
lean_inc_ref(v_expectedType_4095_);
v___x_4322_ = l_Lean_Meta_isExprDefEq(v_expectedType_4095_, v_snd_4264_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; uint8_t v___x_4324_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = lean_unbox(v_a_4323_);
lean_dec(v_a_4323_);
if (v___x_4324_ == 0)
{
lean_object* v_toConstantVal_4325_; lean_object* v_name_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4330_; 
lean_dec(v_fst_4260_);
lean_dec_ref(v_x_4103_);
lean_dec_ref(v_x_4102_);
lean_dec(v_val_4101_);
v_toConstantVal_4325_ = lean_ctor_get(v_val_4253_, 0);
lean_inc_ref(v_toConstantVal_4325_);
lean_dec_ref(v_val_4253_);
v_name_4326_ = lean_ctor_get(v_toConstantVal_4325_, 0);
lean_inc(v_name_4326_);
lean_dec_ref(v_toConstantVal_4325_);
v___x_4327_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_4328_ = l_Lean_MessageData_ofExpr(v_expectedType_4095_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set_tag(v___x_4266_, 7);
lean_ctor_set(v___x_4266_, 1, v___x_4328_);
lean_ctor_set(v___x_4266_, 0, v___x_4327_);
v___x_4330_ = v___x_4266_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4348_, 1, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4331_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_4263_ == 0)
{
lean_ctor_set_tag(v___x_4262_, 7);
lean_ctor_set(v___x_4262_, 1, v___x_4331_);
lean_ctor_set(v___x_4262_, 0, v___x_4330_);
v___x_4333_ = v___x_4262_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4347_, 1, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
v___x_4334_ = l_Lean_MessageData_ofConstName(v_name_4326_, v___x_4096_);
v___x_4335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4333_);
lean_ctor_set(v___x_4335_, 1, v___x_4334_);
v___x_4336_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4335_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
v___x_4338_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4337_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
else
{
lean_del_object(v___x_4266_);
lean_del_object(v___x_4262_);
v___y_4270_ = v___y_4105_;
v___y_4271_ = v___y_4106_;
v___y_4272_ = v___y_4107_;
v___y_4273_ = v___y_4108_;
goto v___jp_4269_;
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_del_object(v___x_4266_);
lean_del_object(v___x_4262_);
lean_dec(v_fst_4260_);
lean_dec_ref(v_val_4253_);
lean_dec_ref(v_x_4103_);
lean_dec_ref(v_x_4102_);
lean_dec(v_val_4101_);
lean_dec_ref(v_expectedType_4095_);
v_a_4349_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4322_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4322_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
v___jp_4269_:
{
lean_object* v_numParams_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v_numParams_4274_ = lean_ctor_get(v_val_4253_, 3);
lean_inc(v_numParams_4274_);
lean_dec_ref(v_val_4253_);
v___x_4275_ = lean_box(0);
v___x_4276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_4268_, v_fst_4260_, v_x_4103_, v___x_4097_, v_compile_4098_, v_logCompileErrors_4099_, v___x_4096_, v_isMeta_4100_, v_val_4101_, v_expectedType_4095_, v_numParams_4274_, v___x_4275_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec_ref(v_x_4103_);
if (lean_obj_tag(v___x_4276_) == 0)
{
size_t v_sz_4277_; size_t v___x_4278_; lean_object* v___x_4279_; 
lean_dec_ref(v___x_4276_);
v_sz_4277_ = lean_array_size(v_fst_4260_);
v___x_4278_ = ((size_t)0ULL);
v___x_4279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_4277_, v___x_4278_, v_fst_4260_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4288_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4282_ = v___x_4279_;
v_isShared_4283_ = v_isSharedCheck_4288_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4279_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4288_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4284_; lean_object* v___x_4286_; 
v___x_4284_ = l_Lean_mkAppN(v_x_4102_, v_a_4280_);
lean_dec(v_a_4280_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v___x_4284_);
v___x_4286_ = v___x_4282_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4284_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec_ref(v_x_4102_);
v_a_4289_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4279_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4279_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
else
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
lean_dec(v_fst_4260_);
lean_dec_ref(v_x_4102_);
v_a_4297_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4276_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4276_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec_ref(v_val_4253_);
lean_dec_ref(v_x_4103_);
lean_dec_ref(v_x_4102_);
lean_dec(v_val_4101_);
lean_dec_ref(v_expectedType_4095_);
v_a_4360_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4257_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4257_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_dec_ref(v_val_4253_);
lean_dec_ref(v_x_4103_);
lean_dec_ref(v_x_4102_);
lean_dec(v_val_4101_);
lean_dec_ref(v_expectedType_4095_);
return v___x_4254_;
}
}
else
{
lean_dec(v_a_4252_);
lean_dec_ref(v_x_4103_);
lean_dec_ref(v_x_4102_);
lean_dec(v_val_4101_);
v___y_4228_ = v___y_4105_;
v___y_4229_ = v___y_4106_;
v___y_4230_ = v___y_4107_;
v___y_4231_ = v___y_4108_;
goto v___jp_4227_;
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec_ref(v_x_4103_);
lean_dec_ref(v_x_4102_);
lean_dec(v_val_4101_);
lean_dec_ref(v_expectedType_4095_);
lean_dec_ref(v_inst_4094_);
v_a_4368_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4251_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4251_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
v___jp_4227_:
{
lean_object* v_options_4232_; uint8_t v_hasTrace_4233_; 
v_options_4232_ = lean_ctor_get(v___y_4230_, 2);
v_hasTrace_4233_ = lean_ctor_get_uint8(v_options_4232_, sizeof(void*)*1);
if (v_hasTrace_4233_ == 0)
{
v___y_4150_ = v___y_4228_;
v___y_4151_ = v___y_4229_;
v___y_4152_ = v___y_4230_;
v_options_4153_ = v_options_4232_;
v___y_4154_ = v___y_4231_;
goto v___jp_4149_;
}
else
{
lean_object* v_inheritedTraceOptions_4234_; lean_object* v___x_4235_; uint8_t v___x_4236_; 
v_inheritedTraceOptions_4234_ = lean_ctor_get(v___y_4230_, 13);
v___x_4235_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_4236_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4234_, v_options_4232_, v___x_4235_);
if (v___x_4236_ == 0)
{
v___y_4150_ = v___y_4228_;
v___y_4151_ = v___y_4229_;
v___y_4152_ = v___y_4230_;
v_options_4153_ = v_options_4232_;
v___y_4154_ = v___y_4231_;
goto v___jp_4149_;
}
else
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4237_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_4094_);
v___x_4238_ = l_Lean_MessageData_ofExpr(v_inst_4094_);
v___x_4239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4237_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4226_, v___x_4239_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_dec_ref(v___x_4240_);
v___y_4150_ = v___y_4228_;
v___y_4151_ = v___y_4229_;
v___y_4152_ = v___y_4230_;
v_options_4153_ = v_options_4232_;
v___y_4154_ = v___y_4231_;
goto v___jp_4149_;
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_expectedType_4095_);
lean_dec_ref(v_inst_4094_);
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4240_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4240_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
}
}
v___jp_4110_:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_enableRealizationsForConst(v___y_4112_, v___y_4113_, v___y_4114_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4122_ == 0)
{
lean_object* v_unused_4123_; 
v_unused_4123_ = lean_ctor_get(v___x_4115_, 0);
lean_dec(v_unused_4123_);
v___x_4117_ = v___x_4115_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_dec(v___x_4115_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 0, v___y_4111_);
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___y_4111_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec_ref(v___y_4111_);
v_a_4124_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4115_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4115_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
v___jp_4132_:
{
if (v_compile_4098_ == 0)
{
v___y_4111_ = v___y_4133_;
v___y_4112_ = v___y_4134_;
v___y_4113_ = v___y_4135_;
v___y_4114_ = v___y_4136_;
goto v___jp_4110_;
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4137_ = lean_unsigned_to_nat(1u);
v___x_4138_ = lean_mk_empty_array_with_capacity(v___x_4137_);
lean_inc(v___y_4134_);
v___x_4139_ = lean_array_push(v___x_4138_, v___y_4134_);
v___x_4140_ = l_Lean_compileDecls(v___x_4139_, v_logCompileErrors_4099_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_dec_ref(v___x_4140_);
v___y_4111_ = v___y_4133_;
v___y_4112_ = v___y_4134_;
v___y_4113_ = v___y_4135_;
v___y_4114_ = v___y_4136_;
goto v___jp_4110_;
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4140_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4140_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
v___jp_4149_:
{
lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4155_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4156_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4153_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; 
lean_dec_ref(v_expectedType_4095_);
v___x_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_inst_4094_);
return v___x_4157_;
}
else
{
lean_object* v___x_4158_; 
lean_inc(v___y_4154_);
lean_inc_ref(v___y_4152_);
lean_inc(v___y_4151_);
lean_inc_ref(v___y_4150_);
lean_inc_ref(v_inst_4094_);
v___x_4158_ = lean_infer_type(v_inst_4094_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4154_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4160_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref(v___x_4158_);
lean_inc_ref(v_expectedType_4095_);
v___x_4160_ = l_Lean_Meta_isExprDefEq(v_expectedType_4095_, v_a_4159_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4154_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4211_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4163_ = v___x_4160_;
v_isShared_4164_ = v_isSharedCheck_4211_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4211_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
uint8_t v___x_4165_; 
v___x_4165_ = lean_unbox(v_a_4161_);
lean_dec(v_a_4161_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v_a_4168_; lean_object* v___x_4169_; 
lean_del_object(v___x_4163_);
v___x_4166_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_4167_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4166_, v___y_4154_);
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc_n(v_a_4168_, 2);
lean_dec_ref(v___x_4167_);
v___x_4169_ = l_Lean_Meta_mkAuxDefinition(v_a_4168_, v_expectedType_4095_, v_inst_4094_, v___x_4096_, v___x_4096_, v___x_4097_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4154_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; uint8_t v___x_4171_; lean_object* v___x_4172_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc(v_a_4170_);
lean_dec_ref(v___x_4169_);
v___x_4171_ = 3;
lean_inc(v_a_4168_);
v___x_4172_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4168_, v___x_4171_, v___y_4151_, v___y_4154_);
lean_dec_ref(v___x_4172_);
if (v_isMeta_4100_ == 0)
{
v___y_4133_ = v_a_4170_;
v___y_4134_ = v_a_4168_;
v___y_4135_ = v___y_4152_;
v___y_4136_ = v___y_4154_;
goto v___jp_4132_;
}
else
{
lean_object* v___x_4173_; lean_object* v_env_4174_; lean_object* v_nextMacroScope_4175_; lean_object* v_ngen_4176_; lean_object* v_auxDeclNGen_4177_; lean_object* v_traceState_4178_; lean_object* v_messages_4179_; lean_object* v_infoState_4180_; lean_object* v_snapshotTasks_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4206_; 
v___x_4173_ = lean_st_ref_take(v___y_4154_);
v_env_4174_ = lean_ctor_get(v___x_4173_, 0);
v_nextMacroScope_4175_ = lean_ctor_get(v___x_4173_, 1);
v_ngen_4176_ = lean_ctor_get(v___x_4173_, 2);
v_auxDeclNGen_4177_ = lean_ctor_get(v___x_4173_, 3);
v_traceState_4178_ = lean_ctor_get(v___x_4173_, 4);
v_messages_4179_ = lean_ctor_get(v___x_4173_, 6);
v_infoState_4180_ = lean_ctor_get(v___x_4173_, 7);
v_snapshotTasks_4181_ = lean_ctor_get(v___x_4173_, 8);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4206_ == 0)
{
lean_object* v_unused_4207_; 
v_unused_4207_ = lean_ctor_get(v___x_4173_, 5);
lean_dec(v_unused_4207_);
v___x_4183_ = v___x_4173_;
v_isShared_4184_ = v_isSharedCheck_4206_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_snapshotTasks_4181_);
lean_inc(v_infoState_4180_);
lean_inc(v_messages_4179_);
lean_inc(v_traceState_4178_);
lean_inc(v_auxDeclNGen_4177_);
lean_inc(v_ngen_4176_);
lean_inc(v_nextMacroScope_4175_);
lean_inc(v_env_4174_);
lean_dec(v___x_4173_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4206_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4188_; 
lean_inc(v_a_4168_);
v___x_4185_ = l_Lean_markMeta(v_env_4174_, v_a_4168_);
v___x_4186_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 5, v___x_4186_);
lean_ctor_set(v___x_4183_, 0, v___x_4185_);
v___x_4188_ = v___x_4183_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4185_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_nextMacroScope_4175_);
lean_ctor_set(v_reuseFailAlloc_4205_, 2, v_ngen_4176_);
lean_ctor_set(v_reuseFailAlloc_4205_, 3, v_auxDeclNGen_4177_);
lean_ctor_set(v_reuseFailAlloc_4205_, 4, v_traceState_4178_);
lean_ctor_set(v_reuseFailAlloc_4205_, 5, v___x_4186_);
lean_ctor_set(v_reuseFailAlloc_4205_, 6, v_messages_4179_);
lean_ctor_set(v_reuseFailAlloc_4205_, 7, v_infoState_4180_);
lean_ctor_set(v_reuseFailAlloc_4205_, 8, v_snapshotTasks_4181_);
v___x_4188_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v_mctx_4191_; lean_object* v_zetaDeltaFVarIds_4192_; lean_object* v_postponed_4193_; lean_object* v_diag_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4203_; 
v___x_4189_ = lean_st_ref_set(v___y_4154_, v___x_4188_);
v___x_4190_ = lean_st_ref_take(v___y_4151_);
v_mctx_4191_ = lean_ctor_get(v___x_4190_, 0);
v_zetaDeltaFVarIds_4192_ = lean_ctor_get(v___x_4190_, 2);
v_postponed_4193_ = lean_ctor_get(v___x_4190_, 3);
v_diag_4194_ = lean_ctor_get(v___x_4190_, 4);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4203_ == 0)
{
lean_object* v_unused_4204_; 
v_unused_4204_ = lean_ctor_get(v___x_4190_, 1);
lean_dec(v_unused_4204_);
v___x_4196_ = v___x_4190_;
v_isShared_4197_ = v_isSharedCheck_4203_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_diag_4194_);
lean_inc(v_postponed_4193_);
lean_inc(v_zetaDeltaFVarIds_4192_);
lean_inc(v_mctx_4191_);
lean_dec(v___x_4190_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4203_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4198_; lean_object* v___x_4200_; 
v___x_4198_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 1, v___x_4198_);
v___x_4200_ = v___x_4196_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_mctx_4191_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v___x_4198_);
lean_ctor_set(v_reuseFailAlloc_4202_, 2, v_zetaDeltaFVarIds_4192_);
lean_ctor_set(v_reuseFailAlloc_4202_, 3, v_postponed_4193_);
lean_ctor_set(v_reuseFailAlloc_4202_, 4, v_diag_4194_);
v___x_4200_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_st_ref_set(v___y_4151_, v___x_4200_);
v___y_4133_ = v_a_4170_;
v___y_4134_ = v_a_4168_;
v___y_4135_ = v___y_4152_;
v___y_4136_ = v___y_4154_;
goto v___jp_4132_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4168_);
return v___x_4169_;
}
}
else
{
lean_object* v___x_4209_; 
lean_dec_ref(v_expectedType_4095_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v_inst_4094_);
v___x_4209_ = v___x_4163_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_inst_4094_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec_ref(v_expectedType_4095_);
lean_dec_ref(v_inst_4094_);
v_a_4212_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4160_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4160_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4095_);
lean_dec_ref(v_inst_4094_);
return v___x_4158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object* v_inst_4376_, lean_object* v_expectedType_4377_, uint8_t v___x_4378_, uint8_t v___x_4379_, uint8_t v_compile_4380_, uint8_t v_logCompileErrors_4381_, uint8_t v_isMeta_4382_, lean_object* v_val_4383_, lean_object* v_x_4384_, lean_object* v_x_4385_, lean_object* v_x_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v_options_4435_; lean_object* v___y_4436_; 
if (lean_obj_tag(v_x_4384_) == 5)
{
lean_object* v_fn_4502_; lean_object* v_arg_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v_fn_4502_ = lean_ctor_get(v_x_4384_, 0);
lean_inc_ref(v_fn_4502_);
v_arg_4503_ = lean_ctor_get(v_x_4384_, 1);
lean_inc_ref(v_arg_4503_);
lean_dec_ref(v_x_4384_);
v___x_4504_ = lean_array_set(v_x_4385_, v_x_4386_, v_arg_4503_);
v___x_4505_ = lean_unsigned_to_nat(1u);
v___x_4506_ = lean_nat_sub(v_x_4386_, v___x_4505_);
v___x_4507_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(v_inst_4376_, v_expectedType_4377_, v___x_4378_, v___x_4379_, v_compile_4380_, v_logCompileErrors_4381_, v_isMeta_4382_, v_val_4383_, v_fn_4502_, v___x_4504_, v___x_4506_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
return v___x_4507_;
}
else
{
lean_object* v_cls_4508_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___x_4531_; 
v_cls_4508_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4531_ = l_Lean_Expr_constName_x3f(v_x_4384_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_dec_ref(v_x_4385_);
lean_dec_ref(v_x_4384_);
lean_dec(v_val_4383_);
v___y_4510_ = v___y_4387_;
v___y_4511_ = v___y_4388_;
v___y_4512_ = v___y_4389_;
v___y_4513_ = v___y_4390_;
goto v___jp_4509_;
}
else
{
lean_object* v_val_4532_; lean_object* v___x_4533_; 
v_val_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_val_4532_);
lean_dec_ref(v___x_4531_);
v___x_4533_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4532_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
lean_inc(v_a_4534_);
lean_dec_ref(v___x_4533_);
if (lean_obj_tag(v_a_4534_) == 6)
{
lean_object* v_val_4535_; lean_object* v___x_4536_; 
lean_dec_ref(v_inst_4376_);
v_val_4535_ = lean_ctor_get(v_a_4534_, 0);
lean_inc_ref(v_val_4535_);
lean_dec_ref(v_a_4534_);
lean_inc(v___y_4390_);
lean_inc_ref(v___y_4389_);
lean_inc(v___y_4388_);
lean_inc_ref(v___y_4387_);
lean_inc_ref(v_x_4384_);
v___x_4536_ = lean_infer_type(v_x_4384_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; uint8_t v___x_4538_; lean_object* v___x_4539_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref(v___x_4536_);
v___x_4538_ = 0;
v___x_4539_ = l_Lean_Meta_forallMetaTelescope(v_a_4537_, v___x_4538_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v_snd_4541_; lean_object* v_fst_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4641_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_a_4540_);
lean_dec_ref(v___x_4539_);
v_snd_4541_ = lean_ctor_get(v_a_4540_, 1);
v_fst_4542_ = lean_ctor_get(v_a_4540_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_a_4540_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4544_ = v_a_4540_;
v_isShared_4545_ = v_isSharedCheck_4641_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_snd_4541_);
lean_inc(v_fst_4542_);
lean_dec(v_a_4540_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4641_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v_snd_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4639_; 
v_snd_4546_ = lean_ctor_get(v_snd_4541_, 1);
v_isSharedCheck_4639_ = !lean_is_exclusive(v_snd_4541_);
if (v_isSharedCheck_4639_ == 0)
{
lean_object* v_unused_4640_; 
v_unused_4640_ = lean_ctor_get(v_snd_4541_, 0);
lean_dec(v_unused_4640_);
v___x_4548_ = v_snd_4541_;
v_isShared_4549_ = v_isSharedCheck_4639_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_snd_4546_);
lean_dec(v_snd_4541_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4639_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4550_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___x_4587_; uint8_t v___x_4588_; 
v___x_4550_ = lean_array_get_size(v_x_4385_);
v___x_4587_ = lean_array_get_size(v_fst_4542_);
v___x_4588_ = lean_nat_dec_eq(v___x_4550_, v___x_4587_);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4592_; 
lean_dec(v_snd_4546_);
lean_dec(v_fst_4542_);
lean_dec_ref(v_val_4535_);
lean_dec(v_val_4383_);
lean_dec_ref(v_expectedType_4377_);
v___x_4589_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_4590_ = l_Lean_MessageData_ofExpr(v_x_4384_);
if (v_isShared_4549_ == 0)
{
lean_ctor_set_tag(v___x_4548_, 7);
lean_ctor_set(v___x_4548_, 1, v___x_4590_);
lean_ctor_set(v___x_4548_, 0, v___x_4589_);
v___x_4592_ = v___x_4548_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v___x_4590_);
v___x_4592_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4593_; lean_object* v___x_4595_; 
v___x_4593_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3);
if (v_isShared_4545_ == 0)
{
lean_ctor_set_tag(v___x_4544_, 7);
lean_ctor_set(v___x_4544_, 1, v___x_4593_);
lean_ctor_set(v___x_4544_, 0, v___x_4592_);
v___x_4595_ = v___x_4544_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4592_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4596_ = lean_array_to_list(v_x_4385_);
v___x_4597_ = lean_box(0);
v___x_4598_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_4596_, v___x_4597_);
v___x_4599_ = l_Lean_MessageData_ofList(v___x_4598_);
v___x_4600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4595_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
v___x_4601_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4600_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
return v___x_4601_;
}
}
}
else
{
lean_object* v___x_4604_; 
lean_inc_ref(v_expectedType_4377_);
v___x_4604_ = l_Lean_Meta_isExprDefEq(v_expectedType_4377_, v_snd_4546_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; uint8_t v___x_4606_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref(v___x_4604_);
v___x_4606_ = lean_unbox(v_a_4605_);
lean_dec(v_a_4605_);
if (v___x_4606_ == 0)
{
lean_object* v_toConstantVal_4607_; lean_object* v_name_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
lean_dec(v_fst_4542_);
lean_dec_ref(v_x_4385_);
lean_dec_ref(v_x_4384_);
lean_dec(v_val_4383_);
v_toConstantVal_4607_ = lean_ctor_get(v_val_4535_, 0);
lean_inc_ref(v_toConstantVal_4607_);
lean_dec_ref(v_val_4535_);
v_name_4608_ = lean_ctor_get(v_toConstantVal_4607_, 0);
lean_inc(v_name_4608_);
lean_dec_ref(v_toConstantVal_4607_);
v___x_4609_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_4610_ = l_Lean_MessageData_ofExpr(v_expectedType_4377_);
if (v_isShared_4549_ == 0)
{
lean_ctor_set_tag(v___x_4548_, 7);
lean_ctor_set(v___x_4548_, 1, v___x_4610_);
lean_ctor_set(v___x_4548_, 0, v___x_4609_);
v___x_4612_ = v___x_4548_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4615_; 
v___x_4613_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_4545_ == 0)
{
lean_ctor_set_tag(v___x_4544_, 7);
lean_ctor_set(v___x_4544_, 1, v___x_4613_);
lean_ctor_set(v___x_4544_, 0, v___x_4612_);
v___x_4615_ = v___x_4544_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4612_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v___x_4613_);
v___x_4615_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
v___x_4616_ = l_Lean_MessageData_ofConstName(v_name_4608_, v___x_4378_);
v___x_4617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4615_);
lean_ctor_set(v___x_4617_, 1, v___x_4616_);
v___x_4618_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4619_, 0, v___x_4617_);
lean_ctor_set(v___x_4619_, 1, v___x_4618_);
v___x_4620_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_4619_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4620_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4620_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
}
}
else
{
lean_del_object(v___x_4548_);
lean_del_object(v___x_4544_);
v___y_4552_ = v___y_4387_;
v___y_4553_ = v___y_4388_;
v___y_4554_ = v___y_4389_;
v___y_4555_ = v___y_4390_;
goto v___jp_4551_;
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
lean_del_object(v___x_4548_);
lean_del_object(v___x_4544_);
lean_dec(v_fst_4542_);
lean_dec_ref(v_val_4535_);
lean_dec_ref(v_x_4385_);
lean_dec_ref(v_x_4384_);
lean_dec(v_val_4383_);
lean_dec_ref(v_expectedType_4377_);
v_a_4631_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4604_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4604_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
v___jp_4551_:
{
lean_object* v_numParams_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v_numParams_4556_ = lean_ctor_get(v_val_4535_, 3);
lean_inc(v_numParams_4556_);
lean_dec_ref(v_val_4535_);
v___x_4557_ = lean_box(0);
v___x_4558_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_4550_, v_fst_4542_, v_x_4385_, v___x_4379_, v_compile_4380_, v_logCompileErrors_4381_, v___x_4378_, v_isMeta_4382_, v_val_4383_, v_expectedType_4377_, v_numParams_4556_, v___x_4557_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
lean_dec_ref(v_x_4385_);
if (lean_obj_tag(v___x_4558_) == 0)
{
size_t v_sz_4559_; size_t v___x_4560_; lean_object* v___x_4561_; 
lean_dec_ref(v___x_4558_);
v_sz_4559_ = lean_array_size(v_fst_4542_);
v___x_4560_ = ((size_t)0ULL);
v___x_4561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_4559_, v___x_4560_, v_fst_4542_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4570_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4564_ = v___x_4561_;
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4561_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4566_ = l_Lean_mkAppN(v_x_4384_, v_a_4562_);
lean_dec(v_a_4562_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v___x_4566_);
v___x_4568_ = v___x_4564_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v_x_4384_);
v_a_4571_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4561_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4561_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec(v_fst_4542_);
lean_dec_ref(v_x_4384_);
v_a_4579_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4558_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4558_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4649_; 
lean_dec_ref(v_val_4535_);
lean_dec_ref(v_x_4385_);
lean_dec_ref(v_x_4384_);
lean_dec(v_val_4383_);
lean_dec_ref(v_expectedType_4377_);
v_a_4642_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4644_ = v___x_4539_;
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v___x_4539_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4649_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4647_; 
if (v_isShared_4645_ == 0)
{
v___x_4647_ = v___x_4644_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4642_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
else
{
lean_dec_ref(v_val_4535_);
lean_dec_ref(v_x_4385_);
lean_dec_ref(v_x_4384_);
lean_dec(v_val_4383_);
lean_dec_ref(v_expectedType_4377_);
return v___x_4536_;
}
}
else
{
lean_dec(v_a_4534_);
lean_dec_ref(v_x_4385_);
lean_dec_ref(v_x_4384_);
lean_dec(v_val_4383_);
v___y_4510_ = v___y_4387_;
v___y_4511_ = v___y_4388_;
v___y_4512_ = v___y_4389_;
v___y_4513_ = v___y_4390_;
goto v___jp_4509_;
}
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
lean_dec_ref(v_x_4385_);
lean_dec_ref(v_x_4384_);
lean_dec(v_val_4383_);
lean_dec_ref(v_expectedType_4377_);
lean_dec_ref(v_inst_4376_);
v_a_4650_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4533_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4533_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
v___jp_4509_:
{
lean_object* v_options_4514_; uint8_t v_hasTrace_4515_; 
v_options_4514_ = lean_ctor_get(v___y_4512_, 2);
v_hasTrace_4515_ = lean_ctor_get_uint8(v_options_4514_, sizeof(void*)*1);
if (v_hasTrace_4515_ == 0)
{
v___y_4432_ = v___y_4510_;
v___y_4433_ = v___y_4511_;
v___y_4434_ = v___y_4512_;
v_options_4435_ = v_options_4514_;
v___y_4436_ = v___y_4513_;
goto v___jp_4431_;
}
else
{
lean_object* v_inheritedTraceOptions_4516_; lean_object* v___x_4517_; uint8_t v___x_4518_; 
v_inheritedTraceOptions_4516_ = lean_ctor_get(v___y_4512_, 13);
v___x_4517_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_4518_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4516_, v_options_4514_, v___x_4517_);
if (v___x_4518_ == 0)
{
v___y_4432_ = v___y_4510_;
v___y_4433_ = v___y_4511_;
v___y_4434_ = v___y_4512_;
v_options_4435_ = v_options_4514_;
v___y_4436_ = v___y_4513_;
goto v___jp_4431_;
}
else
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4519_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_4376_);
v___x_4520_ = l_Lean_MessageData_ofExpr(v_inst_4376_);
v___x_4521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4519_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
v___x_4522_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4508_, v___x_4521_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_dec_ref(v___x_4522_);
v___y_4432_ = v___y_4510_;
v___y_4433_ = v___y_4511_;
v___y_4434_ = v___y_4512_;
v_options_4435_ = v_options_4514_;
v___y_4436_ = v___y_4513_;
goto v___jp_4431_;
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_dec_ref(v_expectedType_4377_);
lean_dec_ref(v_inst_4376_);
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4522_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4522_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
}
}
}
v___jp_4392_:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_enableRealizationsForConst(v___y_4393_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v___x_4397_, 0);
lean_dec(v_unused_4405_);
v___x_4399_ = v___x_4397_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_dec(v___x_4397_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v___y_4394_);
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___y_4394_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
lean_dec_ref(v___y_4394_);
v_a_4406_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4397_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4397_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
v___jp_4414_:
{
if (v_compile_4380_ == 0)
{
v___y_4393_ = v___y_4415_;
v___y_4394_ = v___y_4416_;
v___y_4395_ = v___y_4417_;
v___y_4396_ = v___y_4418_;
goto v___jp_4392_;
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4419_ = lean_unsigned_to_nat(1u);
v___x_4420_ = lean_mk_empty_array_with_capacity(v___x_4419_);
lean_inc(v___y_4415_);
v___x_4421_ = lean_array_push(v___x_4420_, v___y_4415_);
v___x_4422_ = l_Lean_compileDecls(v___x_4421_, v_logCompileErrors_4381_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_dec_ref(v___x_4422_);
v___y_4393_ = v___y_4415_;
v___y_4394_ = v___y_4416_;
v___y_4395_ = v___y_4417_;
v___y_4396_ = v___y_4418_;
goto v___jp_4392_;
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec_ref(v___y_4416_);
lean_dec(v___y_4415_);
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4422_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4422_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
v___jp_4431_:
{
lean_object* v___x_4437_; uint8_t v___x_4438_; 
v___x_4437_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4438_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4435_, v___x_4437_);
if (v___x_4438_ == 0)
{
lean_object* v___x_4439_; 
lean_dec_ref(v_expectedType_4377_);
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v_inst_4376_);
return v___x_4439_;
}
else
{
lean_object* v___x_4440_; 
lean_inc(v___y_4436_);
lean_inc_ref(v___y_4434_);
lean_inc(v___y_4433_);
lean_inc_ref(v___y_4432_);
lean_inc_ref(v_inst_4376_);
v___x_4440_ = lean_infer_type(v_inst_4376_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4436_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4442_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref(v___x_4440_);
lean_inc_ref(v_expectedType_4377_);
v___x_4442_ = l_Lean_Meta_isExprDefEq(v_expectedType_4377_, v_a_4441_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4436_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4493_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4445_ = v___x_4442_;
v_isShared_4446_ = v_isSharedCheck_4493_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4442_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4493_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
uint8_t v___x_4447_; 
v___x_4447_ = lean_unbox(v_a_4443_);
lean_dec(v_a_4443_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v_a_4450_; lean_object* v___x_4451_; 
lean_del_object(v___x_4445_);
v___x_4448_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_4449_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4448_, v___y_4436_);
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc_n(v_a_4450_, 2);
lean_dec_ref(v___x_4449_);
v___x_4451_ = l_Lean_Meta_mkAuxDefinition(v_a_4450_, v_expectedType_4377_, v_inst_4376_, v___x_4378_, v___x_4378_, v___x_4379_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4436_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; uint8_t v___x_4453_; lean_object* v___x_4454_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref(v___x_4451_);
v___x_4453_ = 3;
lean_inc(v_a_4450_);
v___x_4454_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4450_, v___x_4453_, v___y_4433_, v___y_4436_);
lean_dec_ref(v___x_4454_);
if (v_isMeta_4382_ == 0)
{
v___y_4415_ = v_a_4450_;
v___y_4416_ = v_a_4452_;
v___y_4417_ = v___y_4434_;
v___y_4418_ = v___y_4436_;
goto v___jp_4414_;
}
else
{
lean_object* v___x_4455_; lean_object* v_env_4456_; lean_object* v_nextMacroScope_4457_; lean_object* v_ngen_4458_; lean_object* v_auxDeclNGen_4459_; lean_object* v_traceState_4460_; lean_object* v_messages_4461_; lean_object* v_infoState_4462_; lean_object* v_snapshotTasks_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4488_; 
v___x_4455_ = lean_st_ref_take(v___y_4436_);
v_env_4456_ = lean_ctor_get(v___x_4455_, 0);
v_nextMacroScope_4457_ = lean_ctor_get(v___x_4455_, 1);
v_ngen_4458_ = lean_ctor_get(v___x_4455_, 2);
v_auxDeclNGen_4459_ = lean_ctor_get(v___x_4455_, 3);
v_traceState_4460_ = lean_ctor_get(v___x_4455_, 4);
v_messages_4461_ = lean_ctor_get(v___x_4455_, 6);
v_infoState_4462_ = lean_ctor_get(v___x_4455_, 7);
v_snapshotTasks_4463_ = lean_ctor_get(v___x_4455_, 8);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; 
v_unused_4489_ = lean_ctor_get(v___x_4455_, 5);
lean_dec(v_unused_4489_);
v___x_4465_ = v___x_4455_;
v_isShared_4466_ = v_isSharedCheck_4488_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_snapshotTasks_4463_);
lean_inc(v_infoState_4462_);
lean_inc(v_messages_4461_);
lean_inc(v_traceState_4460_);
lean_inc(v_auxDeclNGen_4459_);
lean_inc(v_ngen_4458_);
lean_inc(v_nextMacroScope_4457_);
lean_inc(v_env_4456_);
lean_dec(v___x_4455_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4488_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4470_; 
lean_inc(v_a_4450_);
v___x_4467_ = l_Lean_markMeta(v_env_4456_, v_a_4450_);
v___x_4468_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 5, v___x_4468_);
lean_ctor_set(v___x_4465_, 0, v___x_4467_);
v___x_4470_ = v___x_4465_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4467_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_nextMacroScope_4457_);
lean_ctor_set(v_reuseFailAlloc_4487_, 2, v_ngen_4458_);
lean_ctor_set(v_reuseFailAlloc_4487_, 3, v_auxDeclNGen_4459_);
lean_ctor_set(v_reuseFailAlloc_4487_, 4, v_traceState_4460_);
lean_ctor_set(v_reuseFailAlloc_4487_, 5, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4487_, 6, v_messages_4461_);
lean_ctor_set(v_reuseFailAlloc_4487_, 7, v_infoState_4462_);
lean_ctor_set(v_reuseFailAlloc_4487_, 8, v_snapshotTasks_4463_);
v___x_4470_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v_mctx_4473_; lean_object* v_zetaDeltaFVarIds_4474_; lean_object* v_postponed_4475_; lean_object* v_diag_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4485_; 
v___x_4471_ = lean_st_ref_set(v___y_4436_, v___x_4470_);
v___x_4472_ = lean_st_ref_take(v___y_4433_);
v_mctx_4473_ = lean_ctor_get(v___x_4472_, 0);
v_zetaDeltaFVarIds_4474_ = lean_ctor_get(v___x_4472_, 2);
v_postponed_4475_ = lean_ctor_get(v___x_4472_, 3);
v_diag_4476_ = lean_ctor_get(v___x_4472_, 4);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4485_ == 0)
{
lean_object* v_unused_4486_; 
v_unused_4486_ = lean_ctor_get(v___x_4472_, 1);
lean_dec(v_unused_4486_);
v___x_4478_ = v___x_4472_;
v_isShared_4479_ = v_isSharedCheck_4485_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_diag_4476_);
lean_inc(v_postponed_4475_);
lean_inc(v_zetaDeltaFVarIds_4474_);
lean_inc(v_mctx_4473_);
lean_dec(v___x_4472_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4485_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4480_; lean_object* v___x_4482_; 
v___x_4480_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 1, v___x_4480_);
v___x_4482_ = v___x_4478_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_mctx_4473_);
lean_ctor_set(v_reuseFailAlloc_4484_, 1, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4484_, 2, v_zetaDeltaFVarIds_4474_);
lean_ctor_set(v_reuseFailAlloc_4484_, 3, v_postponed_4475_);
lean_ctor_set(v_reuseFailAlloc_4484_, 4, v_diag_4476_);
v___x_4482_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4483_; 
v___x_4483_ = lean_st_ref_set(v___y_4433_, v___x_4482_);
v___y_4415_ = v_a_4450_;
v___y_4416_ = v_a_4452_;
v___y_4417_ = v___y_4434_;
v___y_4418_ = v___y_4436_;
goto v___jp_4414_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4450_);
return v___x_4451_;
}
}
else
{
lean_object* v___x_4491_; 
lean_dec_ref(v_expectedType_4377_);
if (v_isShared_4446_ == 0)
{
lean_ctor_set(v___x_4445_, 0, v_inst_4376_);
v___x_4491_ = v___x_4445_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_inst_4376_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec_ref(v_expectedType_4377_);
lean_dec_ref(v_inst_4376_);
v_a_4494_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4442_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4442_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4377_);
lean_dec_ref(v_inst_4376_);
return v___x_4440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object* v_expectedType_4658_, lean_object* v_inst_4659_, uint8_t v___x_4660_, uint8_t v_hasTrace_4661_, uint8_t v_compile_4662_, uint8_t v_logCompileErrors_4663_, uint8_t v_isMeta_4664_, lean_object* v_val_4665_, lean_object* v_____r_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v___x_4672_; 
lean_inc_ref(v_expectedType_4658_);
v___x_4672_ = l_Lean_Meta_isProp(v_expectedType_4658_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4694_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4675_ = v___x_4672_;
v_isShared_4676_ = v_isSharedCheck_4694_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4672_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4694_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
uint8_t v___x_4677_; 
v___x_4677_ = lean_unbox(v_a_4673_);
lean_dec(v_a_4673_);
if (v___x_4677_ == 0)
{
lean_object* v___x_4678_; 
lean_del_object(v___x_4675_);
lean_inc(v___y_4670_);
lean_inc_ref(v___y_4669_);
lean_inc(v___y_4668_);
lean_inc_ref(v___y_4667_);
lean_inc_ref(v_inst_4659_);
v___x_4678_ = lean_whnf(v_inst_4659_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v_dummy_4680_; lean_object* v_nargs_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4679_);
lean_dec_ref(v___x_4678_);
v_dummy_4680_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_4681_ = l_Lean_Expr_getAppNumArgs(v_a_4679_);
lean_inc(v_nargs_4681_);
v___x_4682_ = lean_mk_array(v_nargs_4681_, v_dummy_4680_);
v___x_4683_ = lean_unsigned_to_nat(1u);
v___x_4684_ = lean_nat_sub(v_nargs_4681_, v___x_4683_);
lean_dec(v_nargs_4681_);
v___x_4685_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_inst_4659_, v_expectedType_4658_, v___x_4660_, v_hasTrace_4661_, v_compile_4662_, v_logCompileErrors_4663_, v_isMeta_4664_, v_val_4665_, v_a_4679_, v___x_4682_, v___x_4684_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___x_4684_);
return v___x_4685_;
}
else
{
lean_dec(v_val_4665_);
lean_dec_ref(v_inst_4659_);
lean_dec_ref(v_expectedType_4658_);
return v___x_4678_;
}
}
else
{
lean_object* v_options_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
lean_dec(v_val_4665_);
v_options_4686_ = lean_ctor_get(v___y_4669_, 2);
v___x_4687_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4688_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4686_, v___x_4687_);
if (v___x_4688_ == 0)
{
lean_object* v___x_4690_; 
lean_dec_ref(v_expectedType_4658_);
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v_inst_4659_);
v___x_4690_ = v___x_4675_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_inst_4659_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
else
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
lean_del_object(v___x_4675_);
v___x_4692_ = lean_box(0);
v___x_4693_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_4658_, v_inst_4659_, v_hasTrace_4661_, v___x_4692_, v_hasTrace_4661_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
return v___x_4693_;
}
}
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4702_; 
lean_dec(v_val_4665_);
lean_dec_ref(v_inst_4659_);
lean_dec_ref(v_expectedType_4658_);
v_a_4695_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4697_ = v___x_4672_;
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4672_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
if (v_isShared_4698_ == 0)
{
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___closed__3(void){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4704_ = ((lean_object*)(l_Lean_Meta_wrapInstance___closed__2));
v___x_4705_ = l_Lean_stringToMessageData(v___x_4704_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(lean_object* v_upperBound_4706_, lean_object* v_fst_4707_, lean_object* v_args_4708_, uint8_t v___x_4709_, uint8_t v_compile_4710_, uint8_t v_logCompileErrors_4711_, uint8_t v_isMeta_4712_, lean_object* v_val_4713_, lean_object* v_expectedType_4714_, lean_object* v_a_4715_, lean_object* v_b_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v_a_4723_; lean_object* v___y_4728_; uint8_t v___x_4747_; 
v___x_4747_ = lean_nat_dec_lt(v_a_4715_, v_upperBound_4706_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; 
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v___x_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4748_, 0, v_b_4716_);
return v___x_4748_;
}
else
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4749_ = lean_array_fget_borrowed(v_fst_4707_, v_a_4715_);
v___x_4750_ = l_Lean_Expr_mvarId_x21(v___x_4749_);
lean_inc(v___x_4750_);
v___x_4751_ = l_Lean_MVarId_getDecl(v___x_4750_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v_userName_4753_; lean_object* v_type_4754_; lean_object* v___x_4755_; 
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
lean_inc(v_a_4752_);
lean_dec_ref(v___x_4751_);
v_userName_4753_ = lean_ctor_get(v_a_4752_, 0);
lean_inc(v_userName_4753_);
v_type_4754_ = lean_ctor_get(v_a_4752_, 2);
lean_inc_ref(v_type_4754_);
lean_dec(v_a_4752_);
v___x_4755_ = l_Lean_instantiateMVars___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_type_4754_, v___y_4718_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4757_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
lean_inc_n(v_a_4756_, 2);
lean_dec_ref(v___x_4755_);
v___x_4757_ = l_Lean_Meta_isProp(v_a_4756_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; lean_object* v___x_4759_; lean_object* v_cls_4760_; lean_object* v___f_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref(v___x_4757_);
v___x_4759_ = lean_box(0);
v_cls_4760_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___f_4761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__0));
v___x_4762_ = lean_array_fget_borrowed(v_args_4708_, v_a_4715_);
v___x_4763_ = lean_unbox(v_a_4758_);
lean_dec(v_a_4758_);
if (v___x_4763_ == 0)
{
lean_object* v___x_4764_; 
lean_inc(v_a_4756_);
v___x_4764_ = l_Lean_Meta_isClass_x3f(v_a_4756_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4863_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4767_ = v___x_4764_;
v_isShared_4768_ = v_isSharedCheck_4863_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4764_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4863_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___f_4773_; 
v___x_4769_ = lean_box(v___x_4709_);
v___x_4770_ = lean_box(v_compile_4710_);
v___x_4771_ = lean_box(v_logCompileErrors_4711_);
v___x_4772_ = lean_box(v_isMeta_4712_);
lean_inc(v_a_4756_);
lean_inc(v___x_4762_);
lean_inc(v___x_4750_);
v___f_4773_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1___boxed), 14, 8);
lean_closure_set(v___f_4773_, 0, v___x_4750_);
lean_closure_set(v___f_4773_, 1, v___x_4762_);
lean_closure_set(v___f_4773_, 2, v___x_4759_);
lean_closure_set(v___f_4773_, 3, v_a_4756_);
lean_closure_set(v___f_4773_, 4, v___x_4769_);
lean_closure_set(v___f_4773_, 5, v___x_4770_);
lean_closure_set(v___f_4773_, 6, v___x_4771_);
lean_closure_set(v___f_4773_, 7, v___x_4772_);
if (lean_obj_tag(v_a_4765_) == 0)
{
lean_del_object(v___x_4767_);
goto v___jp_4776_;
}
else
{
lean_dec_ref(v_a_4765_);
if (v___x_4709_ == 0)
{
lean_del_object(v___x_4767_);
goto v___jp_4776_;
}
else
{
lean_object* v_options_4824_; lean_object* v_a_4826_; lean_object* v___y_4829_; uint8_t v___y_4830_; lean_object* v_a_4835_; lean_object* v___y_4839_; lean_object* v___x_4843_; uint8_t v___x_4844_; 
lean_dec_ref(v___f_4773_);
lean_dec(v_userName_4753_);
v_options_4824_ = lean_ctor_get(v___y_4719_, 2);
v___x_4843_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4844_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4824_, v___x_4843_);
if (v___x_4844_ == 0)
{
lean_object* v___x_4845_; 
lean_del_object(v___x_4767_);
lean_inc(v___x_4762_);
v___x_4845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_4762_, v_a_4756_, v_compile_4710_, v_logCompileErrors_4711_, v_isMeta_4712_, v___x_4750_, v___x_4759_, v___x_4759_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4845_;
goto v___jp_4727_;
}
else
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = lean_box(0);
lean_inc(v_a_4756_);
v___x_4847_ = l_Lean_Meta_trySynthInstance(v_a_4756_, v___x_4846_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v_a_4848_; 
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
lean_inc(v_a_4848_);
lean_dec_ref(v___x_4847_);
if (lean_obj_tag(v_a_4848_) == 1)
{
lean_object* v_a_4849_; lean_object* v___x_4850_; 
v_a_4849_ = lean_ctor_get(v_a_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref(v_a_4848_);
v___x_4850_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_4760_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; uint8_t v___x_4852_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref(v___x_4850_);
v___x_4852_ = lean_unbox(v_a_4851_);
lean_dec(v_a_4851_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; 
lean_inc(v___x_4750_);
v___x_4853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_4750_, v_a_4849_, v___x_4759_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4839_ = v___x_4853_;
goto v___jp_4838_;
}
else
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4854_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__2);
lean_inc(v_a_4849_);
v___x_4855_ = l_Lean_MessageData_ofExpr(v_a_4849_);
v___x_4856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4854_);
lean_ctor_set(v___x_4856_, 1, v___x_4855_);
v___x_4857_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4760_, v___x_4856_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4859_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref(v___x_4857_);
lean_inc(v___x_4750_);
v___x_4859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__5(v___x_4750_, v_a_4849_, v_a_4858_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4839_ = v___x_4859_;
goto v___jp_4838_;
}
else
{
lean_object* v_a_4860_; 
lean_dec(v_a_4849_);
v_a_4860_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4860_);
lean_dec_ref(v___x_4857_);
v_a_4835_ = v_a_4860_;
goto v___jp_4834_;
}
}
}
else
{
lean_object* v_a_4861_; 
lean_dec(v_a_4849_);
v_a_4861_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4861_);
lean_dec_ref(v___x_4850_);
v_a_4835_ = v_a_4861_;
goto v___jp_4834_;
}
}
else
{
lean_dec(v_a_4848_);
lean_del_object(v___x_4767_);
v_a_4826_ = v___x_4759_;
goto v___jp_4825_;
}
}
else
{
lean_object* v_a_4862_; 
v_a_4862_ = lean_ctor_get(v___x_4847_, 0);
lean_inc(v_a_4862_);
lean_dec_ref(v___x_4847_);
v_a_4835_ = v_a_4862_;
goto v___jp_4834_;
}
}
v___jp_4825_:
{
lean_object* v___x_4827_; 
lean_inc(v___x_4762_);
v___x_4827_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_4762_, v_a_4756_, v_compile_4710_, v_logCompileErrors_4711_, v_isMeta_4712_, v___x_4750_, v___x_4759_, v_a_4826_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4827_;
goto v___jp_4727_;
}
v___jp_4828_:
{
if (v___y_4830_ == 0)
{
lean_dec_ref(v___y_4829_);
lean_del_object(v___x_4767_);
v_a_4826_ = v___x_4759_;
goto v___jp_4825_;
}
else
{
lean_object* v___x_4832_; 
lean_dec(v_a_4756_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
if (v_isShared_4768_ == 0)
{
lean_ctor_set_tag(v___x_4767_, 1);
lean_ctor_set(v___x_4767_, 0, v___y_4829_);
v___x_4832_ = v___x_4767_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___y_4829_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
v___jp_4834_:
{
uint8_t v___x_4836_; 
v___x_4836_ = l_Lean_Exception_isInterrupt(v_a_4835_);
if (v___x_4836_ == 0)
{
uint8_t v___x_4837_; 
lean_inc_ref(v_a_4835_);
v___x_4837_ = l_Lean_Exception_isRuntime(v_a_4835_);
v___y_4829_ = v_a_4835_;
v___y_4830_ = v___x_4837_;
goto v___jp_4828_;
}
else
{
v___y_4829_ = v_a_4835_;
v___y_4830_ = v___x_4836_;
goto v___jp_4828_;
}
}
v___jp_4838_:
{
if (lean_obj_tag(v___y_4839_) == 0)
{
lean_object* v_a_4840_; 
lean_del_object(v___x_4767_);
v_a_4840_ = lean_ctor_get(v___y_4839_, 0);
lean_inc(v_a_4840_);
lean_dec_ref(v___y_4839_);
if (lean_obj_tag(v_a_4840_) == 0)
{
lean_dec(v_a_4756_);
lean_dec(v___x_4750_);
v_a_4723_ = v___x_4759_;
goto v___jp_4722_;
}
else
{
lean_object* v_a_4841_; 
v_a_4841_ = lean_ctor_get(v_a_4840_, 0);
lean_inc(v_a_4841_);
lean_dec_ref(v_a_4840_);
v_a_4826_ = v_a_4841_;
goto v___jp_4825_;
}
}
else
{
lean_object* v_a_4842_; 
v_a_4842_ = lean_ctor_get(v___y_4839_, 0);
lean_inc(v_a_4842_);
lean_dec_ref(v___y_4839_);
v_a_4835_ = v_a_4842_;
goto v___jp_4834_;
}
}
}
}
v___jp_4774_:
{
lean_object* v___x_4775_; 
lean_inc(v___x_4762_);
v___x_4775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(v___x_4750_, v___x_4762_, v___x_4759_, v_a_4756_, v___x_4709_, v_compile_4710_, v_logCompileErrors_4711_, v_isMeta_4712_, v___x_4759_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4775_;
goto v___jp_4727_;
}
v___jp_4776_:
{
lean_object* v_options_4777_; lean_object* v___x_4778_; uint8_t v___x_4779_; 
v_options_4777_ = lean_ctor_get(v___y_4719_, 2);
v___x_4778_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4779_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4777_, v___x_4778_);
if (v___x_4779_ == 0)
{
lean_object* v___x_4780_; 
lean_dec_ref(v___f_4773_);
lean_dec(v_userName_4753_);
lean_inc(v___x_4762_);
v___x_4780_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___lam__1(v___x_4750_, v___x_4762_, v___x_4759_, v_a_4756_, v___x_4709_, v_compile_4710_, v_logCompileErrors_4711_, v_isMeta_4712_, v___x_4759_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4780_;
goto v___jp_4727_;
}
else
{
lean_object* v___x_4781_; 
lean_inc(v_userName_4753_);
lean_inc(v_val_4713_);
v___x_4781_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin(v_val_4713_, v_userName_4753_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; lean_object* v_fst_4783_; lean_object* v_snd_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4815_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_a_4782_);
lean_dec_ref(v___x_4781_);
v_fst_4783_ = lean_ctor_get(v_a_4782_, 0);
v_snd_4784_ = lean_ctor_get(v_a_4782_, 1);
v_isSharedCheck_4815_ = !lean_is_exclusive(v_a_4782_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4786_ = v_a_4782_;
v_isShared_4787_ = v_isSharedCheck_4815_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_snd_4784_);
lean_inc(v_fst_4783_);
lean_dec(v_a_4782_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4815_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
uint8_t v___x_4788_; 
v___x_4788_ = lean_name_eq(v_fst_4783_, v_val_4713_);
if (v___x_4788_ == 0)
{
if (v___x_4709_ == 0)
{
lean_del_object(v___x_4786_);
lean_dec(v_snd_4784_);
lean_dec(v_fst_4783_);
lean_dec_ref(v___f_4773_);
lean_dec(v_userName_4753_);
goto v___jp_4774_;
}
else
{
lean_object* v___x_4789_; 
lean_dec(v_a_4756_);
v___x_4789_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_4760_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v_a_4790_; uint8_t v___x_4791_; 
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
lean_inc(v_a_4790_);
lean_dec_ref(v___x_4789_);
v___x_4791_ = lean_unbox(v_a_4790_);
lean_dec(v_a_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; 
lean_del_object(v___x_4786_);
lean_dec(v_userName_4753_);
lean_inc_ref(v_expectedType_4714_);
lean_inc(v_val_4713_);
v___x_4792_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5(v_val_4713_, v_fst_4783_, v_expectedType_4714_, v___f_4761_, v___f_4773_, v___x_4759_, v_cls_4760_, v_snd_4784_, v___x_4750_, v___x_4759_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4792_;
goto v___jp_4727_;
}
else
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4796_; 
v___x_4793_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__4);
v___x_4794_ = l_Lean_MessageData_ofName(v_userName_4753_);
if (v_isShared_4787_ == 0)
{
lean_ctor_set_tag(v___x_4786_, 7);
lean_ctor_set(v___x_4786_, 1, v___x_4794_);
lean_ctor_set(v___x_4786_, 0, v___x_4793_);
v___x_4796_ = v___x_4786_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4793_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v___x_4794_);
v___x_4796_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4797_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__6);
v___x_4798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4796_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
lean_inc(v_fst_4783_);
v___x_4799_ = l_Lean_MessageData_ofName(v_fst_4783_);
v___x_4800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4798_);
lean_ctor_set(v___x_4800_, 1, v___x_4799_);
v___x_4801_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_4802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4800_);
lean_ctor_set(v___x_4802_, 1, v___x_4801_);
v___x_4803_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4760_, v___x_4802_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4804_);
lean_dec_ref(v___x_4803_);
lean_inc_ref(v_expectedType_4714_);
lean_inc(v_val_4713_);
v___x_4805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5(v_val_4713_, v_fst_4783_, v_expectedType_4714_, v___f_4761_, v___f_4773_, v___x_4759_, v_cls_4760_, v_snd_4784_, v___x_4750_, v_a_4804_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4805_;
goto v___jp_4727_;
}
else
{
lean_dec(v_snd_4784_);
lean_dec(v_fst_4783_);
lean_dec_ref(v___f_4773_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
return v___x_4803_;
}
}
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_del_object(v___x_4786_);
lean_dec(v_snd_4784_);
lean_dec(v_fst_4783_);
lean_dec_ref(v___f_4773_);
lean_dec(v_userName_4753_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4807_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4789_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4789_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
}
else
{
lean_del_object(v___x_4786_);
lean_dec(v_snd_4784_);
lean_dec(v_fst_4783_);
lean_dec_ref(v___f_4773_);
lean_dec(v_userName_4753_);
goto v___jp_4774_;
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
lean_dec_ref(v___f_4773_);
lean_dec(v_a_4756_);
lean_dec(v_userName_4753_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4816_ = lean_ctor_get(v___x_4781_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4781_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4781_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4781_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
lean_dec(v_a_4756_);
lean_dec(v_userName_4753_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4864_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4764_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4764_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4869_; 
if (v_isShared_4867_ == 0)
{
v___x_4869_ = v___x_4866_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
}
else
{
lean_object* v___x_4872_; 
lean_dec(v_userName_4753_);
lean_inc(v___y_4720_);
lean_inc_ref(v___y_4719_);
lean_inc(v___y_4718_);
lean_inc_ref(v___y_4717_);
lean_inc(v___x_4762_);
v___x_4872_ = lean_infer_type(v___x_4762_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc_n(v_a_4873_, 2);
lean_dec_ref(v___x_4872_);
lean_inc(v_a_4756_);
v___x_4874_ = l_Lean_Meta_isExprDefEq(v_a_4756_, v_a_4873_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___f_4876_; uint8_t v___x_4877_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref(v___x_4874_);
v___f_4876_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__7));
v___x_4877_ = lean_unbox(v_a_4875_);
lean_dec(v_a_4875_);
if (v___x_4877_ == 0)
{
lean_object* v___x_4878_; 
v___x_4878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__0(v_cls_4760_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4878_) == 0)
{
lean_object* v_a_4879_; uint8_t v___x_4880_; 
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
lean_inc(v_a_4879_);
lean_dec_ref(v___x_4878_);
v___x_4880_ = lean_unbox(v_a_4879_);
lean_dec(v_a_4879_);
if (v___x_4880_ == 0)
{
lean_object* v___x_4881_; 
lean_dec(v_a_4873_);
lean_inc(v___x_4762_);
v___x_4881_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_4756_, v___x_4762_, v___x_4709_, v___x_4750_, v___f_4876_, v___x_4759_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4881_;
goto v___jp_4727_;
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; 
v___x_4882_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__9);
lean_inc(v_a_4715_);
v___x_4883_ = l_Nat_reprFast(v_a_4715_);
v___x_4884_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4883_);
v___x_4885_ = l_Lean_MessageData_ofFormat(v___x_4884_);
v___x_4886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4882_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__11);
v___x_4888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4886_);
lean_ctor_set(v___x_4888_, 1, v___x_4887_);
lean_inc(v_a_4756_);
v___x_4889_ = l_Lean_MessageData_ofExpr(v_a_4756_);
v___x_4890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4888_);
lean_ctor_set(v___x_4890_, 1, v___x_4889_);
v___x_4891_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__13);
v___x_4892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4890_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = l_Lean_MessageData_ofExpr(v_a_4873_);
v___x_4894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4892_);
lean_ctor_set(v___x_4894_, 1, v___x_4893_);
v___x_4895_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___closed__15);
v___x_4896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4894_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
lean_inc(v___x_4762_);
v___x_4897_ = l_Lean_MessageData_ofExpr(v___x_4762_);
v___x_4898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4896_);
lean_ctor_set(v___x_4898_, 1, v___x_4897_);
v___x_4899_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4760_, v___x_4898_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4901_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_a_4900_);
lean_dec_ref(v___x_4899_);
lean_inc(v___x_4762_);
v___x_4901_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__7(v_a_4756_, v___x_4762_, v___x_4709_, v___x_4750_, v___f_4876_, v_a_4900_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4901_;
goto v___jp_4727_;
}
else
{
lean_dec(v_a_4756_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
return v___x_4899_;
}
}
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
lean_dec(v_a_4873_);
lean_dec(v_a_4756_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4902_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4878_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4878_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_object* v___x_4910_; 
lean_dec(v_a_4873_);
lean_dec(v_a_4756_);
lean_inc(v___x_4762_);
v___x_4910_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_4750_, v___x_4762_, v___y_4718_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref(v___x_4910_);
v___x_4912_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__6(v___x_4759_, v_a_4911_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
v___y_4728_ = v___x_4912_;
goto v___jp_4727_;
}
else
{
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
return v___x_4910_;
}
}
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec(v_a_4873_);
lean_dec(v_a_4756_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4913_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4874_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4874_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec(v_a_4756_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4921_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4872_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4872_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
else
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
lean_dec(v_a_4756_);
lean_dec(v_userName_4753_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4929_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4931_ = v___x_4757_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v___x_4757_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_a_4929_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4944_; 
lean_dec(v_userName_4753_);
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4937_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4939_ = v___x_4755_;
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4755_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4942_; 
if (v_isShared_4940_ == 0)
{
v___x_4942_ = v___x_4939_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_a_4937_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
else
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4952_; 
lean_dec(v___x_4750_);
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4945_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4947_ = v___x_4751_;
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4751_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4950_; 
if (v_isShared_4948_ == 0)
{
v___x_4950_ = v___x_4947_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4945_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
}
}
}
}
v___jp_4722_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = lean_unsigned_to_nat(1u);
v___x_4725_ = lean_nat_add(v_a_4715_, v___x_4724_);
lean_dec(v_a_4715_);
v_a_4715_ = v___x_4725_;
v_b_4716_ = v_a_4723_;
goto _start;
}
v___jp_4727_:
{
if (lean_obj_tag(v___y_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4738_; 
v_a_4729_ = lean_ctor_get(v___y_4728_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___y_4728_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4731_ = v___y_4728_;
v_isShared_4732_ = v_isSharedCheck_4738_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___y_4728_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4738_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
if (lean_obj_tag(v_a_4729_) == 0)
{
lean_object* v_a_4733_; lean_object* v___x_4735_; 
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4733_ = lean_ctor_get(v_a_4729_, 0);
lean_inc(v_a_4733_);
lean_dec_ref(v_a_4729_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v_a_4733_);
v___x_4735_ = v___x_4731_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4733_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
else
{
lean_object* v_a_4737_; 
lean_del_object(v___x_4731_);
v_a_4737_ = lean_ctor_get(v_a_4729_, 0);
lean_inc(v_a_4737_);
lean_dec_ref(v_a_4729_);
v_a_4723_ = v_a_4737_;
goto v___jp_4722_;
}
}
}
else
{
lean_object* v_a_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4746_; 
lean_dec(v_a_4715_);
lean_dec_ref(v_expectedType_4714_);
lean_dec(v_val_4713_);
v_a_4739_ = lean_ctor_get(v___y_4728_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___y_4728_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4741_ = v___y_4728_;
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_a_4739_);
lean_dec(v___y_4728_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4744_; 
if (v_isShared_4742_ == 0)
{
v___x_4744_ = v___x_4741_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4739_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25(lean_object* v_inst_4953_, lean_object* v_expectedType_4954_, uint8_t v___x_4955_, uint8_t v_compile_4956_, uint8_t v_logCompileErrors_4957_, uint8_t v_isMeta_4958_, lean_object* v_val_4959_, lean_object* v_x_4960_, lean_object* v_x_4961_, lean_object* v_x_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_5008_; lean_object* v___y_5009_; lean_object* v___y_5010_; lean_object* v_options_5011_; lean_object* v___y_5012_; 
if (lean_obj_tag(v_x_4960_) == 5)
{
lean_object* v_fn_5080_; lean_object* v_arg_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v_fn_5080_ = lean_ctor_get(v_x_4960_, 0);
lean_inc_ref(v_fn_5080_);
v_arg_5081_ = lean_ctor_get(v_x_4960_, 1);
lean_inc_ref(v_arg_5081_);
lean_dec_ref(v_x_4960_);
v___x_5082_ = lean_array_set(v_x_4961_, v_x_4962_, v_arg_5081_);
v___x_5083_ = lean_unsigned_to_nat(1u);
v___x_5084_ = lean_nat_sub(v_x_4962_, v___x_5083_);
lean_dec(v_x_4962_);
v_x_4960_ = v_fn_5080_;
v_x_4961_ = v___x_5082_;
v_x_4962_ = v___x_5084_;
goto _start;
}
else
{
lean_object* v_cls_5086_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5091_; lean_object* v___x_5109_; 
lean_dec(v_x_4962_);
v_cls_5086_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5109_ = l_Lean_Expr_constName_x3f(v_x_4960_);
if (lean_obj_tag(v___x_5109_) == 0)
{
lean_dec_ref(v_x_4961_);
lean_dec_ref(v_x_4960_);
lean_dec(v_val_4959_);
v___y_5088_ = v___y_4963_;
v___y_5089_ = v___y_4964_;
v___y_5090_ = v___y_4965_;
v___y_5091_ = v___y_4966_;
goto v___jp_5087_;
}
else
{
lean_object* v_val_5110_; lean_object* v___x_5111_; 
v_val_5110_ = lean_ctor_get(v___x_5109_, 0);
lean_inc(v_val_5110_);
lean_dec_ref(v___x_5109_);
v___x_5111_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_5110_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_5111_) == 0)
{
lean_object* v_a_5112_; 
v_a_5112_ = lean_ctor_get(v___x_5111_, 0);
lean_inc(v_a_5112_);
lean_dec_ref(v___x_5111_);
if (lean_obj_tag(v_a_5112_) == 6)
{
lean_object* v_val_5113_; lean_object* v___x_5114_; 
lean_dec_ref(v_inst_4953_);
v_val_5113_ = lean_ctor_get(v_a_5112_, 0);
lean_inc_ref(v_val_5113_);
lean_dec_ref(v_a_5112_);
lean_inc(v___y_4966_);
lean_inc_ref(v___y_4965_);
lean_inc(v___y_4964_);
lean_inc_ref(v___y_4963_);
lean_inc_ref(v_x_4960_);
v___x_5114_ = lean_infer_type(v_x_4960_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_5114_) == 0)
{
lean_object* v_a_5115_; uint8_t v___x_5116_; lean_object* v___x_5117_; 
v_a_5115_ = lean_ctor_get(v___x_5114_, 0);
lean_inc(v_a_5115_);
lean_dec_ref(v___x_5114_);
v___x_5116_ = 0;
v___x_5117_ = l_Lean_Meta_forallMetaTelescope(v_a_5115_, v___x_5116_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v_a_5118_; lean_object* v_snd_5119_; lean_object* v_fst_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5220_; 
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc(v_a_5118_);
lean_dec_ref(v___x_5117_);
v_snd_5119_ = lean_ctor_get(v_a_5118_, 1);
v_fst_5120_ = lean_ctor_get(v_a_5118_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v_a_5118_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5122_ = v_a_5118_;
v_isShared_5123_ = v_isSharedCheck_5220_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_snd_5119_);
lean_inc(v_fst_5120_);
lean_dec(v_a_5118_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5220_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v_snd_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5218_; 
v_snd_5124_ = lean_ctor_get(v_snd_5119_, 1);
v_isSharedCheck_5218_ = !lean_is_exclusive(v_snd_5119_);
if (v_isSharedCheck_5218_ == 0)
{
lean_object* v_unused_5219_; 
v_unused_5219_ = lean_ctor_get(v_snd_5119_, 0);
lean_dec(v_unused_5219_);
v___x_5126_ = v_snd_5119_;
v_isShared_5127_ = v_isSharedCheck_5218_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_snd_5124_);
lean_dec(v_snd_5119_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5218_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5128_; lean_object* v___y_5130_; lean_object* v___y_5131_; lean_object* v___y_5132_; lean_object* v___y_5133_; lean_object* v___x_5165_; uint8_t v___x_5166_; 
v___x_5128_ = lean_array_get_size(v_x_4961_);
v___x_5165_ = lean_array_get_size(v_fst_5120_);
v___x_5166_ = lean_nat_dec_eq(v___x_5128_, v___x_5165_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5170_; 
lean_dec(v_snd_5124_);
lean_dec(v_fst_5120_);
lean_dec_ref(v_val_5113_);
lean_dec(v_val_4959_);
lean_dec_ref(v_expectedType_4954_);
v___x_5167_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_5168_ = l_Lean_MessageData_ofExpr(v_x_4960_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set_tag(v___x_5126_, 7);
lean_ctor_set(v___x_5126_, 1, v___x_5168_);
lean_ctor_set(v___x_5126_, 0, v___x_5167_);
v___x_5170_ = v___x_5126_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v___x_5167_);
lean_ctor_set(v_reuseFailAlloc_5181_, 1, v___x_5168_);
v___x_5170_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5171_; lean_object* v___x_5173_; 
v___x_5171_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3);
if (v_isShared_5123_ == 0)
{
lean_ctor_set_tag(v___x_5122_, 7);
lean_ctor_set(v___x_5122_, 1, v___x_5171_);
lean_ctor_set(v___x_5122_, 0, v___x_5170_);
v___x_5173_ = v___x_5122_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5170_);
lean_ctor_set(v_reuseFailAlloc_5180_, 1, v___x_5171_);
v___x_5173_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5174_ = lean_array_to_list(v_x_4961_);
v___x_5175_ = lean_box(0);
v___x_5176_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_5174_, v___x_5175_);
v___x_5177_ = l_Lean_MessageData_ofList(v___x_5176_);
v___x_5178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5178_, 0, v___x_5173_);
lean_ctor_set(v___x_5178_, 1, v___x_5177_);
v___x_5179_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5178_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
return v___x_5179_;
}
}
}
else
{
lean_object* v___x_5182_; 
lean_inc_ref(v_expectedType_4954_);
v___x_5182_ = l_Lean_Meta_isExprDefEq(v_expectedType_4954_, v_snd_5124_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; uint8_t v___x_5184_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
lean_dec_ref(v___x_5182_);
v___x_5184_ = lean_unbox(v_a_5183_);
if (v___x_5184_ == 0)
{
lean_object* v_toConstantVal_5185_; lean_object* v_name_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5190_; 
lean_dec(v_fst_5120_);
lean_dec_ref(v_x_4961_);
lean_dec_ref(v_x_4960_);
lean_dec(v_val_4959_);
v_toConstantVal_5185_ = lean_ctor_get(v_val_5113_, 0);
lean_inc_ref(v_toConstantVal_5185_);
lean_dec_ref(v_val_5113_);
v_name_5186_ = lean_ctor_get(v_toConstantVal_5185_, 0);
lean_inc(v_name_5186_);
lean_dec_ref(v_toConstantVal_5185_);
v___x_5187_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_5188_ = l_Lean_MessageData_ofExpr(v_expectedType_4954_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set_tag(v___x_5126_, 7);
lean_ctor_set(v___x_5126_, 1, v___x_5188_);
lean_ctor_set(v___x_5126_, 0, v___x_5187_);
v___x_5190_ = v___x_5126_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5187_);
lean_ctor_set(v_reuseFailAlloc_5209_, 1, v___x_5188_);
v___x_5190_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
lean_object* v___x_5191_; lean_object* v___x_5193_; 
v___x_5191_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_5123_ == 0)
{
lean_ctor_set_tag(v___x_5122_, 7);
lean_ctor_set(v___x_5122_, 1, v___x_5191_);
lean_ctor_set(v___x_5122_, 0, v___x_5190_);
v___x_5193_ = v___x_5122_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v___x_5190_);
lean_ctor_set(v_reuseFailAlloc_5208_, 1, v___x_5191_);
v___x_5193_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
uint8_t v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5207_; 
v___x_5194_ = lean_unbox(v_a_5183_);
lean_dec(v_a_5183_);
v___x_5195_ = l_Lean_MessageData_ofConstName(v_name_5186_, v___x_5194_);
v___x_5196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5193_);
lean_ctor_set(v___x_5196_, 1, v___x_5195_);
v___x_5197_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_5198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5196_);
lean_ctor_set(v___x_5198_, 1, v___x_5197_);
v___x_5199_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5198_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5205_; 
if (v_isShared_5203_ == 0)
{
v___x_5205_ = v___x_5202_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_a_5200_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
}
}
else
{
lean_dec(v_a_5183_);
lean_del_object(v___x_5126_);
lean_del_object(v___x_5122_);
v___y_5130_ = v___y_4963_;
v___y_5131_ = v___y_4964_;
v___y_5132_ = v___y_4965_;
v___y_5133_ = v___y_4966_;
goto v___jp_5129_;
}
}
else
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
lean_del_object(v___x_5126_);
lean_del_object(v___x_5122_);
lean_dec(v_fst_5120_);
lean_dec_ref(v_val_5113_);
lean_dec_ref(v_x_4961_);
lean_dec_ref(v_x_4960_);
lean_dec(v_val_4959_);
lean_dec_ref(v_expectedType_4954_);
v_a_5210_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5182_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5182_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
v___jp_5129_:
{
lean_object* v_numParams_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; 
v_numParams_5134_ = lean_ctor_get(v_val_5113_, 3);
lean_inc(v_numParams_5134_);
lean_dec_ref(v_val_5113_);
v___x_5135_ = lean_box(0);
v___x_5136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(v___x_5128_, v_fst_5120_, v_x_4961_, v___x_4955_, v_compile_4956_, v_logCompileErrors_4957_, v_isMeta_4958_, v_val_4959_, v_expectedType_4954_, v_numParams_5134_, v___x_5135_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
lean_dec_ref(v_x_4961_);
if (lean_obj_tag(v___x_5136_) == 0)
{
size_t v_sz_5137_; size_t v___x_5138_; lean_object* v___x_5139_; 
lean_dec_ref(v___x_5136_);
v_sz_5137_ = lean_array_size(v_fst_5120_);
v___x_5138_ = ((size_t)0ULL);
v___x_5139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_5137_, v___x_5138_, v_fst_5120_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5148_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5142_ = v___x_5139_;
v_isShared_5143_ = v_isSharedCheck_5148_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5139_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5148_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5144_; lean_object* v___x_5146_; 
v___x_5144_ = l_Lean_mkAppN(v_x_4960_, v_a_5140_);
lean_dec(v_a_5140_);
if (v_isShared_5143_ == 0)
{
lean_ctor_set(v___x_5142_, 0, v___x_5144_);
v___x_5146_ = v___x_5142_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v___x_5144_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec_ref(v_x_4960_);
v_a_5149_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5139_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5139_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec(v_fst_5120_);
lean_dec_ref(v_x_4960_);
v_a_5157_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5136_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5136_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
lean_dec_ref(v_val_5113_);
lean_dec_ref(v_x_4961_);
lean_dec_ref(v_x_4960_);
lean_dec(v_val_4959_);
lean_dec_ref(v_expectedType_4954_);
v_a_5221_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5117_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5117_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
else
{
lean_dec_ref(v_val_5113_);
lean_dec_ref(v_x_4961_);
lean_dec_ref(v_x_4960_);
lean_dec(v_val_4959_);
lean_dec_ref(v_expectedType_4954_);
return v___x_5114_;
}
}
else
{
lean_dec(v_a_5112_);
lean_dec_ref(v_x_4961_);
lean_dec_ref(v_x_4960_);
lean_dec(v_val_4959_);
v___y_5088_ = v___y_4963_;
v___y_5089_ = v___y_4964_;
v___y_5090_ = v___y_4965_;
v___y_5091_ = v___y_4966_;
goto v___jp_5087_;
}
}
else
{
lean_object* v_a_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5236_; 
lean_dec_ref(v_x_4961_);
lean_dec_ref(v_x_4960_);
lean_dec(v_val_4959_);
lean_dec_ref(v_expectedType_4954_);
lean_dec_ref(v_inst_4953_);
v_a_5229_ = lean_ctor_get(v___x_5111_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5111_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5231_ = v___x_5111_;
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5111_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
v_resetjp_5230_:
{
lean_object* v___x_5234_; 
if (v_isShared_5232_ == 0)
{
v___x_5234_ = v___x_5231_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_a_5229_);
v___x_5234_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
return v___x_5234_;
}
}
}
}
v___jp_5087_:
{
lean_object* v_options_5092_; uint8_t v_hasTrace_5093_; 
v_options_5092_ = lean_ctor_get(v___y_5090_, 2);
v_hasTrace_5093_ = lean_ctor_get_uint8(v_options_5092_, sizeof(void*)*1);
if (v_hasTrace_5093_ == 0)
{
v___y_5008_ = v___y_5088_;
v___y_5009_ = v___y_5089_;
v___y_5010_ = v___y_5090_;
v_options_5011_ = v_options_5092_;
v___y_5012_ = v___y_5091_;
goto v___jp_5007_;
}
else
{
lean_object* v_inheritedTraceOptions_5094_; lean_object* v___x_5095_; uint8_t v___x_5096_; 
v_inheritedTraceOptions_5094_ = lean_ctor_get(v___y_5090_, 13);
v___x_5095_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_5096_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5094_, v_options_5092_, v___x_5095_);
if (v___x_5096_ == 0)
{
v___y_5008_ = v___y_5088_;
v___y_5009_ = v___y_5089_;
v___y_5010_ = v___y_5090_;
v_options_5011_ = v_options_5092_;
v___y_5012_ = v___y_5091_;
goto v___jp_5007_;
}
else
{
lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___x_5097_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_4953_);
v___x_5098_ = l_Lean_MessageData_ofExpr(v_inst_4953_);
v___x_5099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set(v___x_5099_, 1, v___x_5098_);
v___x_5100_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5086_, v___x_5099_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
if (lean_obj_tag(v___x_5100_) == 0)
{
lean_dec_ref(v___x_5100_);
v___y_5008_ = v___y_5088_;
v___y_5009_ = v___y_5089_;
v___y_5010_ = v___y_5090_;
v_options_5011_ = v_options_5092_;
v___y_5012_ = v___y_5091_;
goto v___jp_5007_;
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
lean_dec_ref(v_expectedType_4954_);
lean_dec_ref(v_inst_4953_);
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___x_5100_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
if (v_isShared_5104_ == 0)
{
v___x_5106_ = v___x_5103_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
}
}
}
}
v___jp_4968_:
{
lean_object* v___x_4973_; 
v___x_4973_ = l_Lean_enableRealizationsForConst(v___y_4970_, v___y_4971_, v___y_4972_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4980_ == 0)
{
lean_object* v_unused_4981_; 
v_unused_4981_ = lean_ctor_get(v___x_4973_, 0);
lean_dec(v_unused_4981_);
v___x_4975_ = v___x_4973_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_dec(v___x_4973_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
lean_ctor_set(v___x_4975_, 0, v___y_4969_);
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___y_4969_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
else
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4989_; 
lean_dec_ref(v___y_4969_);
v_a_4982_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4984_ = v___x_4973_;
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4973_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4989_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4987_; 
if (v_isShared_4985_ == 0)
{
v___x_4987_ = v___x_4984_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4982_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
return v___x_4987_;
}
}
}
}
v___jp_4990_:
{
if (v_compile_4956_ == 0)
{
v___y_4969_ = v___y_4991_;
v___y_4970_ = v___y_4992_;
v___y_4971_ = v___y_4993_;
v___y_4972_ = v___y_4994_;
goto v___jp_4968_;
}
else
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4995_ = lean_unsigned_to_nat(1u);
v___x_4996_ = lean_mk_empty_array_with_capacity(v___x_4995_);
lean_inc(v___y_4992_);
v___x_4997_ = lean_array_push(v___x_4996_, v___y_4992_);
v___x_4998_ = l_Lean_compileDecls(v___x_4997_, v_logCompileErrors_4957_, v___y_4993_, v___y_4994_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_dec_ref(v___x_4998_);
v___y_4969_ = v___y_4991_;
v___y_4970_ = v___y_4992_;
v___y_4971_ = v___y_4993_;
v___y_4972_ = v___y_4994_;
goto v___jp_4968_;
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec(v___y_4992_);
lean_dec_ref(v___y_4991_);
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4998_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4998_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
v___jp_5007_:
{
lean_object* v___x_5013_; uint8_t v___x_5014_; 
v___x_5013_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5014_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5011_, v___x_5013_);
if (v___x_5014_ == 0)
{
lean_object* v___x_5015_; 
lean_dec_ref(v_expectedType_4954_);
v___x_5015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5015_, 0, v_inst_4953_);
return v___x_5015_;
}
else
{
lean_object* v___x_5016_; 
lean_inc(v___y_5012_);
lean_inc_ref(v___y_5010_);
lean_inc(v___y_5009_);
lean_inc_ref(v___y_5008_);
lean_inc_ref(v_inst_4953_);
v___x_5016_ = lean_infer_type(v_inst_4953_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5012_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v___x_5018_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5017_);
lean_dec_ref(v___x_5016_);
lean_inc_ref(v_expectedType_4954_);
v___x_5018_ = l_Lean_Meta_isExprDefEq(v_expectedType_4954_, v_a_5017_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5012_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5071_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5021_ = v___x_5018_;
v_isShared_5022_ = v_isSharedCheck_5071_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5071_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
uint8_t v___x_5023_; 
v___x_5023_ = lean_unbox(v_a_5019_);
if (v___x_5023_ == 0)
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v_a_5026_; uint8_t v___x_5027_; uint8_t v___x_5028_; lean_object* v___x_5029_; 
lean_del_object(v___x_5021_);
v___x_5024_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_5025_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_5024_, v___y_5012_);
v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
lean_inc_n(v_a_5026_, 2);
lean_dec_ref(v___x_5025_);
v___x_5027_ = lean_unbox(v_a_5019_);
v___x_5028_ = lean_unbox(v_a_5019_);
lean_dec(v_a_5019_);
v___x_5029_ = l_Lean_Meta_mkAuxDefinition(v_a_5026_, v_expectedType_4954_, v_inst_4953_, v___x_5027_, v___x_5028_, v___x_4955_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5012_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_a_5030_; uint8_t v___x_5031_; lean_object* v___x_5032_; 
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_a_5030_);
lean_dec_ref(v___x_5029_);
v___x_5031_ = 3;
lean_inc(v_a_5026_);
v___x_5032_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_5026_, v___x_5031_, v___y_5009_, v___y_5012_);
lean_dec_ref(v___x_5032_);
if (v_isMeta_4958_ == 0)
{
v___y_4991_ = v_a_5030_;
v___y_4992_ = v_a_5026_;
v___y_4993_ = v___y_5010_;
v___y_4994_ = v___y_5012_;
goto v___jp_4990_;
}
else
{
lean_object* v___x_5033_; lean_object* v_env_5034_; lean_object* v_nextMacroScope_5035_; lean_object* v_ngen_5036_; lean_object* v_auxDeclNGen_5037_; lean_object* v_traceState_5038_; lean_object* v_messages_5039_; lean_object* v_infoState_5040_; lean_object* v_snapshotTasks_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5066_; 
v___x_5033_ = lean_st_ref_take(v___y_5012_);
v_env_5034_ = lean_ctor_get(v___x_5033_, 0);
v_nextMacroScope_5035_ = lean_ctor_get(v___x_5033_, 1);
v_ngen_5036_ = lean_ctor_get(v___x_5033_, 2);
v_auxDeclNGen_5037_ = lean_ctor_get(v___x_5033_, 3);
v_traceState_5038_ = lean_ctor_get(v___x_5033_, 4);
v_messages_5039_ = lean_ctor_get(v___x_5033_, 6);
v_infoState_5040_ = lean_ctor_get(v___x_5033_, 7);
v_snapshotTasks_5041_ = lean_ctor_get(v___x_5033_, 8);
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5066_ == 0)
{
lean_object* v_unused_5067_; 
v_unused_5067_ = lean_ctor_get(v___x_5033_, 5);
lean_dec(v_unused_5067_);
v___x_5043_ = v___x_5033_;
v_isShared_5044_ = v_isSharedCheck_5066_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_snapshotTasks_5041_);
lean_inc(v_infoState_5040_);
lean_inc(v_messages_5039_);
lean_inc(v_traceState_5038_);
lean_inc(v_auxDeclNGen_5037_);
lean_inc(v_ngen_5036_);
lean_inc(v_nextMacroScope_5035_);
lean_inc(v_env_5034_);
lean_dec(v___x_5033_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5066_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5048_; 
lean_inc(v_a_5026_);
v___x_5045_ = l_Lean_markMeta(v_env_5034_, v_a_5026_);
v___x_5046_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_5044_ == 0)
{
lean_ctor_set(v___x_5043_, 5, v___x_5046_);
lean_ctor_set(v___x_5043_, 0, v___x_5045_);
v___x_5048_ = v___x_5043_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5045_);
lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_nextMacroScope_5035_);
lean_ctor_set(v_reuseFailAlloc_5065_, 2, v_ngen_5036_);
lean_ctor_set(v_reuseFailAlloc_5065_, 3, v_auxDeclNGen_5037_);
lean_ctor_set(v_reuseFailAlloc_5065_, 4, v_traceState_5038_);
lean_ctor_set(v_reuseFailAlloc_5065_, 5, v___x_5046_);
lean_ctor_set(v_reuseFailAlloc_5065_, 6, v_messages_5039_);
lean_ctor_set(v_reuseFailAlloc_5065_, 7, v_infoState_5040_);
lean_ctor_set(v_reuseFailAlloc_5065_, 8, v_snapshotTasks_5041_);
v___x_5048_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v_mctx_5051_; lean_object* v_zetaDeltaFVarIds_5052_; lean_object* v_postponed_5053_; lean_object* v_diag_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5063_; 
v___x_5049_ = lean_st_ref_set(v___y_5012_, v___x_5048_);
v___x_5050_ = lean_st_ref_take(v___y_5009_);
v_mctx_5051_ = lean_ctor_get(v___x_5050_, 0);
v_zetaDeltaFVarIds_5052_ = lean_ctor_get(v___x_5050_, 2);
v_postponed_5053_ = lean_ctor_get(v___x_5050_, 3);
v_diag_5054_ = lean_ctor_get(v___x_5050_, 4);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5063_ == 0)
{
lean_object* v_unused_5064_; 
v_unused_5064_ = lean_ctor_get(v___x_5050_, 1);
lean_dec(v_unused_5064_);
v___x_5056_ = v___x_5050_;
v_isShared_5057_ = v_isSharedCheck_5063_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_diag_5054_);
lean_inc(v_postponed_5053_);
lean_inc(v_zetaDeltaFVarIds_5052_);
lean_inc(v_mctx_5051_);
lean_dec(v___x_5050_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5063_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5058_; lean_object* v___x_5060_; 
v___x_5058_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 1, v___x_5058_);
v___x_5060_ = v___x_5056_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_mctx_5051_);
lean_ctor_set(v_reuseFailAlloc_5062_, 1, v___x_5058_);
lean_ctor_set(v_reuseFailAlloc_5062_, 2, v_zetaDeltaFVarIds_5052_);
lean_ctor_set(v_reuseFailAlloc_5062_, 3, v_postponed_5053_);
lean_ctor_set(v_reuseFailAlloc_5062_, 4, v_diag_5054_);
v___x_5060_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
lean_object* v___x_5061_; 
v___x_5061_ = lean_st_ref_set(v___y_5009_, v___x_5060_);
v___y_4991_ = v_a_5030_;
v___y_4992_ = v_a_5026_;
v___y_4993_ = v___y_5010_;
v___y_4994_ = v___y_5012_;
goto v___jp_4990_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5026_);
return v___x_5029_;
}
}
else
{
lean_object* v___x_5069_; 
lean_dec(v_a_5019_);
lean_dec_ref(v_expectedType_4954_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 0, v_inst_4953_);
v___x_5069_ = v___x_5021_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_inst_4953_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
lean_dec_ref(v_expectedType_4954_);
lean_dec_ref(v_inst_4953_);
v_a_5072_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5018_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5018_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
if (v_isShared_5075_ == 0)
{
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4954_);
lean_dec_ref(v_inst_4953_);
return v___x_5016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16(lean_object* v_inst_5237_, lean_object* v_expectedType_5238_, uint8_t v___x_5239_, uint8_t v_compile_5240_, uint8_t v_logCompileErrors_5241_, uint8_t v_isMeta_5242_, lean_object* v_val_5243_, lean_object* v_x_5244_, lean_object* v_x_5245_, lean_object* v_x_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v___y_5253_; lean_object* v___y_5254_; lean_object* v___y_5255_; lean_object* v___y_5256_; lean_object* v___y_5275_; lean_object* v___y_5276_; lean_object* v___y_5277_; lean_object* v___y_5278_; lean_object* v___y_5292_; lean_object* v___y_5293_; lean_object* v___y_5294_; lean_object* v_options_5295_; lean_object* v___y_5296_; 
if (lean_obj_tag(v_x_5244_) == 5)
{
lean_object* v_fn_5364_; lean_object* v_arg_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; 
v_fn_5364_ = lean_ctor_get(v_x_5244_, 0);
lean_inc_ref(v_fn_5364_);
v_arg_5365_ = lean_ctor_get(v_x_5244_, 1);
lean_inc_ref(v_arg_5365_);
lean_dec_ref(v_x_5244_);
v___x_5366_ = lean_array_set(v_x_5245_, v_x_5246_, v_arg_5365_);
v___x_5367_ = lean_unsigned_to_nat(1u);
v___x_5368_ = lean_nat_sub(v_x_5246_, v___x_5367_);
v___x_5369_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25(v_inst_5237_, v_expectedType_5238_, v___x_5239_, v_compile_5240_, v_logCompileErrors_5241_, v_isMeta_5242_, v_val_5243_, v_fn_5364_, v___x_5366_, v___x_5368_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
return v___x_5369_;
}
else
{
lean_object* v_cls_5370_; lean_object* v___y_5372_; lean_object* v___y_5373_; lean_object* v___y_5374_; lean_object* v___y_5375_; lean_object* v___x_5393_; 
v_cls_5370_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5393_ = l_Lean_Expr_constName_x3f(v_x_5244_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_dec_ref(v_x_5245_);
lean_dec_ref(v_x_5244_);
lean_dec(v_val_5243_);
v___y_5372_ = v___y_5247_;
v___y_5373_ = v___y_5248_;
v___y_5374_ = v___y_5249_;
v___y_5375_ = v___y_5250_;
goto v___jp_5371_;
}
else
{
lean_object* v_val_5394_; lean_object* v___x_5395_; 
v_val_5394_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_val_5394_);
lean_dec_ref(v___x_5393_);
v___x_5395_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_5394_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v_a_5396_; 
v_a_5396_ = lean_ctor_get(v___x_5395_, 0);
lean_inc(v_a_5396_);
lean_dec_ref(v___x_5395_);
if (lean_obj_tag(v_a_5396_) == 6)
{
lean_object* v_val_5397_; lean_object* v___x_5398_; 
lean_dec_ref(v_inst_5237_);
v_val_5397_ = lean_ctor_get(v_a_5396_, 0);
lean_inc_ref(v_val_5397_);
lean_dec_ref(v_a_5396_);
lean_inc(v___y_5250_);
lean_inc_ref(v___y_5249_);
lean_inc(v___y_5248_);
lean_inc_ref(v___y_5247_);
lean_inc_ref(v_x_5244_);
v___x_5398_ = lean_infer_type(v_x_5244_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
if (lean_obj_tag(v___x_5398_) == 0)
{
lean_object* v_a_5399_; uint8_t v___x_5400_; lean_object* v___x_5401_; 
v_a_5399_ = lean_ctor_get(v___x_5398_, 0);
lean_inc(v_a_5399_);
lean_dec_ref(v___x_5398_);
v___x_5400_ = 0;
v___x_5401_ = l_Lean_Meta_forallMetaTelescope(v_a_5399_, v___x_5400_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_object* v_a_5402_; lean_object* v_snd_5403_; lean_object* v_fst_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5504_; 
v_a_5402_ = lean_ctor_get(v___x_5401_, 0);
lean_inc(v_a_5402_);
lean_dec_ref(v___x_5401_);
v_snd_5403_ = lean_ctor_get(v_a_5402_, 1);
v_fst_5404_ = lean_ctor_get(v_a_5402_, 0);
v_isSharedCheck_5504_ = !lean_is_exclusive(v_a_5402_);
if (v_isSharedCheck_5504_ == 0)
{
v___x_5406_ = v_a_5402_;
v_isShared_5407_ = v_isSharedCheck_5504_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_snd_5403_);
lean_inc(v_fst_5404_);
lean_dec(v_a_5402_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5504_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v_snd_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5502_; 
v_snd_5408_ = lean_ctor_get(v_snd_5403_, 1);
v_isSharedCheck_5502_ = !lean_is_exclusive(v_snd_5403_);
if (v_isSharedCheck_5502_ == 0)
{
lean_object* v_unused_5503_; 
v_unused_5503_ = lean_ctor_get(v_snd_5403_, 0);
lean_dec(v_unused_5503_);
v___x_5410_ = v_snd_5403_;
v_isShared_5411_ = v_isSharedCheck_5502_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_snd_5408_);
lean_dec(v_snd_5403_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5502_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5412_; lean_object* v___y_5414_; lean_object* v___y_5415_; lean_object* v___y_5416_; lean_object* v___y_5417_; lean_object* v___x_5449_; uint8_t v___x_5450_; 
v___x_5412_ = lean_array_get_size(v_x_5245_);
v___x_5449_ = lean_array_get_size(v_fst_5404_);
v___x_5450_ = lean_nat_dec_eq(v___x_5412_, v___x_5449_);
if (v___x_5450_ == 0)
{
lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5454_; 
lean_dec(v_snd_5408_);
lean_dec(v_fst_5404_);
lean_dec_ref(v_val_5397_);
lean_dec(v_val_5243_);
lean_dec_ref(v_expectedType_5238_);
v___x_5451_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__3);
v___x_5452_ = l_Lean_MessageData_ofExpr(v_x_5244_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set_tag(v___x_5410_, 7);
lean_ctor_set(v___x_5410_, 1, v___x_5452_);
lean_ctor_set(v___x_5410_, 0, v___x_5451_);
v___x_5454_ = v___x_5410_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v___x_5451_);
lean_ctor_set(v_reuseFailAlloc_5465_, 1, v___x_5452_);
v___x_5454_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5455_; lean_object* v___x_5457_; 
v___x_5455_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___lam__5___closed__3);
if (v_isShared_5407_ == 0)
{
lean_ctor_set_tag(v___x_5406_, 7);
lean_ctor_set(v___x_5406_, 1, v___x_5455_);
lean_ctor_set(v___x_5406_, 0, v___x_5454_);
v___x_5457_ = v___x_5406_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5464_, 1, v___x_5455_);
v___x_5457_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; 
v___x_5458_ = lean_array_to_list(v_x_5245_);
v___x_5459_ = lean_box(0);
v___x_5460_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__9(v___x_5458_, v___x_5459_);
v___x_5461_ = l_Lean_MessageData_ofList(v___x_5460_);
v___x_5462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5462_, 0, v___x_5457_);
lean_ctor_set(v___x_5462_, 1, v___x_5461_);
v___x_5463_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5462_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
return v___x_5463_;
}
}
}
else
{
lean_object* v___x_5466_; 
lean_inc_ref(v_expectedType_5238_);
v___x_5466_ = l_Lean_Meta_isExprDefEq(v_expectedType_5238_, v_snd_5408_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; uint8_t v___x_5468_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
lean_inc(v_a_5467_);
lean_dec_ref(v___x_5466_);
v___x_5468_ = lean_unbox(v_a_5467_);
if (v___x_5468_ == 0)
{
lean_object* v_toConstantVal_5469_; lean_object* v_name_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5474_; 
lean_dec(v_fst_5404_);
lean_dec_ref(v_x_5245_);
lean_dec_ref(v_x_5244_);
lean_dec(v_val_5243_);
v_toConstantVal_5469_ = lean_ctor_get(v_val_5397_, 0);
lean_inc_ref(v_toConstantVal_5469_);
lean_dec_ref(v_val_5397_);
v_name_5470_ = lean_ctor_get(v_toConstantVal_5469_, 0);
lean_inc(v_name_5470_);
lean_dec_ref(v_toConstantVal_5469_);
v___x_5471_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__5);
v___x_5472_ = l_Lean_MessageData_ofExpr(v_expectedType_5238_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set_tag(v___x_5410_, 7);
lean_ctor_set(v___x_5410_, 1, v___x_5472_);
lean_ctor_set(v___x_5410_, 0, v___x_5471_);
v___x_5474_ = v___x_5410_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v___x_5472_);
v___x_5474_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
lean_object* v___x_5475_; lean_object* v___x_5477_; 
v___x_5475_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__7);
if (v_isShared_5407_ == 0)
{
lean_ctor_set_tag(v___x_5406_, 7);
lean_ctor_set(v___x_5406_, 1, v___x_5475_);
lean_ctor_set(v___x_5406_, 0, v___x_5474_);
v___x_5477_ = v___x_5406_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5474_);
lean_ctor_set(v_reuseFailAlloc_5492_, 1, v___x_5475_);
v___x_5477_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
uint8_t v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5491_; 
v___x_5478_ = lean_unbox(v_a_5467_);
lean_dec(v_a_5467_);
v___x_5479_ = l_Lean_MessageData_ofConstName(v_name_5470_, v___x_5478_);
v___x_5480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5477_);
lean_ctor_set(v___x_5480_, 1, v___x_5479_);
v___x_5481_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__7);
v___x_5482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5480_);
lean_ctor_set(v___x_5482_, 1, v___x_5481_);
v___x_5483_ = l_Lean_throwError___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getFieldOrigin_spec__1___redArg(v___x_5482_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
v_a_5484_ = lean_ctor_get(v___x_5483_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5486_ = v___x_5483_;
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5483_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5489_; 
if (v_isShared_5487_ == 0)
{
v___x_5489_ = v___x_5486_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_a_5484_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
}
}
else
{
lean_dec(v_a_5467_);
lean_del_object(v___x_5410_);
lean_del_object(v___x_5406_);
v___y_5414_ = v___y_5247_;
v___y_5415_ = v___y_5248_;
v___y_5416_ = v___y_5249_;
v___y_5417_ = v___y_5250_;
goto v___jp_5413_;
}
}
else
{
lean_object* v_a_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5501_; 
lean_del_object(v___x_5410_);
lean_del_object(v___x_5406_);
lean_dec(v_fst_5404_);
lean_dec_ref(v_val_5397_);
lean_dec_ref(v_x_5245_);
lean_dec_ref(v_x_5244_);
lean_dec(v_val_5243_);
lean_dec_ref(v_expectedType_5238_);
v_a_5494_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5496_ = v___x_5466_;
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_a_5494_);
lean_dec(v___x_5466_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5499_; 
if (v_isShared_5497_ == 0)
{
v___x_5499_ = v___x_5496_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5494_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
return v___x_5499_;
}
}
}
}
v___jp_5413_:
{
lean_object* v_numParams_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
v_numParams_5418_ = lean_ctor_get(v_val_5397_, 3);
lean_inc(v_numParams_5418_);
lean_dec_ref(v_val_5397_);
v___x_5419_ = lean_box(0);
v___x_5420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(v___x_5412_, v_fst_5404_, v_x_5245_, v___x_5239_, v_compile_5240_, v_logCompileErrors_5241_, v_isMeta_5242_, v_val_5243_, v_expectedType_5238_, v_numParams_5418_, v___x_5419_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_);
lean_dec_ref(v_x_5245_);
if (lean_obj_tag(v___x_5420_) == 0)
{
size_t v_sz_5421_; size_t v___x_5422_; lean_object* v___x_5423_; 
lean_dec_ref(v___x_5420_);
v_sz_5421_ = lean_array_size(v_fst_5404_);
v___x_5422_ = ((size_t)0ULL);
v___x_5423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__6(v_sz_5421_, v___x_5422_, v_fst_5404_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5432_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5432_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5432_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5428_; lean_object* v___x_5430_; 
v___x_5428_ = l_Lean_mkAppN(v_x_5244_, v_a_5424_);
lean_dec(v_a_5424_);
if (v_isShared_5427_ == 0)
{
lean_ctor_set(v___x_5426_, 0, v___x_5428_);
v___x_5430_ = v___x_5426_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v___x_5428_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
else
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5440_; 
lean_dec_ref(v_x_5244_);
v_a_5433_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5440_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5440_ == 0)
{
v___x_5435_ = v___x_5423_;
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___x_5423_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5438_; 
if (v_isShared_5436_ == 0)
{
v___x_5438_ = v___x_5435_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_a_5433_);
v___x_5438_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
return v___x_5438_;
}
}
}
}
else
{
lean_object* v_a_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5448_; 
lean_dec(v_fst_5404_);
lean_dec_ref(v_x_5244_);
v_a_5441_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5448_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5448_ == 0)
{
v___x_5443_ = v___x_5420_;
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_dec(v___x_5420_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
lean_object* v___x_5446_; 
if (v_isShared_5444_ == 0)
{
v___x_5446_ = v___x_5443_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_a_5441_);
v___x_5446_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
return v___x_5446_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5512_; 
lean_dec_ref(v_val_5397_);
lean_dec_ref(v_x_5245_);
lean_dec_ref(v_x_5244_);
lean_dec(v_val_5243_);
lean_dec_ref(v_expectedType_5238_);
v_a_5505_ = lean_ctor_get(v___x_5401_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5401_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5507_ = v___x_5401_;
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5401_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
if (v_isShared_5508_ == 0)
{
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_a_5505_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
else
{
lean_dec_ref(v_val_5397_);
lean_dec_ref(v_x_5245_);
lean_dec_ref(v_x_5244_);
lean_dec(v_val_5243_);
lean_dec_ref(v_expectedType_5238_);
return v___x_5398_;
}
}
else
{
lean_dec(v_a_5396_);
lean_dec_ref(v_x_5245_);
lean_dec_ref(v_x_5244_);
lean_dec(v_val_5243_);
v___y_5372_ = v___y_5247_;
v___y_5373_ = v___y_5248_;
v___y_5374_ = v___y_5249_;
v___y_5375_ = v___y_5250_;
goto v___jp_5371_;
}
}
else
{
lean_object* v_a_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5520_; 
lean_dec_ref(v_x_5245_);
lean_dec_ref(v_x_5244_);
lean_dec(v_val_5243_);
lean_dec_ref(v_expectedType_5238_);
lean_dec_ref(v_inst_5237_);
v_a_5513_ = lean_ctor_get(v___x_5395_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5395_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5515_ = v___x_5395_;
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_a_5513_);
lean_dec(v___x_5395_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5518_; 
if (v_isShared_5516_ == 0)
{
v___x_5518_ = v___x_5515_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
v___jp_5371_:
{
lean_object* v_options_5376_; uint8_t v_hasTrace_5377_; 
v_options_5376_ = lean_ctor_get(v___y_5374_, 2);
v_hasTrace_5377_ = lean_ctor_get_uint8(v_options_5376_, sizeof(void*)*1);
if (v_hasTrace_5377_ == 0)
{
v___y_5292_ = v___y_5372_;
v___y_5293_ = v___y_5373_;
v___y_5294_ = v___y_5374_;
v_options_5295_ = v_options_5376_;
v___y_5296_ = v___y_5375_;
goto v___jp_5291_;
}
else
{
lean_object* v_inheritedTraceOptions_5378_; lean_object* v___x_5379_; uint8_t v___x_5380_; 
v_inheritedTraceOptions_5378_ = lean_ctor_get(v___y_5374_, 13);
v___x_5379_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_5380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5378_, v_options_5376_, v___x_5379_);
if (v___x_5380_ == 0)
{
v___y_5292_ = v___y_5372_;
v___y_5293_ = v___y_5373_;
v___y_5294_ = v___y_5374_;
v_options_5295_ = v_options_5376_;
v___y_5296_ = v___y_5375_;
goto v___jp_5291_;
}
else
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5381_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___closed__1);
lean_inc_ref(v_inst_5237_);
v___x_5382_ = l_Lean_MessageData_ofExpr(v_inst_5237_);
v___x_5383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5383_, 0, v___x_5381_);
lean_ctor_set(v___x_5383_, 1, v___x_5382_);
v___x_5384_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5370_, v___x_5383_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
if (lean_obj_tag(v___x_5384_) == 0)
{
lean_dec_ref(v___x_5384_);
v___y_5292_ = v___y_5372_;
v___y_5293_ = v___y_5373_;
v___y_5294_ = v___y_5374_;
v_options_5295_ = v_options_5376_;
v___y_5296_ = v___y_5375_;
goto v___jp_5291_;
}
else
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
lean_dec_ref(v_expectedType_5238_);
lean_dec_ref(v_inst_5237_);
v_a_5385_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5384_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5384_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
}
}
}
}
v___jp_5252_:
{
lean_object* v___x_5257_; 
v___x_5257_ = l_Lean_enableRealizationsForConst(v___y_5253_, v___y_5255_, v___y_5256_);
if (lean_obj_tag(v___x_5257_) == 0)
{
lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5264_ == 0)
{
lean_object* v_unused_5265_; 
v_unused_5265_ = lean_ctor_get(v___x_5257_, 0);
lean_dec(v_unused_5265_);
v___x_5259_ = v___x_5257_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_dec(v___x_5257_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v___y_5254_);
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___y_5254_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
else
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5273_; 
lean_dec_ref(v___y_5254_);
v_a_5266_ = lean_ctor_get(v___x_5257_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5268_ = v___x_5257_;
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v___x_5257_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5273_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v___x_5271_; 
if (v_isShared_5269_ == 0)
{
v___x_5271_ = v___x_5268_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
v___x_5271_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
return v___x_5271_;
}
}
}
}
v___jp_5274_:
{
if (v_compile_5240_ == 0)
{
v___y_5253_ = v___y_5275_;
v___y_5254_ = v___y_5276_;
v___y_5255_ = v___y_5277_;
v___y_5256_ = v___y_5278_;
goto v___jp_5252_;
}
else
{
lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5279_ = lean_unsigned_to_nat(1u);
v___x_5280_ = lean_mk_empty_array_with_capacity(v___x_5279_);
lean_inc(v___y_5275_);
v___x_5281_ = lean_array_push(v___x_5280_, v___y_5275_);
v___x_5282_ = l_Lean_compileDecls(v___x_5281_, v_logCompileErrors_5241_, v___y_5277_, v___y_5278_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_dec_ref(v___x_5282_);
v___y_5253_ = v___y_5275_;
v___y_5254_ = v___y_5276_;
v___y_5255_ = v___y_5277_;
v___y_5256_ = v___y_5278_;
goto v___jp_5252_;
}
else
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5290_; 
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5285_ = v___x_5282_;
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___x_5282_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v___x_5288_; 
if (v_isShared_5286_ == 0)
{
v___x_5288_ = v___x_5285_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_a_5283_);
v___x_5288_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
return v___x_5288_;
}
}
}
}
}
v___jp_5291_:
{
lean_object* v___x_5297_; uint8_t v___x_5298_; 
v___x_5297_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5298_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5295_, v___x_5297_);
if (v___x_5298_ == 0)
{
lean_object* v___x_5299_; 
lean_dec_ref(v_expectedType_5238_);
v___x_5299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5299_, 0, v_inst_5237_);
return v___x_5299_;
}
else
{
lean_object* v___x_5300_; 
lean_inc(v___y_5296_);
lean_inc_ref(v___y_5294_);
lean_inc(v___y_5293_);
lean_inc_ref(v___y_5292_);
lean_inc_ref(v_inst_5237_);
v___x_5300_ = lean_infer_type(v_inst_5237_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5296_);
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_object* v_a_5301_; lean_object* v___x_5302_; 
v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
lean_inc(v_a_5301_);
lean_dec_ref(v___x_5300_);
lean_inc_ref(v_expectedType_5238_);
v___x_5302_ = l_Lean_Meta_isExprDefEq(v_expectedType_5238_, v_a_5301_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5296_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5355_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5305_ = v___x_5302_;
v_isShared_5306_ = v_isSharedCheck_5355_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5302_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5355_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
uint8_t v___x_5307_; 
v___x_5307_ = lean_unbox(v_a_5303_);
if (v___x_5307_ == 0)
{
lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v_a_5310_; uint8_t v___x_5311_; uint8_t v___x_5312_; lean_object* v___x_5313_; 
lean_del_object(v___x_5305_);
v___x_5308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__1___closed__1));
v___x_5309_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_5308_, v___y_5296_);
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc_n(v_a_5310_, 2);
lean_dec_ref(v___x_5309_);
v___x_5311_ = lean_unbox(v_a_5303_);
v___x_5312_ = lean_unbox(v_a_5303_);
lean_dec(v_a_5303_);
v___x_5313_ = l_Lean_Meta_mkAuxDefinition(v_a_5310_, v_expectedType_5238_, v_inst_5237_, v___x_5311_, v___x_5312_, v___x_5239_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5296_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; uint8_t v___x_5315_; lean_object* v___x_5316_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_a_5314_);
lean_dec_ref(v___x_5313_);
v___x_5315_ = 3;
lean_inc(v_a_5310_);
v___x_5316_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_5310_, v___x_5315_, v___y_5293_, v___y_5296_);
lean_dec_ref(v___x_5316_);
if (v_isMeta_5242_ == 0)
{
v___y_5275_ = v_a_5310_;
v___y_5276_ = v_a_5314_;
v___y_5277_ = v___y_5294_;
v___y_5278_ = v___y_5296_;
goto v___jp_5274_;
}
else
{
lean_object* v___x_5317_; lean_object* v_env_5318_; lean_object* v_nextMacroScope_5319_; lean_object* v_ngen_5320_; lean_object* v_auxDeclNGen_5321_; lean_object* v_traceState_5322_; lean_object* v_messages_5323_; lean_object* v_infoState_5324_; lean_object* v_snapshotTasks_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5350_; 
v___x_5317_ = lean_st_ref_take(v___y_5296_);
v_env_5318_ = lean_ctor_get(v___x_5317_, 0);
v_nextMacroScope_5319_ = lean_ctor_get(v___x_5317_, 1);
v_ngen_5320_ = lean_ctor_get(v___x_5317_, 2);
v_auxDeclNGen_5321_ = lean_ctor_get(v___x_5317_, 3);
v_traceState_5322_ = lean_ctor_get(v___x_5317_, 4);
v_messages_5323_ = lean_ctor_get(v___x_5317_, 6);
v_infoState_5324_ = lean_ctor_get(v___x_5317_, 7);
v_snapshotTasks_5325_ = lean_ctor_get(v___x_5317_, 8);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5350_ == 0)
{
lean_object* v_unused_5351_; 
v_unused_5351_ = lean_ctor_get(v___x_5317_, 5);
lean_dec(v_unused_5351_);
v___x_5327_ = v___x_5317_;
v_isShared_5328_ = v_isSharedCheck_5350_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_snapshotTasks_5325_);
lean_inc(v_infoState_5324_);
lean_inc(v_messages_5323_);
lean_inc(v_traceState_5322_);
lean_inc(v_auxDeclNGen_5321_);
lean_inc(v_ngen_5320_);
lean_inc(v_nextMacroScope_5319_);
lean_inc(v_env_5318_);
lean_dec(v___x_5317_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5350_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5332_; 
lean_inc(v_a_5310_);
v___x_5329_ = l_Lean_markMeta(v_env_5318_, v_a_5310_);
v___x_5330_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 5, v___x_5330_);
lean_ctor_set(v___x_5327_, 0, v___x_5329_);
v___x_5332_ = v___x_5327_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5329_);
lean_ctor_set(v_reuseFailAlloc_5349_, 1, v_nextMacroScope_5319_);
lean_ctor_set(v_reuseFailAlloc_5349_, 2, v_ngen_5320_);
lean_ctor_set(v_reuseFailAlloc_5349_, 3, v_auxDeclNGen_5321_);
lean_ctor_set(v_reuseFailAlloc_5349_, 4, v_traceState_5322_);
lean_ctor_set(v_reuseFailAlloc_5349_, 5, v___x_5330_);
lean_ctor_set(v_reuseFailAlloc_5349_, 6, v_messages_5323_);
lean_ctor_set(v_reuseFailAlloc_5349_, 7, v_infoState_5324_);
lean_ctor_set(v_reuseFailAlloc_5349_, 8, v_snapshotTasks_5325_);
v___x_5332_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v_mctx_5335_; lean_object* v_zetaDeltaFVarIds_5336_; lean_object* v_postponed_5337_; lean_object* v_diag_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5347_; 
v___x_5333_ = lean_st_ref_set(v___y_5296_, v___x_5332_);
v___x_5334_ = lean_st_ref_take(v___y_5293_);
v_mctx_5335_ = lean_ctor_get(v___x_5334_, 0);
v_zetaDeltaFVarIds_5336_ = lean_ctor_get(v___x_5334_, 2);
v_postponed_5337_ = lean_ctor_get(v___x_5334_, 3);
v_diag_5338_ = lean_ctor_get(v___x_5334_, 4);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; 
v_unused_5348_ = lean_ctor_get(v___x_5334_, 1);
lean_dec(v_unused_5348_);
v___x_5340_ = v___x_5334_;
v_isShared_5341_ = v_isSharedCheck_5347_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_diag_5338_);
lean_inc(v_postponed_5337_);
lean_inc(v_zetaDeltaFVarIds_5336_);
lean_inc(v_mctx_5335_);
lean_dec(v___x_5334_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5347_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5342_; lean_object* v___x_5344_; 
v___x_5342_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_5341_ == 0)
{
lean_ctor_set(v___x_5340_, 1, v___x_5342_);
v___x_5344_ = v___x_5340_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_mctx_5335_);
lean_ctor_set(v_reuseFailAlloc_5346_, 1, v___x_5342_);
lean_ctor_set(v_reuseFailAlloc_5346_, 2, v_zetaDeltaFVarIds_5336_);
lean_ctor_set(v_reuseFailAlloc_5346_, 3, v_postponed_5337_);
lean_ctor_set(v_reuseFailAlloc_5346_, 4, v_diag_5338_);
v___x_5344_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
lean_object* v___x_5345_; 
v___x_5345_ = lean_st_ref_set(v___y_5293_, v___x_5344_);
v___y_5275_ = v_a_5310_;
v___y_5276_ = v_a_5314_;
v___y_5277_ = v___y_5294_;
v___y_5278_ = v___y_5296_;
goto v___jp_5274_;
}
}
}
}
}
}
else
{
lean_dec(v_a_5310_);
return v___x_5313_;
}
}
else
{
lean_object* v___x_5353_; 
lean_dec(v_a_5303_);
lean_dec_ref(v_expectedType_5238_);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 0, v_inst_5237_);
v___x_5353_ = v___x_5305_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_inst_5237_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
}
else
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5363_; 
lean_dec_ref(v_expectedType_5238_);
lean_dec_ref(v_inst_5237_);
v_a_5356_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5358_ = v___x_5302_;
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5302_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
if (v_isShared_5359_ == 0)
{
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5356_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_5238_);
lean_dec_ref(v_inst_5237_);
return v___x_5300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object* v_expectedType_5521_, lean_object* v_inst_5522_, uint8_t v___x_5523_, uint8_t v_compile_5524_, uint8_t v_logCompileErrors_5525_, uint8_t v_isMeta_5526_, lean_object* v_val_5527_, lean_object* v_____r_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_){
_start:
{
lean_object* v___x_5534_; 
lean_inc_ref(v_expectedType_5521_);
v___x_5534_ = l_Lean_Meta_isProp(v_expectedType_5521_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
if (lean_obj_tag(v___x_5534_) == 0)
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5556_; 
v_a_5535_ = lean_ctor_get(v___x_5534_, 0);
v_isSharedCheck_5556_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5556_ == 0)
{
v___x_5537_ = v___x_5534_;
v_isShared_5538_ = v_isSharedCheck_5556_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5534_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5556_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
uint8_t v___x_5539_; 
v___x_5539_ = lean_unbox(v_a_5535_);
lean_dec(v_a_5535_);
if (v___x_5539_ == 0)
{
lean_object* v___x_5540_; 
lean_del_object(v___x_5537_);
lean_inc(v___y_5532_);
lean_inc_ref(v___y_5531_);
lean_inc(v___y_5530_);
lean_inc_ref(v___y_5529_);
lean_inc_ref(v_inst_5522_);
v___x_5540_ = lean_whnf(v_inst_5522_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
if (lean_obj_tag(v___x_5540_) == 0)
{
lean_object* v_a_5541_; lean_object* v_dummy_5542_; lean_object* v_nargs_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v_a_5541_ = lean_ctor_get(v___x_5540_, 0);
lean_inc(v_a_5541_);
lean_dec_ref(v___x_5540_);
v_dummy_5542_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5543_ = l_Lean_Expr_getAppNumArgs(v_a_5541_);
lean_inc(v_nargs_5543_);
v___x_5544_ = lean_mk_array(v_nargs_5543_, v_dummy_5542_);
v___x_5545_ = lean_unsigned_to_nat(1u);
v___x_5546_ = lean_nat_sub(v_nargs_5543_, v___x_5545_);
lean_dec(v_nargs_5543_);
v___x_5547_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16(v_inst_5522_, v_expectedType_5521_, v___x_5523_, v_compile_5524_, v_logCompileErrors_5525_, v_isMeta_5526_, v_val_5527_, v_a_5541_, v___x_5544_, v___x_5546_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
lean_dec(v___x_5546_);
return v___x_5547_;
}
else
{
lean_dec(v_val_5527_);
lean_dec_ref(v_inst_5522_);
lean_dec_ref(v_expectedType_5521_);
return v___x_5540_;
}
}
else
{
lean_object* v_options_5548_; lean_object* v___x_5549_; uint8_t v___x_5550_; 
lean_dec(v_val_5527_);
v_options_5548_ = lean_ctor_get(v___y_5531_, 2);
v___x_5549_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5550_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5548_, v___x_5549_);
if (v___x_5550_ == 0)
{
lean_object* v___x_5552_; 
lean_dec_ref(v_expectedType_5521_);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 0, v_inst_5522_);
v___x_5552_ = v___x_5537_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_inst_5522_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
else
{
lean_object* v___x_5554_; lean_object* v___x_5555_; 
lean_del_object(v___x_5537_);
v___x_5554_ = lean_box(0);
v___x_5555_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5521_, v_inst_5522_, v___x_5523_, v___x_5554_, v___x_5523_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
return v___x_5555_;
}
}
}
}
else
{
lean_object* v_a_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5564_; 
lean_dec(v_val_5527_);
lean_dec_ref(v_inst_5522_);
lean_dec_ref(v_expectedType_5521_);
v_a_5557_ = lean_ctor_get(v___x_5534_, 0);
v_isSharedCheck_5564_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5559_ = v___x_5534_;
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_a_5557_);
lean_dec(v___x_5534_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5562_; 
if (v_isShared_5560_ == 0)
{
v___x_5562_ = v___x_5559_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5557_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object* v_inst_5565_, lean_object* v_expectedType_5566_, uint8_t v_compile_5567_, uint8_t v_logCompileErrors_5568_, uint8_t v_isMeta_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_){
_start:
{
lean_object* v___x_5575_; lean_object* v_options_5576_; uint8_t v_foApprox_5577_; uint8_t v_ctxApprox_5578_; uint8_t v_quasiPatternApprox_5579_; uint8_t v_constApprox_5580_; uint8_t v_isDefEqStuckEx_5581_; uint8_t v_unificationHints_5582_; uint8_t v_proofIrrelevance_5583_; uint8_t v_assignSyntheticOpaque_5584_; uint8_t v_offsetCnstrs_5585_; uint8_t v_etaStruct_5586_; uint8_t v_univApprox_5587_; uint8_t v_iota_5588_; uint8_t v_beta_5589_; uint8_t v_proj_5590_; uint8_t v_zeta_5591_; uint8_t v_zetaDelta_5592_; uint8_t v_zetaUnused_5593_; uint8_t v_zetaHave_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5845_; 
v___x_5575_ = l_Lean_Meta_Context_config(v_a_5570_);
v_options_5576_ = lean_ctor_get(v_a_5572_, 2);
v_foApprox_5577_ = lean_ctor_get_uint8(v___x_5575_, 0);
v_ctxApprox_5578_ = lean_ctor_get_uint8(v___x_5575_, 1);
v_quasiPatternApprox_5579_ = lean_ctor_get_uint8(v___x_5575_, 2);
v_constApprox_5580_ = lean_ctor_get_uint8(v___x_5575_, 3);
v_isDefEqStuckEx_5581_ = lean_ctor_get_uint8(v___x_5575_, 4);
v_unificationHints_5582_ = lean_ctor_get_uint8(v___x_5575_, 5);
v_proofIrrelevance_5583_ = lean_ctor_get_uint8(v___x_5575_, 6);
v_assignSyntheticOpaque_5584_ = lean_ctor_get_uint8(v___x_5575_, 7);
v_offsetCnstrs_5585_ = lean_ctor_get_uint8(v___x_5575_, 8);
v_etaStruct_5586_ = lean_ctor_get_uint8(v___x_5575_, 10);
v_univApprox_5587_ = lean_ctor_get_uint8(v___x_5575_, 11);
v_iota_5588_ = lean_ctor_get_uint8(v___x_5575_, 12);
v_beta_5589_ = lean_ctor_get_uint8(v___x_5575_, 13);
v_proj_5590_ = lean_ctor_get_uint8(v___x_5575_, 14);
v_zeta_5591_ = lean_ctor_get_uint8(v___x_5575_, 15);
v_zetaDelta_5592_ = lean_ctor_get_uint8(v___x_5575_, 16);
v_zetaUnused_5593_ = lean_ctor_get_uint8(v___x_5575_, 17);
v_zetaHave_5594_ = lean_ctor_get_uint8(v___x_5575_, 18);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5845_ == 0)
{
v___x_5596_ = v___x_5575_;
v_isShared_5597_ = v_isSharedCheck_5845_;
goto v_resetjp_5595_;
}
else
{
lean_dec(v___x_5575_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5845_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
uint8_t v_trackZetaDelta_5598_; lean_object* v_zetaDeltaSet_5599_; lean_object* v_lctx_5600_; lean_object* v_localInstances_5601_; lean_object* v_defEqCtx_x3f_5602_; lean_object* v_synthPendingDepth_5603_; lean_object* v_canUnfold_x3f_5604_; uint8_t v_univApprox_5605_; uint8_t v_inTypeClassResolution_5606_; uint8_t v_cacheInferType_5607_; lean_object* v_inheritedTraceOptions_5608_; uint8_t v_hasTrace_5609_; uint8_t v___x_5610_; lean_object* v_config_5612_; 
v_trackZetaDelta_5598_ = lean_ctor_get_uint8(v_a_5570_, sizeof(void*)*7);
v_zetaDeltaSet_5599_ = lean_ctor_get(v_a_5570_, 1);
v_lctx_5600_ = lean_ctor_get(v_a_5570_, 2);
v_localInstances_5601_ = lean_ctor_get(v_a_5570_, 3);
v_defEqCtx_x3f_5602_ = lean_ctor_get(v_a_5570_, 4);
v_synthPendingDepth_5603_ = lean_ctor_get(v_a_5570_, 5);
v_canUnfold_x3f_5604_ = lean_ctor_get(v_a_5570_, 6);
v_univApprox_5605_ = lean_ctor_get_uint8(v_a_5570_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5606_ = lean_ctor_get_uint8(v_a_5570_, sizeof(void*)*7 + 2);
v_cacheInferType_5607_ = lean_ctor_get_uint8(v_a_5570_, sizeof(void*)*7 + 3);
v_inheritedTraceOptions_5608_ = lean_ctor_get(v_a_5572_, 13);
v_hasTrace_5609_ = lean_ctor_get_uint8(v_options_5576_, sizeof(void*)*1);
v___x_5610_ = 3;
if (v_isShared_5597_ == 0)
{
v_config_5612_ = v___x_5596_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 0, v_foApprox_5577_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 1, v_ctxApprox_5578_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 2, v_quasiPatternApprox_5579_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 3, v_constApprox_5580_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 4, v_isDefEqStuckEx_5581_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 5, v_unificationHints_5582_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 6, v_proofIrrelevance_5583_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 7, v_assignSyntheticOpaque_5584_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 8, v_offsetCnstrs_5585_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 10, v_etaStruct_5586_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 11, v_univApprox_5587_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 12, v_iota_5588_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 13, v_beta_5589_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 14, v_proj_5590_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 15, v_zeta_5591_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 16, v_zetaDelta_5592_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 17, v_zetaUnused_5593_);
lean_ctor_set_uint8(v_reuseFailAlloc_5844_, 18, v_zetaHave_5594_);
v_config_5612_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
uint64_t v___x_5613_; uint64_t v___x_5614_; uint64_t v___x_5615_; uint64_t v___x_5616_; uint64_t v___x_5617_; uint64_t v_key_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; 
lean_ctor_set_uint8(v_config_5612_, 9, v___x_5610_);
v___x_5613_ = l_Lean_Meta_Context_configKey(v_a_5570_);
v___x_5614_ = 2ULL;
v___x_5615_ = lean_uint64_shift_right(v___x_5613_, v___x_5614_);
v___x_5616_ = lean_uint64_shift_left(v___x_5615_, v___x_5614_);
v___x_5617_ = lean_uint64_once(&l_Lean_Meta_wrapInstance___closed__0, &l_Lean_Meta_wrapInstance___closed__0_once, _init_l_Lean_Meta_wrapInstance___closed__0);
v_key_5618_ = lean_uint64_lor(v___x_5616_, v___x_5617_);
v___x_5619_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5619_, 0, v_config_5612_);
lean_ctor_set_uint64(v___x_5619_, sizeof(void*)*1, v_key_5618_);
lean_inc(v_canUnfold_x3f_5604_);
lean_inc(v_synthPendingDepth_5603_);
lean_inc(v_defEqCtx_x3f_5602_);
lean_inc_ref(v_localInstances_5601_);
lean_inc_ref(v_lctx_5600_);
lean_inc(v_zetaDeltaSet_5599_);
v___x_5620_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5620_, 0, v___x_5619_);
lean_ctor_set(v___x_5620_, 1, v_zetaDeltaSet_5599_);
lean_ctor_set(v___x_5620_, 2, v_lctx_5600_);
lean_ctor_set(v___x_5620_, 3, v_localInstances_5601_);
lean_ctor_set(v___x_5620_, 4, v_defEqCtx_x3f_5602_);
lean_ctor_set(v___x_5620_, 5, v_synthPendingDepth_5603_);
lean_ctor_set(v___x_5620_, 6, v_canUnfold_x3f_5604_);
lean_ctor_set_uint8(v___x_5620_, sizeof(void*)*7, v_trackZetaDelta_5598_);
lean_ctor_set_uint8(v___x_5620_, sizeof(void*)*7 + 1, v_univApprox_5605_);
lean_ctor_set_uint8(v___x_5620_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5606_);
lean_ctor_set_uint8(v___x_5620_, sizeof(void*)*7 + 3, v_cacheInferType_5607_);
if (v_hasTrace_5609_ == 0)
{
lean_object* v___x_5621_; 
lean_inc_ref(v_expectedType_5566_);
v___x_5621_ = l_Lean_Meta_isClass_x3f(v_expectedType_5566_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5621_) == 0)
{
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5660_; 
v_a_5622_ = lean_ctor_get(v___x_5621_, 0);
v_isSharedCheck_5660_ = !lean_is_exclusive(v___x_5621_);
if (v_isSharedCheck_5660_ == 0)
{
v___x_5624_ = v___x_5621_;
v_isShared_5625_ = v_isSharedCheck_5660_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5621_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5660_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
if (lean_obj_tag(v_a_5622_) == 1)
{
lean_object* v_val_5626_; lean_object* v___x_5627_; 
lean_del_object(v___x_5624_);
v_val_5626_ = lean_ctor_get(v_a_5622_, 0);
lean_inc(v_val_5626_);
lean_dec_ref(v_a_5622_);
lean_inc_ref(v_expectedType_5566_);
v___x_5627_ = l_Lean_Meta_isProp(v_expectedType_5566_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5648_; 
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5648_ == 0)
{
v___x_5630_ = v___x_5627_;
v_isShared_5631_ = v_isSharedCheck_5648_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_a_5628_);
lean_dec(v___x_5627_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5648_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
uint8_t v___x_5632_; 
v___x_5632_ = lean_unbox(v_a_5628_);
lean_dec(v_a_5628_);
if (v___x_5632_ == 0)
{
lean_object* v___x_5633_; 
lean_del_object(v___x_5630_);
lean_inc(v_a_5573_);
lean_inc_ref(v_a_5572_);
lean_inc(v_a_5571_);
lean_inc_ref(v___x_5620_);
lean_inc_ref(v_inst_5565_);
v___x_5633_ = lean_whnf(v_inst_5565_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5633_) == 0)
{
lean_object* v_a_5634_; lean_object* v_dummy_5635_; lean_object* v_nargs_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; 
v_a_5634_ = lean_ctor_get(v___x_5633_, 0);
lean_inc(v_a_5634_);
lean_dec_ref(v___x_5633_);
v_dummy_5635_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5636_ = l_Lean_Expr_getAppNumArgs(v_a_5634_);
lean_inc(v_nargs_5636_);
v___x_5637_ = lean_mk_array(v_nargs_5636_, v_dummy_5635_);
v___x_5638_ = lean_unsigned_to_nat(1u);
v___x_5639_ = lean_nat_sub(v_nargs_5636_, v___x_5638_);
lean_dec(v_nargs_5636_);
v___x_5640_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10(v_inst_5565_, v_expectedType_5566_, v_hasTrace_5609_, v_compile_5567_, v_logCompileErrors_5568_, v_isMeta_5569_, v_val_5626_, v_a_5634_, v___x_5637_, v___x_5639_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
lean_dec_ref(v___x_5620_);
lean_dec(v___x_5639_);
return v___x_5640_;
}
else
{
lean_dec(v_val_5626_);
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
return v___x_5633_;
}
}
else
{
lean_object* v___x_5641_; uint8_t v___x_5642_; 
lean_dec(v_val_5626_);
v___x_5641_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5642_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5576_, v___x_5641_);
if (v___x_5642_ == 0)
{
lean_object* v___x_5644_; 
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 0, v_inst_5565_);
v___x_5644_ = v___x_5630_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5645_; 
v_reuseFailAlloc_5645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_inst_5565_);
v___x_5644_ = v_reuseFailAlloc_5645_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
return v___x_5644_;
}
}
else
{
lean_object* v___x_5646_; lean_object* v___x_5647_; 
lean_del_object(v___x_5630_);
v___x_5646_ = lean_box(0);
v___x_5647_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5566_, v_inst_5565_, v___x_5642_, v___x_5646_, v___x_5642_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
lean_dec_ref(v___x_5620_);
return v___x_5647_;
}
}
}
}
else
{
lean_object* v_a_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5656_; 
lean_dec(v_val_5626_);
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5649_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5651_ = v___x_5627_;
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_a_5649_);
lean_dec(v___x_5627_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
lean_object* v___x_5654_; 
if (v_isShared_5652_ == 0)
{
v___x_5654_ = v___x_5651_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
return v___x_5654_;
}
}
}
}
else
{
lean_object* v___x_5658_; 
lean_dec(v_a_5622_);
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
if (v_isShared_5625_ == 0)
{
lean_ctor_set(v___x_5624_, 0, v_inst_5565_);
v___x_5658_ = v___x_5624_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_inst_5565_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
return v___x_5658_;
}
}
}
}
else
{
lean_object* v_a_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5668_; 
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5661_ = lean_ctor_get(v___x_5621_, 0);
v_isSharedCheck_5668_ = !lean_is_exclusive(v___x_5621_);
if (v_isSharedCheck_5668_ == 0)
{
v___x_5663_ = v___x_5621_;
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_a_5661_);
lean_dec(v___x_5621_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5668_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
lean_object* v___x_5666_; 
if (v_isShared_5664_ == 0)
{
v___x_5666_ = v___x_5663_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
else
{
lean_object* v___f_5669_; lean_object* v_cls_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; uint8_t v___x_5673_; lean_object* v___y_5675_; lean_object* v___y_5676_; lean_object* v_a_5677_; lean_object* v___y_5687_; lean_object* v___y_5688_; lean_object* v_a_5689_; lean_object* v___y_5692_; lean_object* v___y_5693_; lean_object* v_a_5694_; lean_object* v___y_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5703_; lean_object* v___y_5704_; lean_object* v_a_5705_; lean_object* v___y_5718_; lean_object* v___y_5719_; lean_object* v_a_5720_; lean_object* v___y_5723_; lean_object* v___y_5724_; lean_object* v_a_5725_; lean_object* v___y_5728_; lean_object* v___y_5729_; lean_object* v___y_5730_; 
lean_inc_ref(v_expectedType_5566_);
v___f_5669_ = lean_alloc_closure((void*)(l_Lean_Meta_wrapInstance___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5669_, 0, v_expectedType_5566_);
v_cls_5670_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5671_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__0___closed__1));
v___x_5672_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__3);
v___x_5673_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5608_, v_options_5576_, v___x_5672_);
if (v___x_5673_ == 0)
{
lean_object* v___x_5776_; uint8_t v___x_5777_; 
v___x_5776_ = l_Lean_trace_profiler;
v___x_5777_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5576_, v___x_5776_);
if (v___x_5777_ == 0)
{
lean_object* v___x_5778_; 
lean_dec_ref(v___f_5669_);
lean_inc_ref(v_expectedType_5566_);
v___x_5778_ = l_Lean_Meta_isClass_x3f(v_expectedType_5566_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5778_) == 0)
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5835_; 
v_a_5779_ = lean_ctor_get(v___x_5778_, 0);
v_isSharedCheck_5835_ = !lean_is_exclusive(v___x_5778_);
if (v_isSharedCheck_5835_ == 0)
{
v___x_5781_ = v___x_5778_;
v_isShared_5782_ = v_isSharedCheck_5835_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5778_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5835_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
if (lean_obj_tag(v_a_5779_) == 1)
{
lean_object* v_val_5783_; lean_object* v___y_5785_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___y_5788_; 
lean_del_object(v___x_5781_);
v_val_5783_ = lean_ctor_get(v_a_5779_, 0);
lean_inc(v_val_5783_);
lean_dec_ref(v_a_5779_);
if (v___x_5673_ == 0)
{
v___y_5785_ = v___x_5620_;
v___y_5786_ = v_a_5571_;
v___y_5787_ = v_a_5572_;
v___y_5788_ = v_a_5573_;
goto v___jp_5784_;
}
else
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5820_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
lean_inc(v_val_5783_);
v___x_5821_ = l_Lean_MessageData_ofName(v_val_5783_);
v___x_5822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5822_, 0, v___x_5820_);
lean_ctor_set(v___x_5822_, 1, v___x_5821_);
v___x_5823_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5670_, v___x_5822_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_dec_ref(v___x_5823_);
v___y_5785_ = v___x_5620_;
v___y_5786_ = v_a_5571_;
v___y_5787_ = v_a_5572_;
v___y_5788_ = v_a_5573_;
goto v___jp_5784_;
}
else
{
lean_object* v_a_5824_; lean_object* v___x_5826_; uint8_t v_isShared_5827_; uint8_t v_isSharedCheck_5831_; 
lean_dec(v_val_5783_);
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5831_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5831_ == 0)
{
v___x_5826_ = v___x_5823_;
v_isShared_5827_ = v_isSharedCheck_5831_;
goto v_resetjp_5825_;
}
else
{
lean_inc(v_a_5824_);
lean_dec(v___x_5823_);
v___x_5826_ = lean_box(0);
v_isShared_5827_ = v_isSharedCheck_5831_;
goto v_resetjp_5825_;
}
v_resetjp_5825_:
{
lean_object* v___x_5829_; 
if (v_isShared_5827_ == 0)
{
v___x_5829_ = v___x_5826_;
goto v_reusejp_5828_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v_a_5824_);
v___x_5829_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5828_;
}
v_reusejp_5828_:
{
return v___x_5829_;
}
}
}
}
v___jp_5784_:
{
lean_object* v___x_5789_; 
lean_inc_ref(v_expectedType_5566_);
v___x_5789_ = l_Lean_Meta_isProp(v_expectedType_5566_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5789_) == 0)
{
lean_object* v_a_5790_; lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5811_; 
v_a_5790_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5811_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5811_ == 0)
{
v___x_5792_ = v___x_5789_;
v_isShared_5793_ = v_isSharedCheck_5811_;
goto v_resetjp_5791_;
}
else
{
lean_inc(v_a_5790_);
lean_dec(v___x_5789_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5811_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
uint8_t v___x_5794_; 
v___x_5794_ = lean_unbox(v_a_5790_);
lean_dec(v_a_5790_);
if (v___x_5794_ == 0)
{
lean_object* v___x_5795_; 
lean_del_object(v___x_5792_);
lean_inc(v___y_5788_);
lean_inc_ref(v___y_5787_);
lean_inc(v___y_5786_);
lean_inc_ref(v___y_5785_);
lean_inc_ref(v_inst_5565_);
v___x_5795_ = lean_whnf(v_inst_5565_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; lean_object* v_dummy_5797_; lean_object* v_nargs_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
lean_inc(v_a_5796_);
lean_dec_ref(v___x_5795_);
v_dummy_5797_ = lean_obj_once(&l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0, &l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0_once, _init_l_List_foldlM___at___00__private_Lean_Meta_WrapInstance_0__Lean_Meta_getParentStructType_x3f_spec__1___closed__0);
v_nargs_5798_ = l_Lean_Expr_getAppNumArgs(v_a_5796_);
lean_inc(v_nargs_5798_);
v___x_5799_ = lean_mk_array(v_nargs_5798_, v_dummy_5797_);
v___x_5800_ = lean_unsigned_to_nat(1u);
v___x_5801_ = lean_nat_sub(v_nargs_5798_, v___x_5800_);
lean_dec(v_nargs_5798_);
v___x_5802_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_inst_5565_, v_expectedType_5566_, v___x_5777_, v_hasTrace_5609_, v_compile_5567_, v_logCompileErrors_5568_, v_isMeta_5569_, v_val_5783_, v_a_5796_, v___x_5799_, v___x_5801_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
lean_dec_ref(v___y_5785_);
lean_dec(v___x_5801_);
return v___x_5802_;
}
else
{
lean_dec_ref(v___y_5785_);
lean_dec(v_val_5783_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
return v___x_5795_;
}
}
else
{
lean_object* v_options_5803_; lean_object* v___x_5804_; uint8_t v___x_5805_; 
lean_dec(v_val_5783_);
v_options_5803_ = lean_ctor_get(v___y_5787_, 2);
v___x_5804_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5805_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5803_, v___x_5804_);
if (v___x_5805_ == 0)
{
lean_object* v___x_5807_; 
lean_dec_ref(v___y_5785_);
lean_dec_ref(v_expectedType_5566_);
if (v_isShared_5793_ == 0)
{
lean_ctor_set(v___x_5792_, 0, v_inst_5565_);
v___x_5807_ = v___x_5792_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5808_; 
v_reuseFailAlloc_5808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5808_, 0, v_inst_5565_);
v___x_5807_ = v_reuseFailAlloc_5808_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
return v___x_5807_;
}
}
else
{
lean_object* v___x_5809_; lean_object* v___x_5810_; 
lean_del_object(v___x_5792_);
v___x_5809_ = lean_box(0);
v___x_5810_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5566_, v_inst_5565_, v_hasTrace_5609_, v___x_5809_, v_hasTrace_5609_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
lean_dec_ref(v___y_5785_);
return v___x_5810_;
}
}
}
}
else
{
lean_object* v_a_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5819_; 
lean_dec_ref(v___y_5785_);
lean_dec(v_val_5783_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5812_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5819_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5819_ == 0)
{
v___x_5814_ = v___x_5789_;
v_isShared_5815_ = v_isSharedCheck_5819_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_a_5812_);
lean_dec(v___x_5789_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5819_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v___x_5817_; 
if (v_isShared_5815_ == 0)
{
v___x_5817_ = v___x_5814_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_a_5812_);
v___x_5817_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
return v___x_5817_;
}
}
}
}
}
else
{
lean_object* v___x_5833_; 
lean_dec(v_a_5779_);
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
if (v_isShared_5782_ == 0)
{
lean_ctor_set(v___x_5781_, 0, v_inst_5565_);
v___x_5833_ = v___x_5781_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_inst_5565_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
}
}
else
{
lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5843_; 
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5836_ = lean_ctor_get(v___x_5778_, 0);
v_isSharedCheck_5843_ = !lean_is_exclusive(v___x_5778_);
if (v_isSharedCheck_5843_ == 0)
{
v___x_5838_ = v___x_5778_;
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5778_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5839_ == 0)
{
v___x_5841_ = v___x_5838_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_a_5836_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
}
else
{
goto v___jp_5733_;
}
}
else
{
goto v___jp_5733_;
}
v___jp_5674_:
{
lean_object* v___x_5678_; double v___x_5679_; double v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; 
v___x_5678_ = lean_io_get_num_heartbeats();
v___x_5679_ = lean_float_of_nat(v___y_5675_);
v___x_5680_ = lean_float_of_nat(v___x_5678_);
v___x_5681_ = lean_box_float(v___x_5679_);
v___x_5682_ = lean_box_float(v___x_5680_);
v___x_5683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5681_);
lean_ctor_set(v___x_5683_, 1, v___x_5682_);
v___x_5684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5684_, 0, v_a_5677_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(v_cls_5670_, v_hasTrace_5609_, v___x_5671_, v_options_5576_, v___x_5673_, v___y_5676_, v___f_5669_, v___x_5684_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
lean_dec_ref(v___x_5620_);
return v___x_5685_;
}
v___jp_5686_:
{
lean_object* v___x_5690_; 
v___x_5690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5690_, 0, v_a_5689_);
v___y_5675_ = v___y_5687_;
v___y_5676_ = v___y_5688_;
v_a_5677_ = v___x_5690_;
goto v___jp_5674_;
}
v___jp_5691_:
{
lean_object* v___x_5695_; 
v___x_5695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5695_, 0, v_a_5694_);
v___y_5675_ = v___y_5692_;
v___y_5676_ = v___y_5693_;
v_a_5677_ = v___x_5695_;
goto v___jp_5674_;
}
v___jp_5696_:
{
if (lean_obj_tag(v___y_5699_) == 0)
{
lean_object* v_a_5700_; 
v_a_5700_ = lean_ctor_get(v___y_5699_, 0);
lean_inc(v_a_5700_);
lean_dec_ref(v___y_5699_);
v___y_5687_ = v___y_5697_;
v___y_5688_ = v___y_5698_;
v_a_5689_ = v_a_5700_;
goto v___jp_5686_;
}
else
{
lean_object* v_a_5701_; 
v_a_5701_ = lean_ctor_get(v___y_5699_, 0);
lean_inc(v_a_5701_);
lean_dec_ref(v___y_5699_);
v___y_5692_ = v___y_5697_;
v___y_5693_ = v___y_5698_;
v_a_5694_ = v_a_5701_;
goto v___jp_5691_;
}
}
v___jp_5702_:
{
lean_object* v___x_5706_; double v___x_5707_; double v___x_5708_; double v___x_5709_; double v___x_5710_; double v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v___x_5706_ = lean_io_mono_nanos_now();
v___x_5707_ = lean_float_of_nat(v___y_5703_);
v___x_5708_ = lean_float_once(&l_Lean_Meta_wrapInstance___closed__1, &l_Lean_Meta_wrapInstance___closed__1_once, _init_l_Lean_Meta_wrapInstance___closed__1);
v___x_5709_ = lean_float_div(v___x_5707_, v___x_5708_);
v___x_5710_ = lean_float_of_nat(v___x_5706_);
v___x_5711_ = lean_float_div(v___x_5710_, v___x_5708_);
v___x_5712_ = lean_box_float(v___x_5709_);
v___x_5713_ = lean_box_float(v___x_5711_);
v___x_5714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5712_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5715_, 0, v_a_5705_);
lean_ctor_set(v___x_5715_, 1, v___x_5714_);
v___x_5716_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12(v_cls_5670_, v_hasTrace_5609_, v___x_5671_, v_options_5576_, v___x_5673_, v___y_5704_, v___f_5669_, v___x_5715_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
lean_dec_ref(v___x_5620_);
return v___x_5716_;
}
v___jp_5717_:
{
lean_object* v___x_5721_; 
v___x_5721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5721_, 0, v_a_5720_);
v___y_5703_ = v___y_5718_;
v___y_5704_ = v___y_5719_;
v_a_5705_ = v___x_5721_;
goto v___jp_5702_;
}
v___jp_5722_:
{
lean_object* v___x_5726_; 
v___x_5726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5726_, 0, v_a_5725_);
v___y_5703_ = v___y_5723_;
v___y_5704_ = v___y_5724_;
v_a_5705_ = v___x_5726_;
goto v___jp_5702_;
}
v___jp_5727_:
{
if (lean_obj_tag(v___y_5730_) == 0)
{
lean_object* v_a_5731_; 
v_a_5731_ = lean_ctor_get(v___y_5730_, 0);
lean_inc(v_a_5731_);
lean_dec_ref(v___y_5730_);
v___y_5723_ = v___y_5728_;
v___y_5724_ = v___y_5729_;
v_a_5725_ = v_a_5731_;
goto v___jp_5722_;
}
else
{
lean_object* v_a_5732_; 
v_a_5732_ = lean_ctor_get(v___y_5730_, 0);
lean_inc(v_a_5732_);
lean_dec_ref(v___y_5730_);
v___y_5718_ = v___y_5728_;
v___y_5719_ = v___y_5729_;
v_a_5720_ = v_a_5732_;
goto v___jp_5717_;
}
}
v___jp_5733_:
{
lean_object* v___x_5734_; 
v___x_5734_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__11___redArg(v_a_5573_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v_a_5735_; lean_object* v___x_5736_; uint8_t v___x_5737_; 
v_a_5735_ = lean_ctor_get(v___x_5734_, 0);
lean_inc(v_a_5735_);
lean_dec_ref(v___x_5734_);
v___x_5736_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5737_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5576_, v___x_5736_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5738_; lean_object* v___x_5739_; 
v___x_5738_ = lean_io_mono_nanos_now();
lean_inc_ref(v_expectedType_5566_);
v___x_5739_ = l_Lean_Meta_isClass_x3f(v_expectedType_5566_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5739_) == 0)
{
lean_object* v_a_5740_; 
v_a_5740_ = lean_ctor_get(v___x_5739_, 0);
lean_inc(v_a_5740_);
lean_dec_ref(v___x_5739_);
if (lean_obj_tag(v_a_5740_) == 1)
{
if (v___x_5673_ == 0)
{
lean_object* v_val_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; 
v_val_5741_ = lean_ctor_get(v_a_5740_, 0);
lean_inc(v_val_5741_);
lean_dec_ref(v_a_5740_);
v___x_5742_ = lean_box(0);
v___x_5743_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5566_, v_inst_5565_, v___x_5737_, v_hasTrace_5609_, v_compile_5567_, v_logCompileErrors_5568_, v_isMeta_5569_, v_val_5741_, v___x_5742_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
v___y_5728_ = v___x_5738_;
v___y_5729_ = v_a_5735_;
v___y_5730_ = v___x_5743_;
goto v___jp_5727_;
}
else
{
lean_object* v_val_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; 
v_val_5744_ = lean_ctor_get(v_a_5740_, 0);
lean_inc_n(v_val_5744_, 2);
lean_dec_ref(v_a_5740_);
v___x_5745_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5746_ = l_Lean_MessageData_ofName(v_val_5744_);
v___x_5747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5747_, 0, v___x_5745_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5670_, v___x_5747_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5748_) == 0)
{
lean_object* v_a_5749_; lean_object* v___x_5750_; 
v_a_5749_ = lean_ctor_get(v___x_5748_, 0);
lean_inc(v_a_5749_);
lean_dec_ref(v___x_5748_);
v___x_5750_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5566_, v_inst_5565_, v___x_5737_, v_hasTrace_5609_, v_compile_5567_, v_logCompileErrors_5568_, v_isMeta_5569_, v_val_5744_, v_a_5749_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
v___y_5728_ = v___x_5738_;
v___y_5729_ = v_a_5735_;
v___y_5730_ = v___x_5750_;
goto v___jp_5727_;
}
else
{
lean_object* v_a_5751_; 
lean_dec(v_val_5744_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5751_ = lean_ctor_get(v___x_5748_, 0);
lean_inc(v_a_5751_);
lean_dec_ref(v___x_5748_);
v___y_5718_ = v___x_5738_;
v___y_5719_ = v_a_5735_;
v_a_5720_ = v_a_5751_;
goto v___jp_5717_;
}
}
}
else
{
lean_dec(v_a_5740_);
lean_dec_ref(v_expectedType_5566_);
v___y_5723_ = v___x_5738_;
v___y_5724_ = v_a_5735_;
v_a_5725_ = v_inst_5565_;
goto v___jp_5722_;
}
}
else
{
lean_object* v_a_5752_; 
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5752_ = lean_ctor_get(v___x_5739_, 0);
lean_inc(v_a_5752_);
lean_dec_ref(v___x_5739_);
v___y_5718_ = v___x_5738_;
v___y_5719_ = v_a_5735_;
v_a_5720_ = v_a_5752_;
goto v___jp_5717_;
}
}
else
{
lean_object* v___x_5753_; lean_object* v___x_5754_; 
v___x_5753_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_expectedType_5566_);
v___x_5754_ = l_Lean_Meta_isClass_x3f(v_expectedType_5566_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5754_) == 0)
{
lean_object* v_a_5755_; 
v_a_5755_ = lean_ctor_get(v___x_5754_, 0);
lean_inc(v_a_5755_);
lean_dec_ref(v___x_5754_);
if (lean_obj_tag(v_a_5755_) == 1)
{
if (v___x_5673_ == 0)
{
lean_object* v_val_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; 
v_val_5756_ = lean_ctor_get(v_a_5755_, 0);
lean_inc(v_val_5756_);
lean_dec_ref(v_a_5755_);
v___x_5757_ = lean_box(0);
v___x_5758_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5566_, v_inst_5565_, v___x_5737_, v_compile_5567_, v_logCompileErrors_5568_, v_isMeta_5569_, v_val_5756_, v___x_5757_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
v___y_5697_ = v___x_5753_;
v___y_5698_ = v_a_5735_;
v___y_5699_ = v___x_5758_;
goto v___jp_5696_;
}
else
{
lean_object* v_val_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; 
v_val_5759_ = lean_ctor_get(v_a_5755_, 0);
lean_inc_n(v_val_5759_, 2);
lean_dec_ref(v_a_5755_);
v___x_5760_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5761_ = l_Lean_MessageData_ofName(v_val_5759_);
v___x_5762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5762_, 0, v___x_5760_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___x_5763_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5670_, v___x_5762_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
if (lean_obj_tag(v___x_5763_) == 0)
{
lean_object* v_a_5764_; lean_object* v___x_5765_; 
v_a_5764_ = lean_ctor_get(v___x_5763_, 0);
lean_inc(v_a_5764_);
lean_dec_ref(v___x_5763_);
v___x_5765_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5566_, v_inst_5565_, v___x_5737_, v_compile_5567_, v_logCompileErrors_5568_, v_isMeta_5569_, v_val_5759_, v_a_5764_, v___x_5620_, v_a_5571_, v_a_5572_, v_a_5573_);
v___y_5697_ = v___x_5753_;
v___y_5698_ = v_a_5735_;
v___y_5699_ = v___x_5765_;
goto v___jp_5696_;
}
else
{
lean_object* v_a_5766_; 
lean_dec(v_val_5759_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5766_ = lean_ctor_get(v___x_5763_, 0);
lean_inc(v_a_5766_);
lean_dec_ref(v___x_5763_);
v___y_5692_ = v___x_5753_;
v___y_5693_ = v_a_5735_;
v_a_5694_ = v_a_5766_;
goto v___jp_5691_;
}
}
}
else
{
lean_dec(v_a_5755_);
lean_dec_ref(v_expectedType_5566_);
v___y_5687_ = v___x_5753_;
v___y_5688_ = v_a_5735_;
v_a_5689_ = v_inst_5565_;
goto v___jp_5686_;
}
}
else
{
lean_object* v_a_5767_; 
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5767_ = lean_ctor_get(v___x_5754_, 0);
lean_inc(v_a_5767_);
lean_dec_ref(v___x_5754_);
v___y_5692_ = v___x_5753_;
v___y_5693_ = v_a_5735_;
v_a_5694_ = v_a_5767_;
goto v___jp_5691_;
}
}
}
else
{
lean_object* v_a_5768_; lean_object* v___x_5770_; uint8_t v_isShared_5771_; uint8_t v_isSharedCheck_5775_; 
lean_dec_ref(v___f_5669_);
lean_dec_ref(v___x_5620_);
lean_dec_ref(v_expectedType_5566_);
lean_dec_ref(v_inst_5565_);
v_a_5768_ = lean_ctor_get(v___x_5734_, 0);
v_isSharedCheck_5775_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5775_ == 0)
{
v___x_5770_ = v___x_5734_;
v_isShared_5771_ = v_isSharedCheck_5775_;
goto v_resetjp_5769_;
}
else
{
lean_inc(v_a_5768_);
lean_dec(v___x_5734_);
v___x_5770_ = lean_box(0);
v_isShared_5771_ = v_isSharedCheck_5775_;
goto v_resetjp_5769_;
}
v_resetjp_5769_:
{
lean_object* v___x_5773_; 
if (v_isShared_5771_ == 0)
{
v___x_5773_ = v___x_5770_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_a_5768_);
v___x_5773_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
return v___x_5773_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(lean_object* v___x_5846_, lean_object* v_a_5847_, uint8_t v_compile_5848_, uint8_t v_logCompileErrors_5849_, uint8_t v_isMeta_5850_, lean_object* v___x_5851_, lean_object* v___x_5852_, lean_object* v_____r_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_){
_start:
{
lean_object* v___x_5859_; 
v___x_5859_ = l_Lean_Meta_wrapInstance(v___x_5846_, v_a_5847_, v_compile_5848_, v_logCompileErrors_5849_, v_isMeta_5850_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_);
if (lean_obj_tag(v___x_5859_) == 0)
{
lean_object* v_a_5860_; lean_object* v___x_5861_; 
v_a_5860_ = lean_ctor_get(v___x_5859_, 0);
lean_inc(v_a_5860_);
lean_dec_ref(v___x_5859_);
v___x_5861_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_5851_, v_a_5860_, v___y_5855_);
if (lean_obj_tag(v___x_5861_) == 0)
{
lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5869_; 
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5861_);
if (v_isSharedCheck_5869_ == 0)
{
lean_object* v_unused_5870_; 
v_unused_5870_ = lean_ctor_get(v___x_5861_, 0);
lean_dec(v_unused_5870_);
v___x_5863_ = v___x_5861_;
v_isShared_5864_ = v_isSharedCheck_5869_;
goto v_resetjp_5862_;
}
else
{
lean_dec(v___x_5861_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5869_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5865_; lean_object* v___x_5867_; 
v___x_5865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5852_);
if (v_isShared_5864_ == 0)
{
lean_ctor_set(v___x_5863_, 0, v___x_5865_);
v___x_5867_ = v___x_5863_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v___x_5865_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
v_a_5871_ = lean_ctor_get(v___x_5861_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5861_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5861_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5861_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
else
{
lean_object* v_a_5879_; lean_object* v___x_5881_; uint8_t v_isShared_5882_; uint8_t v_isSharedCheck_5886_; 
lean_dec(v___x_5851_);
v_a_5879_ = lean_ctor_get(v___x_5859_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5859_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5881_ = v___x_5859_;
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
else
{
lean_inc(v_a_5879_);
lean_dec(v___x_5859_);
v___x_5881_ = lean_box(0);
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
v_resetjp_5880_:
{
lean_object* v___x_5884_; 
if (v_isShared_5882_ == 0)
{
v___x_5884_ = v___x_5881_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
v___x_5884_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
return v___x_5884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4___boxed(lean_object* v___x_5887_, lean_object* v_a_5888_, lean_object* v_compile_5889_, lean_object* v_logCompileErrors_5890_, lean_object* v_isMeta_5891_, lean_object* v___x_5892_, lean_object* v___x_5893_, lean_object* v_____r_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_){
_start:
{
uint8_t v_compile_boxed_5900_; uint8_t v_logCompileErrors_boxed_5901_; uint8_t v_isMeta_boxed_5902_; lean_object* v_res_5903_; 
v_compile_boxed_5900_ = lean_unbox(v_compile_5889_);
v_logCompileErrors_boxed_5901_ = lean_unbox(v_logCompileErrors_5890_);
v_isMeta_boxed_5902_ = lean_unbox(v_isMeta_5891_);
v_res_5903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___lam__4(v___x_5887_, v_a_5888_, v_compile_boxed_5900_, v_logCompileErrors_boxed_5901_, v_isMeta_boxed_5902_, v___x_5892_, v___x_5893_, v_____r_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
lean_dec(v___y_5898_);
lean_dec_ref(v___y_5897_);
lean_dec(v___y_5896_);
lean_dec_ref(v___y_5895_);
return v_res_5903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object* v_expectedType_5904_, lean_object* v_inst_5905_, lean_object* v___x_5906_, lean_object* v_hasTrace_5907_, lean_object* v_compile_5908_, lean_object* v_logCompileErrors_5909_, lean_object* v_isMeta_5910_, lean_object* v_val_5911_, lean_object* v_____r_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_){
_start:
{
uint8_t v___x_162849__boxed_5918_; uint8_t v_hasTrace_boxed_5919_; uint8_t v_compile_boxed_5920_; uint8_t v_logCompileErrors_boxed_5921_; uint8_t v_isMeta_boxed_5922_; lean_object* v_res_5923_; 
v___x_162849__boxed_5918_ = lean_unbox(v___x_5906_);
v_hasTrace_boxed_5919_ = lean_unbox(v_hasTrace_5907_);
v_compile_boxed_5920_ = lean_unbox(v_compile_5908_);
v_logCompileErrors_boxed_5921_ = lean_unbox(v_logCompileErrors_5909_);
v_isMeta_boxed_5922_ = lean_unbox(v_isMeta_5910_);
v_res_5923_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5904_, v_inst_5905_, v___x_162849__boxed_5918_, v_hasTrace_boxed_5919_, v_compile_boxed_5920_, v_logCompileErrors_boxed_5921_, v_isMeta_boxed_5922_, v_val_5911_, v_____r_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
lean_dec(v___y_5914_);
lean_dec_ref(v___y_5913_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object* v_expectedType_5924_, lean_object* v_inst_5925_, lean_object* v___x_5926_, lean_object* v_compile_5927_, lean_object* v_logCompileErrors_5928_, lean_object* v_isMeta_5929_, lean_object* v_val_5930_, lean_object* v_____r_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_){
_start:
{
uint8_t v___x_162874__boxed_5937_; uint8_t v_compile_boxed_5938_; uint8_t v_logCompileErrors_boxed_5939_; uint8_t v_isMeta_boxed_5940_; lean_object* v_res_5941_; 
v___x_162874__boxed_5937_ = lean_unbox(v___x_5926_);
v_compile_boxed_5938_ = lean_unbox(v_compile_5927_);
v_logCompileErrors_boxed_5939_ = lean_unbox(v_logCompileErrors_5928_);
v_isMeta_boxed_5940_ = lean_unbox(v_isMeta_5929_);
v_res_5941_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5924_, v_inst_5925_, v___x_162874__boxed_5937_, v_compile_boxed_5938_, v_logCompileErrors_boxed_5939_, v_isMeta_boxed_5940_, v_val_5930_, v_____r_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_);
lean_dec(v___y_5935_);
lean_dec_ref(v___y_5934_);
lean_dec(v___y_5933_);
lean_dec_ref(v___y_5932_);
return v_res_5941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22___boxed(lean_object* v_inst_5942_, lean_object* v_expectedType_5943_, lean_object* v___x_5944_, lean_object* v___x_5945_, lean_object* v_compile_5946_, lean_object* v_logCompileErrors_5947_, lean_object* v_isMeta_5948_, lean_object* v_val_5949_, lean_object* v_x_5950_, lean_object* v_x_5951_, lean_object* v_x_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_){
_start:
{
uint8_t v___x_162911__boxed_5958_; uint8_t v___x_162912__boxed_5959_; uint8_t v_compile_boxed_5960_; uint8_t v_logCompileErrors_boxed_5961_; uint8_t v_isMeta_boxed_5962_; lean_object* v_res_5963_; 
v___x_162911__boxed_5958_ = lean_unbox(v___x_5944_);
v___x_162912__boxed_5959_ = lean_unbox(v___x_5945_);
v_compile_boxed_5960_ = lean_unbox(v_compile_5946_);
v_logCompileErrors_boxed_5961_ = lean_unbox(v_logCompileErrors_5947_);
v_isMeta_boxed_5962_ = lean_unbox(v_isMeta_5948_);
v_res_5963_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__22(v_inst_5942_, v_expectedType_5943_, v___x_162911__boxed_5958_, v___x_162912__boxed_5959_, v_compile_boxed_5960_, v_logCompileErrors_boxed_5961_, v_isMeta_boxed_5962_, v_val_5949_, v_x_5950_, v_x_5951_, v_x_5952_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_);
lean_dec(v___y_5956_);
lean_dec_ref(v___y_5955_);
lean_dec(v___y_5954_);
lean_dec_ref(v___y_5953_);
return v_res_5963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25___boxed(lean_object* v_inst_5964_, lean_object* v_expectedType_5965_, lean_object* v___x_5966_, lean_object* v_compile_5967_, lean_object* v_logCompileErrors_5968_, lean_object* v_isMeta_5969_, lean_object* v_val_5970_, lean_object* v_x_5971_, lean_object* v_x_5972_, lean_object* v_x_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_){
_start:
{
uint8_t v___x_163067__boxed_5979_; uint8_t v_compile_boxed_5980_; uint8_t v_logCompileErrors_boxed_5981_; uint8_t v_isMeta_boxed_5982_; lean_object* v_res_5983_; 
v___x_163067__boxed_5979_ = lean_unbox(v___x_5966_);
v_compile_boxed_5980_ = lean_unbox(v_compile_5967_);
v_logCompileErrors_boxed_5981_ = lean_unbox(v_logCompileErrors_5968_);
v_isMeta_boxed_5982_ = lean_unbox(v_isMeta_5969_);
v_res_5983_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16_spec__25(v_inst_5964_, v_expectedType_5965_, v___x_163067__boxed_5979_, v_compile_boxed_5980_, v_logCompileErrors_boxed_5981_, v_isMeta_boxed_5982_, v_val_5970_, v_x_5971_, v_x_5972_, v_x_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_);
lean_dec(v___y_5977_);
lean_dec_ref(v___y_5976_);
lean_dec(v___y_5975_);
lean_dec_ref(v___y_5974_);
return v_res_5983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object* v_inst_5984_, lean_object* v_expectedType_5985_, lean_object* v___x_5986_, lean_object* v___x_5987_, lean_object* v_compile_5988_, lean_object* v_logCompileErrors_5989_, lean_object* v_isMeta_5990_, lean_object* v_val_5991_, lean_object* v_x_5992_, lean_object* v_x_5993_, lean_object* v_x_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_){
_start:
{
uint8_t v___x_163235__boxed_6000_; uint8_t v___x_163236__boxed_6001_; uint8_t v_compile_boxed_6002_; uint8_t v_logCompileErrors_boxed_6003_; uint8_t v_isMeta_boxed_6004_; lean_object* v_res_6005_; 
v___x_163235__boxed_6000_ = lean_unbox(v___x_5986_);
v___x_163236__boxed_6001_ = lean_unbox(v___x_5987_);
v_compile_boxed_6002_ = lean_unbox(v_compile_5988_);
v_logCompileErrors_boxed_6003_ = lean_unbox(v_logCompileErrors_5989_);
v_isMeta_boxed_6004_ = lean_unbox(v_isMeta_5990_);
v_res_6005_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_inst_5984_, v_expectedType_5985_, v___x_163235__boxed_6000_, v___x_163236__boxed_6001_, v_compile_boxed_6002_, v_logCompileErrors_boxed_6003_, v_isMeta_boxed_6004_, v_val_5991_, v_x_5992_, v_x_5993_, v_x_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_);
lean_dec(v___y_5998_);
lean_dec_ref(v___y_5997_);
lean_dec(v___y_5996_);
lean_dec_ref(v___y_5995_);
lean_dec(v_x_5994_);
return v_res_6005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16___boxed(lean_object* v_inst_6006_, lean_object* v_expectedType_6007_, lean_object* v___x_6008_, lean_object* v_compile_6009_, lean_object* v_logCompileErrors_6010_, lean_object* v_isMeta_6011_, lean_object* v_val_6012_, lean_object* v_x_6013_, lean_object* v_x_6014_, lean_object* v_x_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_){
_start:
{
uint8_t v___x_163404__boxed_6021_; uint8_t v_compile_boxed_6022_; uint8_t v_logCompileErrors_boxed_6023_; uint8_t v_isMeta_boxed_6024_; lean_object* v_res_6025_; 
v___x_163404__boxed_6021_ = lean_unbox(v___x_6008_);
v_compile_boxed_6022_ = lean_unbox(v_compile_6009_);
v_logCompileErrors_boxed_6023_ = lean_unbox(v_logCompileErrors_6010_);
v_isMeta_boxed_6024_ = lean_unbox(v_isMeta_6011_);
v_res_6025_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__16(v_inst_6006_, v_expectedType_6007_, v___x_163404__boxed_6021_, v_compile_boxed_6022_, v_logCompileErrors_boxed_6023_, v_isMeta_boxed_6024_, v_val_6012_, v_x_6013_, v_x_6014_, v_x_6015_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_);
lean_dec(v___y_6019_);
lean_dec_ref(v___y_6018_);
lean_dec(v___y_6017_);
lean_dec_ref(v___y_6016_);
lean_dec(v_x_6015_);
return v_res_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12___boxed(lean_object* v_inst_6026_, lean_object* v_expectedType_6027_, lean_object* v___x_6028_, lean_object* v_compile_6029_, lean_object* v_logCompileErrors_6030_, lean_object* v_isMeta_6031_, lean_object* v_val_6032_, lean_object* v_x_6033_, lean_object* v_x_6034_, lean_object* v_x_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_){
_start:
{
uint8_t v___x_163572__boxed_6041_; uint8_t v_compile_boxed_6042_; uint8_t v_logCompileErrors_boxed_6043_; uint8_t v_isMeta_boxed_6044_; lean_object* v_res_6045_; 
v___x_163572__boxed_6041_ = lean_unbox(v___x_6028_);
v_compile_boxed_6042_ = lean_unbox(v_compile_6029_);
v_logCompileErrors_boxed_6043_ = lean_unbox(v_logCompileErrors_6030_);
v_isMeta_boxed_6044_ = lean_unbox(v_isMeta_6031_);
v_res_6045_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10_spec__12(v_inst_6026_, v_expectedType_6027_, v___x_163572__boxed_6041_, v_compile_boxed_6042_, v_logCompileErrors_boxed_6043_, v_isMeta_boxed_6044_, v_val_6032_, v_x_6033_, v_x_6034_, v_x_6035_, v___y_6036_, v___y_6037_, v___y_6038_, v___y_6039_);
lean_dec(v___y_6039_);
lean_dec_ref(v___y_6038_);
lean_dec(v___y_6037_);
lean_dec_ref(v___y_6036_);
return v_res_6045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object* v_inst_6046_, lean_object* v_expectedType_6047_, lean_object* v___x_6048_, lean_object* v_compile_6049_, lean_object* v_logCompileErrors_6050_, lean_object* v_isMeta_6051_, lean_object* v_val_6052_, lean_object* v_x_6053_, lean_object* v_x_6054_, lean_object* v_x_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_){
_start:
{
uint8_t v___x_163741__boxed_6061_; uint8_t v_compile_boxed_6062_; uint8_t v_logCompileErrors_boxed_6063_; uint8_t v_isMeta_boxed_6064_; lean_object* v_res_6065_; 
v___x_163741__boxed_6061_ = lean_unbox(v___x_6048_);
v_compile_boxed_6062_ = lean_unbox(v_compile_6049_);
v_logCompileErrors_boxed_6063_ = lean_unbox(v_logCompileErrors_6050_);
v_isMeta_boxed_6064_ = lean_unbox(v_isMeta_6051_);
v_res_6065_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__10(v_inst_6046_, v_expectedType_6047_, v___x_163741__boxed_6061_, v_compile_boxed_6062_, v_logCompileErrors_boxed_6063_, v_isMeta_boxed_6064_, v_val_6052_, v_x_6053_, v_x_6054_, v_x_6055_, v___y_6056_, v___y_6057_, v___y_6058_, v___y_6059_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v_x_6055_);
return v_res_6065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_6066_ = _args[0];
lean_object* v_fst_6067_ = _args[1];
lean_object* v_args_6068_ = _args[2];
lean_object* v___x_6069_ = _args[3];
lean_object* v_compile_6070_ = _args[4];
lean_object* v_logCompileErrors_6071_ = _args[5];
lean_object* v___x_6072_ = _args[6];
lean_object* v_isMeta_6073_ = _args[7];
lean_object* v_val_6074_ = _args[8];
lean_object* v_expectedType_6075_ = _args[9];
lean_object* v_a_6076_ = _args[10];
lean_object* v_b_6077_ = _args[11];
lean_object* v___y_6078_ = _args[12];
lean_object* v___y_6079_ = _args[13];
lean_object* v___y_6080_ = _args[14];
lean_object* v___y_6081_ = _args[15];
lean_object* v___y_6082_ = _args[16];
_start:
{
uint8_t v___x_163937__boxed_6083_; uint8_t v_compile_boxed_6084_; uint8_t v_logCompileErrors_boxed_6085_; uint8_t v___x_163938__boxed_6086_; uint8_t v_isMeta_boxed_6087_; lean_object* v_res_6088_; 
v___x_163937__boxed_6083_ = lean_unbox(v___x_6069_);
v_compile_boxed_6084_ = lean_unbox(v_compile_6070_);
v_logCompileErrors_boxed_6085_ = lean_unbox(v_logCompileErrors_6071_);
v___x_163938__boxed_6086_ = lean_unbox(v___x_6072_);
v_isMeta_boxed_6087_ = lean_unbox(v_isMeta_6073_);
v_res_6088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_6066_, v_fst_6067_, v_args_6068_, v___x_163937__boxed_6083_, v_compile_boxed_6084_, v_logCompileErrors_boxed_6085_, v___x_163938__boxed_6086_, v_isMeta_boxed_6087_, v_val_6074_, v_expectedType_6075_, v_a_6076_, v_b_6077_, v___y_6078_, v___y_6079_, v___y_6080_, v___y_6081_);
lean_dec(v___y_6081_);
lean_dec_ref(v___y_6080_);
lean_dec(v___y_6079_);
lean_dec_ref(v___y_6078_);
lean_dec_ref(v_args_6068_);
lean_dec_ref(v_fst_6067_);
lean_dec(v_upperBound_6066_);
return v_res_6088_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg___boxed(lean_object* v_upperBound_6089_, lean_object* v_fst_6090_, lean_object* v_args_6091_, lean_object* v_compile_6092_, lean_object* v_logCompileErrors_6093_, lean_object* v___x_6094_, lean_object* v_isMeta_6095_, lean_object* v_val_6096_, lean_object* v_expectedType_6097_, lean_object* v_a_6098_, lean_object* v_b_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_){
_start:
{
uint8_t v_compile_boxed_6105_; uint8_t v_logCompileErrors_boxed_6106_; uint8_t v___x_164088__boxed_6107_; uint8_t v_isMeta_boxed_6108_; lean_object* v_res_6109_; 
v_compile_boxed_6105_ = lean_unbox(v_compile_6092_);
v_logCompileErrors_boxed_6106_ = lean_unbox(v_logCompileErrors_6093_);
v___x_164088__boxed_6107_ = lean_unbox(v___x_6094_);
v_isMeta_boxed_6108_ = lean_unbox(v_isMeta_6095_);
v_res_6109_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(v_upperBound_6089_, v_fst_6090_, v_args_6091_, v_compile_boxed_6105_, v_logCompileErrors_boxed_6106_, v___x_164088__boxed_6107_, v_isMeta_boxed_6108_, v_val_6096_, v_expectedType_6097_, v_a_6098_, v_b_6099_, v___y_6100_, v___y_6101_, v___y_6102_, v___y_6103_);
lean_dec(v___y_6103_);
lean_dec_ref(v___y_6102_);
lean_dec(v___y_6101_);
lean_dec_ref(v___y_6100_);
lean_dec_ref(v_args_6091_);
lean_dec_ref(v_fst_6090_);
lean_dec(v_upperBound_6089_);
return v_res_6109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_6110_ = _args[0];
lean_object* v_fst_6111_ = _args[1];
lean_object* v_args_6112_ = _args[2];
lean_object* v___x_6113_ = _args[3];
lean_object* v_compile_6114_ = _args[4];
lean_object* v_logCompileErrors_6115_ = _args[5];
lean_object* v___x_6116_ = _args[6];
lean_object* v_isMeta_6117_ = _args[7];
lean_object* v_val_6118_ = _args[8];
lean_object* v_expectedType_6119_ = _args[9];
lean_object* v_a_6120_ = _args[10];
lean_object* v_b_6121_ = _args[11];
lean_object* v___y_6122_ = _args[12];
lean_object* v___y_6123_ = _args[13];
lean_object* v___y_6124_ = _args[14];
lean_object* v___y_6125_ = _args[15];
lean_object* v___y_6126_ = _args[16];
_start:
{
uint8_t v___x_164247__boxed_6127_; uint8_t v_compile_boxed_6128_; uint8_t v_logCompileErrors_boxed_6129_; uint8_t v___x_164248__boxed_6130_; uint8_t v_isMeta_boxed_6131_; lean_object* v_res_6132_; 
v___x_164247__boxed_6127_ = lean_unbox(v___x_6113_);
v_compile_boxed_6128_ = lean_unbox(v_compile_6114_);
v_logCompileErrors_boxed_6129_ = lean_unbox(v_logCompileErrors_6115_);
v___x_164248__boxed_6130_ = lean_unbox(v___x_6116_);
v_isMeta_boxed_6131_ = lean_unbox(v_isMeta_6117_);
v_res_6132_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(v_upperBound_6110_, v_fst_6111_, v_args_6112_, v___x_164247__boxed_6127_, v_compile_boxed_6128_, v_logCompileErrors_boxed_6129_, v___x_164248__boxed_6130_, v_isMeta_boxed_6131_, v_val_6118_, v_expectedType_6119_, v_a_6120_, v_b_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
lean_dec(v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
lean_dec_ref(v_args_6112_);
lean_dec_ref(v_fst_6111_);
lean_dec(v_upperBound_6110_);
return v_res_6132_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg___boxed(lean_object* v_upperBound_6133_, lean_object* v_fst_6134_, lean_object* v_args_6135_, lean_object* v___x_6136_, lean_object* v_compile_6137_, lean_object* v_logCompileErrors_6138_, lean_object* v_isMeta_6139_, lean_object* v_val_6140_, lean_object* v_expectedType_6141_, lean_object* v_a_6142_, lean_object* v_b_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_){
_start:
{
uint8_t v___x_164408__boxed_6149_; uint8_t v_compile_boxed_6150_; uint8_t v_logCompileErrors_boxed_6151_; uint8_t v_isMeta_boxed_6152_; lean_object* v_res_6153_; 
v___x_164408__boxed_6149_ = lean_unbox(v___x_6136_);
v_compile_boxed_6150_ = lean_unbox(v_compile_6137_);
v_logCompileErrors_boxed_6151_ = lean_unbox(v_logCompileErrors_6138_);
v_isMeta_boxed_6152_ = lean_unbox(v_isMeta_6139_);
v_res_6153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(v_upperBound_6133_, v_fst_6134_, v_args_6135_, v___x_164408__boxed_6149_, v_compile_boxed_6150_, v_logCompileErrors_boxed_6151_, v_isMeta_boxed_6152_, v_val_6140_, v_expectedType_6141_, v_a_6142_, v_b_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
lean_dec_ref(v_args_6135_);
lean_dec_ref(v_fst_6134_);
lean_dec(v_upperBound_6133_);
return v_res_6153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object* v_inst_6154_, lean_object* v_expectedType_6155_, lean_object* v_compile_6156_, lean_object* v_logCompileErrors_6157_, lean_object* v_isMeta_6158_, lean_object* v_a_6159_, lean_object* v_a_6160_, lean_object* v_a_6161_, lean_object* v_a_6162_, lean_object* v_a_6163_){
_start:
{
uint8_t v_compile_boxed_6164_; uint8_t v_logCompileErrors_boxed_6165_; uint8_t v_isMeta_boxed_6166_; lean_object* v_res_6167_; 
v_compile_boxed_6164_ = lean_unbox(v_compile_6156_);
v_logCompileErrors_boxed_6165_ = lean_unbox(v_logCompileErrors_6157_);
v_isMeta_boxed_6166_ = lean_unbox(v_isMeta_6158_);
v_res_6167_ = l_Lean_Meta_wrapInstance(v_inst_6154_, v_expectedType_6155_, v_compile_boxed_6164_, v_logCompileErrors_boxed_6165_, v_isMeta_boxed_6166_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_);
lean_dec(v_a_6162_);
lean_dec_ref(v_a_6161_);
lean_dec(v_a_6160_);
lean_dec_ref(v_a_6159_);
return v_res_6167_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7(lean_object* v_mvarId_6168_, lean_object* v_val_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_){
_start:
{
lean_object* v___x_6175_; 
v___x_6175_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_mvarId_6168_, v_val_6169_, v___y_6171_);
return v___x_6175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object* v_mvarId_6176_, lean_object* v_val_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_){
_start:
{
lean_object* v_res_6183_; 
v_res_6183_ = l_Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7(v_mvarId_6176_, v_val_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
return v_res_6183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8(lean_object* v_upperBound_6184_, lean_object* v_fst_6185_, lean_object* v_args_6186_, uint8_t v_compile_6187_, uint8_t v_logCompileErrors_6188_, uint8_t v___x_6189_, uint8_t v_isMeta_6190_, lean_object* v_val_6191_, lean_object* v_expectedType_6192_, lean_object* v_inst_6193_, lean_object* v_R_6194_, lean_object* v_a_6195_, lean_object* v_b_6196_, lean_object* v_c_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_){
_start:
{
lean_object* v___x_6203_; 
v___x_6203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___redArg(v_upperBound_6184_, v_fst_6185_, v_args_6186_, v_compile_6187_, v_logCompileErrors_6188_, v___x_6189_, v_isMeta_6190_, v_val_6191_, v_expectedType_6192_, v_a_6195_, v_b_6196_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
return v___x_6203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_6204_ = _args[0];
lean_object* v_fst_6205_ = _args[1];
lean_object* v_args_6206_ = _args[2];
lean_object* v_compile_6207_ = _args[3];
lean_object* v_logCompileErrors_6208_ = _args[4];
lean_object* v___x_6209_ = _args[5];
lean_object* v_isMeta_6210_ = _args[6];
lean_object* v_val_6211_ = _args[7];
lean_object* v_expectedType_6212_ = _args[8];
lean_object* v_inst_6213_ = _args[9];
lean_object* v_R_6214_ = _args[10];
lean_object* v_a_6215_ = _args[11];
lean_object* v_b_6216_ = _args[12];
lean_object* v_c_6217_ = _args[13];
lean_object* v___y_6218_ = _args[14];
lean_object* v___y_6219_ = _args[15];
lean_object* v___y_6220_ = _args[16];
lean_object* v___y_6221_ = _args[17];
lean_object* v___y_6222_ = _args[18];
_start:
{
uint8_t v_compile_boxed_6223_; uint8_t v_logCompileErrors_boxed_6224_; uint8_t v___x_168902__boxed_6225_; uint8_t v_isMeta_boxed_6226_; lean_object* v_res_6227_; 
v_compile_boxed_6223_ = lean_unbox(v_compile_6207_);
v_logCompileErrors_boxed_6224_ = lean_unbox(v_logCompileErrors_6208_);
v___x_168902__boxed_6225_ = lean_unbox(v___x_6209_);
v_isMeta_boxed_6226_ = lean_unbox(v_isMeta_6210_);
v_res_6227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__8(v_upperBound_6204_, v_fst_6205_, v_args_6206_, v_compile_boxed_6223_, v_logCompileErrors_boxed_6224_, v___x_168902__boxed_6225_, v_isMeta_boxed_6226_, v_val_6211_, v_expectedType_6212_, v_inst_6213_, v_R_6214_, v_a_6215_, v_b_6216_, v_c_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_);
lean_dec(v___y_6221_);
lean_dec_ref(v___y_6220_);
lean_dec(v___y_6219_);
lean_dec_ref(v___y_6218_);
lean_dec_ref(v_args_6206_);
lean_dec_ref(v_fst_6205_);
lean_dec(v_upperBound_6204_);
return v_res_6227_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17(lean_object* v_00_u03b1_6228_, lean_object* v_x_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_){
_start:
{
lean_object* v___x_6235_; 
v___x_6235_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___redArg(v_x_6229_);
return v___x_6235_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17___boxed(lean_object* v_00_u03b1_6236_, lean_object* v_x_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_){
_start:
{
lean_object* v_res_6243_; 
v_res_6243_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__12_spec__17(v_00_u03b1_6236_, v_x_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
lean_dec(v___y_6241_);
lean_dec_ref(v___y_6240_);
lean_dec(v___y_6239_);
lean_dec_ref(v___y_6238_);
return v_res_6243_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object* v_upperBound_6244_, lean_object* v_fst_6245_, lean_object* v_args_6246_, uint8_t v___x_6247_, uint8_t v_compile_6248_, uint8_t v_logCompileErrors_6249_, uint8_t v___x_6250_, uint8_t v_isMeta_6251_, lean_object* v_val_6252_, lean_object* v_expectedType_6253_, lean_object* v_inst_6254_, lean_object* v_R_6255_, lean_object* v_a_6256_, lean_object* v_b_6257_, lean_object* v_c_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_){
_start:
{
lean_object* v___x_6264_; 
v___x_6264_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_6244_, v_fst_6245_, v_args_6246_, v___x_6247_, v_compile_6248_, v_logCompileErrors_6249_, v___x_6250_, v_isMeta_6251_, v_val_6252_, v_expectedType_6253_, v_a_6256_, v_b_6257_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_);
return v___x_6264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object** _args){
lean_object* v_upperBound_6265_ = _args[0];
lean_object* v_fst_6266_ = _args[1];
lean_object* v_args_6267_ = _args[2];
lean_object* v___x_6268_ = _args[3];
lean_object* v_compile_6269_ = _args[4];
lean_object* v_logCompileErrors_6270_ = _args[5];
lean_object* v___x_6271_ = _args[6];
lean_object* v_isMeta_6272_ = _args[7];
lean_object* v_val_6273_ = _args[8];
lean_object* v_expectedType_6274_ = _args[9];
lean_object* v_inst_6275_ = _args[10];
lean_object* v_R_6276_ = _args[11];
lean_object* v_a_6277_ = _args[12];
lean_object* v_b_6278_ = _args[13];
lean_object* v_c_6279_ = _args[14];
lean_object* v___y_6280_ = _args[15];
lean_object* v___y_6281_ = _args[16];
lean_object* v___y_6282_ = _args[17];
lean_object* v___y_6283_ = _args[18];
lean_object* v___y_6284_ = _args[19];
_start:
{
uint8_t v___x_168954__boxed_6285_; uint8_t v_compile_boxed_6286_; uint8_t v_logCompileErrors_boxed_6287_; uint8_t v___x_168955__boxed_6288_; uint8_t v_isMeta_boxed_6289_; lean_object* v_res_6290_; 
v___x_168954__boxed_6285_ = lean_unbox(v___x_6268_);
v_compile_boxed_6286_ = lean_unbox(v_compile_6269_);
v_logCompileErrors_boxed_6287_ = lean_unbox(v_logCompileErrors_6270_);
v___x_168955__boxed_6288_ = lean_unbox(v___x_6271_);
v_isMeta_boxed_6289_ = lean_unbox(v_isMeta_6272_);
v_res_6290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(v_upperBound_6265_, v_fst_6266_, v_args_6267_, v___x_168954__boxed_6285_, v_compile_boxed_6286_, v_logCompileErrors_boxed_6287_, v___x_168955__boxed_6288_, v_isMeta_boxed_6289_, v_val_6273_, v_expectedType_6274_, v_inst_6275_, v_R_6276_, v_a_6277_, v_b_6278_, v_c_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_);
lean_dec(v___y_6283_);
lean_dec_ref(v___y_6282_);
lean_dec(v___y_6281_);
lean_dec_ref(v___y_6280_);
lean_dec_ref(v_args_6267_);
lean_dec_ref(v_fst_6266_);
lean_dec(v_upperBound_6265_);
return v_res_6290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15(lean_object* v_upperBound_6291_, lean_object* v_fst_6292_, lean_object* v_args_6293_, uint8_t v___x_6294_, uint8_t v_compile_6295_, uint8_t v_logCompileErrors_6296_, uint8_t v_isMeta_6297_, lean_object* v_val_6298_, lean_object* v_expectedType_6299_, lean_object* v_inst_6300_, lean_object* v_R_6301_, lean_object* v_a_6302_, lean_object* v_b_6303_, lean_object* v_c_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_){
_start:
{
lean_object* v___x_6310_; 
v___x_6310_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___redArg(v_upperBound_6291_, v_fst_6292_, v_args_6293_, v___x_6294_, v_compile_6295_, v_logCompileErrors_6296_, v_isMeta_6297_, v_val_6298_, v_expectedType_6299_, v_a_6302_, v_b_6303_, v___y_6305_, v___y_6306_, v___y_6307_, v___y_6308_);
return v___x_6310_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object** _args){
lean_object* v_upperBound_6311_ = _args[0];
lean_object* v_fst_6312_ = _args[1];
lean_object* v_args_6313_ = _args[2];
lean_object* v___x_6314_ = _args[3];
lean_object* v_compile_6315_ = _args[4];
lean_object* v_logCompileErrors_6316_ = _args[5];
lean_object* v_isMeta_6317_ = _args[6];
lean_object* v_val_6318_ = _args[7];
lean_object* v_expectedType_6319_ = _args[8];
lean_object* v_inst_6320_ = _args[9];
lean_object* v_R_6321_ = _args[10];
lean_object* v_a_6322_ = _args[11];
lean_object* v_b_6323_ = _args[12];
lean_object* v_c_6324_ = _args[13];
lean_object* v___y_6325_ = _args[14];
lean_object* v___y_6326_ = _args[15];
lean_object* v___y_6327_ = _args[16];
lean_object* v___y_6328_ = _args[17];
lean_object* v___y_6329_ = _args[18];
_start:
{
uint8_t v___x_168989__boxed_6330_; uint8_t v_compile_boxed_6331_; uint8_t v_logCompileErrors_boxed_6332_; uint8_t v_isMeta_boxed_6333_; lean_object* v_res_6334_; 
v___x_168989__boxed_6330_ = lean_unbox(v___x_6314_);
v_compile_boxed_6331_ = lean_unbox(v_compile_6315_);
v_logCompileErrors_boxed_6332_ = lean_unbox(v_logCompileErrors_6316_);
v_isMeta_boxed_6333_ = lean_unbox(v_isMeta_6317_);
v_res_6334_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__15(v_upperBound_6311_, v_fst_6312_, v_args_6313_, v___x_168989__boxed_6330_, v_compile_boxed_6331_, v_logCompileErrors_boxed_6332_, v_isMeta_boxed_6333_, v_val_6318_, v_expectedType_6319_, v_inst_6320_, v_R_6321_, v_a_6322_, v_b_6323_, v_c_6324_, v___y_6325_, v___y_6326_, v___y_6327_, v___y_6328_);
lean_dec(v___y_6328_);
lean_dec_ref(v___y_6327_);
lean_dec(v___y_6326_);
lean_dec_ref(v___y_6325_);
lean_dec_ref(v_args_6313_);
lean_dec_ref(v_fst_6312_);
lean_dec(v_upperBound_6311_);
return v_res_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(lean_object* v_00_u03b1_6335_, lean_object* v_constName_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_){
_start:
{
lean_object* v___x_6342_; 
v___x_6342_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___redArg(v_constName_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
return v___x_6342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4___boxed(lean_object* v_00_u03b1_6343_, lean_object* v_constName_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_, lean_object* v___y_6349_){
_start:
{
lean_object* v_res_6350_; 
v_res_6350_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4(v_00_u03b1_6343_, v_constName_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_);
lean_dec(v___y_6348_);
lean_dec_ref(v___y_6347_);
lean_dec(v___y_6346_);
lean_dec_ref(v___y_6345_);
return v_res_6350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8(lean_object* v_00_u03b2_6351_, lean_object* v_x_6352_, lean_object* v_x_6353_, lean_object* v_x_6354_){
_start:
{
lean_object* v___x_6355_; 
v___x_6355_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8___redArg(v_x_6352_, v_x_6353_, v_x_6354_);
return v___x_6355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20(lean_object* v_upperBound_6356_, lean_object* v_fst_6357_, lean_object* v_args_6358_, uint8_t v___x_6359_, uint8_t v_compile_6360_, uint8_t v_logCompileErrors_6361_, uint8_t v___x_6362_, uint8_t v_isMeta_6363_, lean_object* v_val_6364_, lean_object* v_expectedType_6365_, lean_object* v_inst_6366_, lean_object* v_R_6367_, lean_object* v_a_6368_, lean_object* v_b_6369_, lean_object* v_c_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_){
_start:
{
lean_object* v___x_6376_; 
v___x_6376_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___redArg(v_upperBound_6356_, v_fst_6357_, v_args_6358_, v___x_6359_, v_compile_6360_, v_logCompileErrors_6361_, v___x_6362_, v_isMeta_6363_, v_val_6364_, v_expectedType_6365_, v_a_6368_, v_b_6369_, v___y_6371_, v___y_6372_, v___y_6373_, v___y_6374_);
return v___x_6376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20___boxed(lean_object** _args){
lean_object* v_upperBound_6377_ = _args[0];
lean_object* v_fst_6378_ = _args[1];
lean_object* v_args_6379_ = _args[2];
lean_object* v___x_6380_ = _args[3];
lean_object* v_compile_6381_ = _args[4];
lean_object* v_logCompileErrors_6382_ = _args[5];
lean_object* v___x_6383_ = _args[6];
lean_object* v_isMeta_6384_ = _args[7];
lean_object* v_val_6385_ = _args[8];
lean_object* v_expectedType_6386_ = _args[9];
lean_object* v_inst_6387_ = _args[10];
lean_object* v_R_6388_ = _args[11];
lean_object* v_a_6389_ = _args[12];
lean_object* v_b_6390_ = _args[13];
lean_object* v_c_6391_ = _args[14];
lean_object* v___y_6392_ = _args[15];
lean_object* v___y_6393_ = _args[16];
lean_object* v___y_6394_ = _args[17];
lean_object* v___y_6395_ = _args[18];
lean_object* v___y_6396_ = _args[19];
_start:
{
uint8_t v___x_169046__boxed_6397_; uint8_t v_compile_boxed_6398_; uint8_t v_logCompileErrors_boxed_6399_; uint8_t v___x_169047__boxed_6400_; uint8_t v_isMeta_boxed_6401_; lean_object* v_res_6402_; 
v___x_169046__boxed_6397_ = lean_unbox(v___x_6380_);
v_compile_boxed_6398_ = lean_unbox(v_compile_6381_);
v_logCompileErrors_boxed_6399_ = lean_unbox(v_logCompileErrors_6382_);
v___x_169047__boxed_6400_ = lean_unbox(v___x_6383_);
v_isMeta_boxed_6401_ = lean_unbox(v_isMeta_6384_);
v_res_6402_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__20(v_upperBound_6377_, v_fst_6378_, v_args_6379_, v___x_169046__boxed_6397_, v_compile_boxed_6398_, v_logCompileErrors_boxed_6399_, v___x_169047__boxed_6400_, v_isMeta_boxed_6401_, v_val_6385_, v_expectedType_6386_, v_inst_6387_, v_R_6388_, v_a_6389_, v_b_6390_, v_c_6391_, v___y_6392_, v___y_6393_, v___y_6394_, v___y_6395_);
lean_dec(v___y_6395_);
lean_dec_ref(v___y_6394_);
lean_dec(v___y_6393_);
lean_dec_ref(v___y_6392_);
lean_dec_ref(v_args_6379_);
lean_dec_ref(v_fst_6378_);
lean_dec(v_upperBound_6377_);
return v_res_6402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7(lean_object* v_00_u03b1_6403_, lean_object* v_ref_6404_, lean_object* v_constName_6405_, lean_object* v___y_6406_, lean_object* v___y_6407_, lean_object* v___y_6408_, lean_object* v___y_6409_){
_start:
{
lean_object* v___x_6411_; 
v___x_6411_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___redArg(v_ref_6404_, v_constName_6405_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_);
return v___x_6411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7___boxed(lean_object* v_00_u03b1_6412_, lean_object* v_ref_6413_, lean_object* v_constName_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_){
_start:
{
lean_object* v_res_6420_; 
v_res_6420_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7(v_00_u03b1_6412_, v_ref_6413_, v_constName_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_);
lean_dec(v___y_6418_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v_ref_6413_);
return v_res_6420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_6421_, lean_object* v_x_6422_, size_t v_x_6423_, size_t v_x_6424_, lean_object* v_x_6425_, lean_object* v_x_6426_){
_start:
{
lean_object* v___x_6427_; 
v___x_6427_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___redArg(v_x_6422_, v_x_6423_, v_x_6424_, v_x_6425_, v_x_6426_);
return v___x_6427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_6428_, lean_object* v_x_6429_, lean_object* v_x_6430_, lean_object* v_x_6431_, lean_object* v_x_6432_, lean_object* v_x_6433_){
_start:
{
size_t v_x_169097__boxed_6434_; size_t v_x_169098__boxed_6435_; lean_object* v_res_6436_; 
v_x_169097__boxed_6434_ = lean_unbox_usize(v_x_6430_);
lean_dec(v_x_6430_);
v_x_169098__boxed_6435_ = lean_unbox_usize(v_x_6431_);
lean_dec(v_x_6431_);
v_res_6436_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11(v_00_u03b2_6428_, v_x_6429_, v_x_169097__boxed_6434_, v_x_169098__boxed_6435_, v_x_6432_, v_x_6433_);
return v_res_6436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21(lean_object* v_00_u03b1_6437_, lean_object* v_ref_6438_, lean_object* v_msg_6439_, lean_object* v_declHint_6440_, lean_object* v___y_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_, lean_object* v___y_6444_){
_start:
{
lean_object* v___x_6446_; 
v___x_6446_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___redArg(v_ref_6438_, v_msg_6439_, v_declHint_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_);
return v___x_6446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21___boxed(lean_object* v_00_u03b1_6447_, lean_object* v_ref_6448_, lean_object* v_msg_6449_, lean_object* v_declHint_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_){
_start:
{
lean_object* v_res_6456_; 
v_res_6456_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21(v_00_u03b1_6447_, v_ref_6448_, v_msg_6449_, v_declHint_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
lean_dec(v___y_6454_);
lean_dec_ref(v___y_6453_);
lean_dec(v___y_6452_);
lean_dec_ref(v___y_6451_);
lean_dec(v_ref_6448_);
return v_res_6456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24(lean_object* v_00_u03b2_6457_, lean_object* v_n_6458_, lean_object* v_k_6459_, lean_object* v_v_6460_){
_start:
{
lean_object* v___x_6461_; 
v___x_6461_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24___redArg(v_n_6458_, v_k_6459_, v_v_6460_);
return v___x_6461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25(lean_object* v_00_u03b2_6462_, size_t v_depth_6463_, lean_object* v_keys_6464_, lean_object* v_vals_6465_, lean_object* v_heq_6466_, lean_object* v_i_6467_, lean_object* v_entries_6468_){
_start:
{
lean_object* v___x_6469_; 
v___x_6469_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___redArg(v_depth_6463_, v_keys_6464_, v_vals_6465_, v_i_6467_, v_entries_6468_);
return v___x_6469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25___boxed(lean_object* v_00_u03b2_6470_, lean_object* v_depth_6471_, lean_object* v_keys_6472_, lean_object* v_vals_6473_, lean_object* v_heq_6474_, lean_object* v_i_6475_, lean_object* v_entries_6476_){
_start:
{
size_t v_depth_boxed_6477_; lean_object* v_res_6478_; 
v_depth_boxed_6477_ = lean_unbox_usize(v_depth_6471_);
lean_dec(v_depth_6471_);
v_res_6478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__25(v_00_u03b2_6470_, v_depth_boxed_6477_, v_keys_6472_, v_vals_6473_, v_heq_6474_, v_i_6475_, v_entries_6476_);
lean_dec_ref(v_vals_6473_);
lean_dec_ref(v_keys_6472_);
return v_res_6478_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31(lean_object* v_msg_6479_, lean_object* v_declHint_6480_, lean_object* v___y_6481_, lean_object* v___y_6482_, lean_object* v___y_6483_, lean_object* v___y_6484_){
_start:
{
lean_object* v___x_6486_; 
v___x_6486_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___redArg(v_msg_6479_, v_declHint_6480_, v___y_6484_);
return v___x_6486_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31___boxed(lean_object* v_msg_6487_, lean_object* v_declHint_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_){
_start:
{
lean_object* v_res_6494_; 
v_res_6494_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__28_spec__31(v_msg_6487_, v_declHint_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_);
lean_dec(v___y_6492_);
lean_dec_ref(v___y_6491_);
lean_dec(v___y_6490_);
lean_dec_ref(v___y_6489_);
return v_res_6494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29(lean_object* v_00_u03b1_6495_, lean_object* v_ref_6496_, lean_object* v_msg_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_){
_start:
{
lean_object* v___x_6503_; 
v___x_6503_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___redArg(v_ref_6496_, v_msg_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_);
return v___x_6503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29___boxed(lean_object* v_00_u03b1_6504_, lean_object* v_ref_6505_, lean_object* v_msg_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_){
_start:
{
lean_object* v_res_6512_; 
v_res_6512_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__4_spec__7_spec__21_spec__29(v_00_u03b1_6504_, v_ref_6505_, v_msg_6506_, v___y_6507_, v___y_6508_, v___y_6509_, v___y_6510_);
lean_dec(v___y_6510_);
lean_dec_ref(v___y_6509_);
lean_dec(v___y_6508_);
lean_dec_ref(v___y_6507_);
lean_dec(v_ref_6505_);
return v_res_6512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32(lean_object* v_00_u03b2_6513_, lean_object* v_x_6514_, lean_object* v_x_6515_, lean_object* v_x_6516_, lean_object* v_x_6517_){
_start:
{
lean_object* v___x_6518_; 
v___x_6518_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_wrapInstance_spec__7_spec__8_spec__11_spec__24_spec__32___redArg(v_x_6514_, v_x_6515_, v_x_6516_, v_x_6517_);
return v___x_6518_;
}
}
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_700393601____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_1995055096____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2138875086____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_instances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_instances);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2650342594____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_data = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_data);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Structure(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WrapInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_WrapInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_WrapInstance(builtin);
}
#ifdef __cplusplus
}
#endif
