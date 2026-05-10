// Lean compiler output
// Module: LeanIR
// Imports: public import Init public meta import Init import Lean.CoreM import Lean.Util.ForEachExpr import all Lean.Util.Path import all Lean.Environment import Lean.Compiler.Options import Lean.Compiler.IR.CompilerM import all Lean.Compiler.CSimpAttr import Lean.Compiler.LCNF.EmitC import Lean.Language.Lean import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.LCNF.Main
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stderr();
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_importModulesCore(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
lean_object* l_Lean_finalizeImport(lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_toName(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_setOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_ir_export_entries(lean_object*);
lean_object* l_Lean_mkModuleData(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_IO_println___at___00Lean_Environment_displayStats_spec__1(lean_object*);
lean_object* l_Lean_ModuleSetup_load(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_getBuildDir();
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedClassState_default;
extern lean_object* l_Lean_Meta_Match_Extension_instInhabitedState;
extern lean_object* l_Lean_Compiler_compiler_inLeanIR;
lean_object* l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_maxHeartbeats;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_saveModuleData(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_emitC(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times();
lean_object* l_Lean_Environment_displayStats(lean_object*);
lean_object* l_Lean_Compiler_LCNF_resumeCompilation(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
double lean_float_of_nat(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_impureSigExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedImportState_default;
lean_object* l_Lean_withImporting___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_CSimp_ext;
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instanceExtension;
extern lean_object* l_Lean_classExtension;
extern lean_object* l_Lean_Meta_Match_Extension_extension;
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
uint8_t l_Lean_instOrdOLeanLevel_ord(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_LeanIR_0__mkIRData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_LeanIR_0__mkIRData___closed__0 = (const lean_object*)&l___private_LeanIR_0__mkIRData___closed__0_value;
static const lean_array_object l___private_LeanIR_0__mkIRData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_LeanIR_0__mkIRData___closed__1 = (const lean_object*)&l___private_LeanIR_0__mkIRData___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "invalid trailing argument `"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__0 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__0_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`, expected argument of the form `-Dopt=val`"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__1 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__1_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-D"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__2 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__2_value;
static lean_once_cell_t l___private_LeanIR_0__setConfigOption___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanIR_0__setConfigOption___closed__3;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unknown option '"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__4 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__4_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__5 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__5_value;
static const lean_string_object l___private_LeanIR_0__setConfigOption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid -D parameter, argument must contain '='"};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__6 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__6_value;
static const lean_ctor_object l___private_LeanIR_0__setConfigOption___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_LeanIR_0__setConfigOption___closed__6_value)}};
static const lean_object* l___private_LeanIR_0__setConfigOption___closed__7 = (const lean_object*)&l___private_LeanIR_0__setConfigOption___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00main_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00main_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_main___lam__1___closed__0 = (const lean_object*)&l_main___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--stat"};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0;
static lean_once_cell_t l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "usage: leanir <setup.json> <output.ir> <output.c> [--stat] <-Dopt=val>..."};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_closure_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_closure_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static lean_once_cell_t l_main___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__3;
static lean_once_cell_t l_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__4;
static lean_once_cell_t l_main___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__5;
static lean_once_cell_t l_main___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__6;
static lean_once_cell_t l_main___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__7;
static lean_once_cell_t l_main___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__8;
static lean_once_cell_t l_main___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__9;
static const lean_ctor_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_ctor_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__11_value),LEAN_SCALAR_PTR_LITERAL(157, 0, 67, 166, 172, 92, 38, 85)}};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_string_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "C code generation"};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static lean_once_cell_t l_main___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__14;
static const lean_string_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "failed to create '"};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_string_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "LeanIR"};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_string_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static lean_once_cell_t l_main___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__19;
static const lean_string_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "import"};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static lean_once_cell_t l_main___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__21;
static lean_once_cell_t l_main___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__22;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
static const lean_ctor_object l_main___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__23_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_main___closed__24 = (const lean_object*)&l_main___closed__24_value;
static const lean_ctor_object l_main___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___closed__24_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_main___closed__25 = (const lean_object*)&l_main___closed__25_value;
static lean_once_cell_t l_main___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__26;
static lean_once_cell_t l_main___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__27;
static lean_once_cell_t l_main___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__28;
static lean_once_cell_t l_main___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__29;
static lean_once_cell_t l_main___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__30;
static lean_once_cell_t l_main___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_main___closed__31;
static const lean_array_object l_main___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__32 = (const lean_object*)&l_main___closed__32_value;
static const lean_array_object l_main___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__33 = (const lean_object*)&l_main___closed__33_value;
static const lean_string_object l_main___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "module '"};
static const lean_object* l_main___closed__34 = (const lean_object*)&l_main___closed__34_value;
static const lean_string_object l_main___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' not found"};
static const lean_object* l_main___closed__35 = (const lean_object*)&l_main___closed__35_value;
static lean_once_cell_t l_main___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_main___closed__36;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* l_main___boxed__const__2;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(lean_object* v_a_1_, lean_object* v_as_2_, size_t v_i_3_, size_t v_stop_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_eq(v_i_3_, v_stop_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_array_uget_borrowed(v_as_2_, v_i_3_);
v___x_7_ = lean_name_eq(v_a_1_, v___x_6_);
if (v___x_7_ == 0)
{
size_t v___x_8_; size_t v___x_9_; 
v___x_8_ = ((size_t)1ULL);
v___x_9_ = lean_usize_add(v_i_3_, v___x_8_);
v_i_3_ = v___x_9_;
goto _start;
}
else
{
return v___x_7_;
}
}
else
{
uint8_t v___x_11_; 
v___x_11_ = 0;
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1___boxed(lean_object* v_a_12_, lean_object* v_as_13_, lean_object* v_i_14_, lean_object* v_stop_15_){
_start:
{
size_t v_i_boxed_16_; size_t v_stop_boxed_17_; uint8_t v_res_18_; lean_object* v_r_19_; 
v_i_boxed_16_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_stop_boxed_17_ = lean_unbox_usize(v_stop_15_);
lean_dec(v_stop_15_);
v_res_18_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_12_, v_as_13_, v_i_boxed_16_, v_stop_boxed_17_);
lean_dec_ref(v_as_13_);
lean_dec(v_a_12_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(lean_object* v_as_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_array_get_size(v_as_20_);
v___x_24_ = lean_nat_dec_lt(v___x_22_, v___x_23_);
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
size_t v___x_25_; size_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = ((size_t)0ULL);
v___x_26_ = lean_usize_of_nat(v___x_23_);
v___x_27_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1_spec__1(v_a_21_, v_as_20_, v___x_25_, v___x_26_);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1___boxed(lean_object* v_as_28_, lean_object* v_a_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_as_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_as_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(lean_object* v_irExtNames_32_, lean_object* v_as_33_, size_t v_i_34_, size_t v_stop_35_, lean_object* v_b_36_){
_start:
{
lean_object* v___y_38_; uint8_t v___x_42_; 
v___x_42_ = lean_usize_dec_eq(v_i_34_, v_stop_35_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v_fst_44_; uint8_t v___x_45_; 
v___x_43_ = lean_array_uget_borrowed(v_as_33_, v_i_34_);
v_fst_44_ = lean_ctor_get(v___x_43_, 0);
v___x_45_ = l_Array_contains___at___00__private_LeanIR_0__mkIRData_spec__1(v_irExtNames_32_, v_fst_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_inc(v___x_43_);
v___x_46_ = lean_array_push(v_b_36_, v___x_43_);
v___y_38_ = v___x_46_;
goto v___jp_37_;
}
else
{
v___y_38_ = v_b_36_;
goto v___jp_37_;
}
}
else
{
return v_b_36_;
}
v___jp_37_:
{
size_t v___x_39_; size_t v___x_40_; 
v___x_39_ = ((size_t)1ULL);
v___x_40_ = lean_usize_add(v_i_34_, v___x_39_);
v_i_34_ = v___x_40_;
v_b_36_ = v___y_38_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2___boxed(lean_object* v_irExtNames_47_, lean_object* v_as_48_, lean_object* v_i_49_, lean_object* v_stop_50_, lean_object* v_b_51_){
_start:
{
size_t v_i_boxed_52_; size_t v_stop_boxed_53_; lean_object* v_res_54_; 
v_i_boxed_52_ = lean_unbox_usize(v_i_49_);
lean_dec(v_i_49_);
v_stop_boxed_53_ = lean_unbox_usize(v_stop_50_);
lean_dec(v_stop_50_);
v_res_54_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_47_, v_as_48_, v_i_boxed_52_, v_stop_boxed_53_, v_b_51_);
lean_dec_ref(v_as_48_);
lean_dec_ref(v_irExtNames_47_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(size_t v_sz_55_, size_t v_i_56_, lean_object* v_bs_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_usize_dec_lt(v_i_56_, v_sz_55_);
if (v___x_58_ == 0)
{
return v_bs_57_;
}
else
{
lean_object* v_v_59_; lean_object* v_fst_60_; lean_object* v___x_61_; lean_object* v_bs_x27_62_; size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; 
v_v_59_ = lean_array_uget_borrowed(v_bs_57_, v_i_56_);
v_fst_60_ = lean_ctor_get(v_v_59_, 0);
lean_inc(v_fst_60_);
v___x_61_ = lean_unsigned_to_nat(0u);
v_bs_x27_62_ = lean_array_uset(v_bs_57_, v_i_56_, v___x_61_);
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_add(v_i_56_, v___x_63_);
v___x_65_ = lean_array_uset(v_bs_x27_62_, v_i_56_, v_fst_60_);
v_i_56_ = v___x_64_;
v_bs_57_ = v___x_65_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0___boxed(lean_object* v_sz_67_, lean_object* v_i_68_, lean_object* v_bs_69_){
_start:
{
size_t v_sz_boxed_70_; size_t v_i_boxed_71_; lean_object* v_res_72_; 
v_sz_boxed_70_ = lean_unbox_usize(v_sz_67_);
lean_dec(v_sz_67_);
v_i_boxed_71_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_res_72_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_boxed_70_, v_i_boxed_71_, v_bs_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData(lean_object* v_env_77_){
_start:
{
lean_object* v_irEntries_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_inc_ref_n(v_env_77_, 2);
v_irEntries_79_ = lean_ir_export_entries(v_env_77_);
v___x_80_ = 2;
v___x_81_ = lean_box(0);
v___x_82_ = l_Lean_mkModuleData(v_env_77_, v___x_80_, v___x_81_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_113_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_113_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_113_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_113_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___y_88_; lean_object* v_entries_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_entries_100_ = lean_ctor_get(v_a_83_, 4);
lean_inc_ref(v_entries_100_);
lean_dec(v_a_83_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_array_get_size(v_entries_100_);
v___x_103_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__1));
v___x_104_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_104_ == 0)
{
lean_dec_ref(v_entries_100_);
v___y_88_ = v___x_103_;
goto v___jp_87_;
}
else
{
size_t v_sz_105_; size_t v___x_106_; lean_object* v_irExtNames_107_; uint8_t v___x_108_; 
v_sz_105_ = lean_array_size(v_irEntries_79_);
v___x_106_ = ((size_t)0ULL);
lean_inc_ref(v_irEntries_79_);
v_irExtNames_107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_LeanIR_0__mkIRData_spec__0(v_sz_105_, v___x_106_, v_irEntries_79_);
v___x_108_ = lean_nat_dec_le(v___x_102_, v___x_102_);
if (v___x_108_ == 0)
{
if (v___x_104_ == 0)
{
lean_dec_ref(v_irExtNames_107_);
lean_dec_ref(v_entries_100_);
v___y_88_ = v___x_103_;
goto v___jp_87_;
}
else
{
size_t v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_usize_of_nat(v___x_102_);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_107_, v_entries_100_, v___x_106_, v___x_109_, v___x_103_);
lean_dec_ref(v_entries_100_);
lean_dec_ref(v_irExtNames_107_);
v___y_88_ = v___x_110_;
goto v___jp_87_;
}
}
else
{
size_t v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_usize_of_nat(v___x_102_);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_LeanIR_0__mkIRData_spec__2(v_irExtNames_107_, v_entries_100_, v___x_106_, v___x_111_, v___x_103_);
lean_dec_ref(v_entries_100_);
lean_dec_ref(v_irExtNames_107_);
v___y_88_ = v___x_112_;
goto v___jp_87_;
}
}
v___jp_87_:
{
lean_object* v___x_89_; uint8_t v_isModule_90_; lean_object* v_imports_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_89_ = l_Lean_Environment_header(v_env_77_);
v_isModule_90_ = lean_ctor_get_uint8(v___x_89_, sizeof(void*)*7 + 4);
v_imports_91_ = lean_ctor_get(v___x_89_, 1);
lean_inc_ref(v_imports_91_);
lean_dec_ref(v___x_89_);
v___x_92_ = ((lean_object*)(l___private_LeanIR_0__mkIRData___closed__0));
v___x_93_ = 1;
v___x_94_ = lean_get_ir_extra_const_names(v_env_77_, v___x_80_, v___x_93_);
v___x_95_ = l_Array_append___redArg(v_irEntries_79_, v___y_88_);
lean_dec_ref(v___y_88_);
v___x_96_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_96_, 0, v_imports_91_);
lean_ctor_set(v___x_96_, 1, v___x_92_);
lean_ctor_set(v___x_96_, 2, v___x_92_);
lean_ctor_set(v___x_96_, 3, v___x_94_);
lean_ctor_set(v___x_96_, 4, v___x_95_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*5, v_isModule_90_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_96_);
v___x_98_ = v___x_85_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_dec_ref(v_irEntries_79_);
lean_dec_ref(v_env_77_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__mkIRData___boxed(lean_object* v_env_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_LeanIR_0__mkIRData(v_env_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(lean_object* v_arg_117_, lean_object* v___x_118_, lean_object* v_arg_119_, lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
lean_object* v_startInclusive_122_; lean_object* v_endExclusive_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_startInclusive_122_ = lean_ctor_get(v_arg_117_, 1);
v_endExclusive_123_ = lean_ctor_get(v_arg_117_, 2);
v___x_124_ = lean_nat_sub(v_endExclusive_123_, v_startInclusive_122_);
v___x_125_ = lean_nat_dec_eq(v_a_120_, v___x_124_);
lean_dec(v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint32_t v___x_127_; uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_126_ = lean_nat_add(v___x_118_, v_a_120_);
v___x_127_ = lean_string_utf8_get_fast(v_arg_119_, v___x_126_);
v___x_128_ = 61;
v___x_129_ = lean_uint32_dec_eq(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_a_120_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_string_utf8_next_fast(v_arg_119_, v___x_126_);
lean_dec(v___x_126_);
v___x_132_ = lean_nat_sub(v___x_131_, v___x_118_);
v_a_120_ = v___x_132_;
v_b_121_ = v___x_130_;
goto _start;
}
else
{
lean_object* v___x_134_; 
lean_dec(v___x_126_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_a_120_);
return v___x_134_;
}
}
else
{
lean_dec(v_a_120_);
lean_inc(v_b_121_);
return v_b_121_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg___boxed(lean_object* v_arg_135_, lean_object* v___x_136_, lean_object* v_arg_137_, lean_object* v_a_138_, lean_object* v_b_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_135_, v___x_136_, v_arg_137_, v_a_138_, v_b_139_);
lean_dec(v_b_139_);
lean_dec_ref(v_arg_137_);
lean_dec(v___x_136_);
lean_dec_ref(v_arg_135_);
return v_res_140_;
}
}
static lean_object* _init_l___private_LeanIR_0__setConfigOption___closed__3(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__2));
v___x_145_ = lean_string_utf8_byte_size(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption(lean_object* v_opts_151_, lean_object* v_arg_152_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_161_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__2));
v___x_162_ = lean_string_utf8_byte_size(v_arg_152_);
v___x_163_ = lean_obj_once(&l___private_LeanIR_0__setConfigOption___closed__3, &l___private_LeanIR_0__setConfigOption___closed__3_once, _init_l___private_LeanIR_0__setConfigOption___closed__3);
v___x_164_ = lean_nat_dec_le(v___x_163_, v___x_162_);
if (v___x_164_ == 0)
{
lean_dec_ref(v_opts_151_);
goto v___jp_154_;
}
else
{
lean_object* v_searcher_165_; uint8_t v___x_166_; 
v_searcher_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_string_memcmp(v_arg_152_, v___x_161_, v_searcher_165_, v_searcher_165_, v___x_163_);
if (v___x_166_ == 0)
{
lean_dec_ref(v_opts_151_);
goto v___jp_154_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___y_171_; lean_object* v_arg_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_167_ = lean_unsigned_to_nat(2u);
lean_inc_ref_n(v_arg_152_, 2);
v___x_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_168_, 0, v_arg_152_);
lean_ctor_set(v___x_168_, 1, v_searcher_165_);
lean_ctor_set(v___x_168_, 2, v___x_162_);
v___x_169_ = l_String_Slice_Pos_nextn(v___x_168_, v_searcher_165_, v___x_167_);
lean_dec_ref(v___x_168_);
lean_inc(v___x_169_);
v_arg_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_arg_209_, 0, v_arg_152_);
lean_ctor_set(v_arg_209_, 1, v___x_169_);
lean_ctor_set(v_arg_209_, 2, v___x_162_);
v___x_210_ = lean_box(0);
v___x_211_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_209_, v___x_169_, v_arg_152_, v_searcher_165_, v___x_210_);
lean_dec_ref(v_arg_209_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_nat_sub(v___x_162_, v___x_169_);
v___y_171_ = v___x_212_;
goto v___jp_170_;
}
else
{
lean_object* v_val_213_; 
v_val_213_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_213_);
lean_dec_ref(v___x_211_);
v___y_171_ = v_val_213_;
goto v___jp_170_;
}
v___jp_170_:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_nat_sub(v___x_162_, v___x_169_);
v___x_173_ = lean_nat_dec_eq(v___y_171_, v___x_172_);
lean_dec(v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_getOptionDecls();
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_198_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_198_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_198_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_198_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_name_181_; lean_object* v___x_182_; 
v___x_179_ = lean_nat_add(v___x_169_, v___y_171_);
lean_dec(v___y_171_);
lean_inc(v___x_179_);
lean_inc(v___x_169_);
lean_inc_ref(v_arg_152_);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v_arg_152_);
lean_ctor_set(v___x_180_, 1, v___x_169_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
v_name_181_ = l_String_Slice_toName(v___x_180_);
lean_dec_ref(v___x_180_);
v___x_182_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_175_, v_name_181_);
lean_dec(v_a_175_);
if (lean_obj_tag(v___x_182_) == 1)
{
lean_object* v_val_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_val_187_; lean_object* v___x_188_; 
lean_del_object(v___x_177_);
v_val_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_val_183_);
lean_dec_ref(v___x_182_);
v___x_184_ = lean_string_utf8_next_fast(v_arg_152_, v___x_179_);
lean_dec(v___x_179_);
v___x_185_ = lean_nat_sub(v___x_184_, v___x_169_);
v___x_186_ = lean_nat_add(v___x_169_, v___x_185_);
lean_dec(v___x_185_);
lean_dec(v___x_169_);
v_val_187_ = lean_string_utf8_extract(v_arg_152_, v___x_186_, v___x_162_);
lean_dec(v___x_186_);
lean_dec_ref(v_arg_152_);
v___x_188_ = l_Lean_Language_Lean_setOption(v_opts_151_, v_val_183_, v_name_181_, v_val_187_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec(v___x_182_);
lean_dec(v___x_179_);
lean_dec(v___x_169_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_opts_151_);
v___x_189_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__4));
v___x_190_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_181_, v___x_166_);
v___x_191_ = lean_string_append(v___x_189_, v___x_190_);
lean_dec_ref(v___x_190_);
v___x_192_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_193_ = lean_string_append(v___x_191_, v___x_192_);
v___x_194_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
if (v_isShared_178_ == 0)
{
lean_ctor_set_tag(v___x_177_, 1);
lean_ctor_set(v___x_177_, 0, v___x_194_);
v___x_196_ = v___x_177_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v___y_171_);
lean_dec(v___x_169_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_opts_151_);
v_a_199_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_174_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_174_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v___y_171_);
lean_dec(v___x_169_);
lean_dec_ref(v_arg_152_);
lean_dec_ref(v_opts_151_);
v___x_207_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__7));
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
}
}
v___jp_154_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__0));
v___x_156_ = lean_string_append(v___x_155_, v_arg_152_);
lean_dec_ref(v_arg_152_);
v___x_157_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__1));
v___x_158_ = lean_string_append(v___x_156_, v___x_157_);
v___x_159_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanIR_0__setConfigOption___boxed(lean_object* v_opts_214_, lean_object* v_arg_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_LeanIR_0__setConfigOption(v_opts_214_, v_arg_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(lean_object* v_arg_218_, lean_object* v___x_219_, lean_object* v_arg_220_, lean_object* v_inst_221_, lean_object* v_R_222_, lean_object* v_a_223_, lean_object* v_b_224_, lean_object* v_c_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___redArg(v_arg_218_, v___x_219_, v_arg_220_, v_a_223_, v_b_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0___boxed(lean_object* v_arg_227_, lean_object* v___x_228_, lean_object* v_arg_229_, lean_object* v_inst_230_, lean_object* v_R_231_, lean_object* v_a_232_, lean_object* v_b_233_, lean_object* v_c_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_WellFounded_opaqueFix_u2083___at___00__private_LeanIR_0__setConfigOption_spec__0(v_arg_227_, v___x_228_, v_arg_229_, v_inst_230_, v_R_231_, v_a_232_, v_b_233_, v_c_234_);
lean_dec(v_b_233_);
lean_dec_ref(v_arg_229_);
lean_dec(v___x_228_);
lean_dec_ref(v_arg_227_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg(lean_object* v___x_236_, lean_object* v_inst_237_, lean_object* v_ext_238_, lean_object* v_env_239_){
_start:
{
lean_object* v_toEnvExtension_241_; lean_object* v_addImportedFn_242_; lean_object* v_asyncMode_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_importedEntries_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_274_; 
v_toEnvExtension_241_ = lean_ctor_get(v_ext_238_, 0);
lean_inc_ref(v_toEnvExtension_241_);
v_addImportedFn_242_ = lean_ctor_get(v_ext_238_, 2);
lean_inc_ref(v_addImportedFn_242_);
lean_dec_ref(v_ext_238_);
v_asyncMode_243_ = lean_ctor_get(v_toEnvExtension_241_, 2);
v___x_244_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v_inst_237_);
lean_inc_ref(v_env_239_);
v___x_245_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_244_, v_toEnvExtension_241_, v_env_239_, v_asyncMode_243_, v___x_236_);
lean_dec_ref(v___x_244_);
v_importedEntries_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v___x_245_, 1);
lean_dec(v_unused_275_);
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_274_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_importedEntries_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_274_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = l_Lean_Options_empty;
lean_inc_ref(v_env_239_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_env_239_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_inc_ref(v_importedEntries_246_);
v___x_252_ = lean_apply_3(v_addImportedFn_242_, v_importedEntries_246_, v___x_251_, lean_box(0));
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_265_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_265_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_265_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_265_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_a_253_);
v___x_258_ = v___x_248_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_importedEntries_246_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_a_253_);
v___x_258_ = v_reuseFailAlloc_264_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_box(0);
v___x_260_ = l_Lean_EnvExtension_setState___redArg(v_toEnvExtension_241_, v_env_239_, v___x_258_, v___x_259_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_260_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_del_object(v___x_248_);
lean_dec_ref(v_importedEntries_246_);
lean_dec_ref(v_toEnvExtension_241_);
lean_dec_ref(v_env_239_);
v_a_266_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_252_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_252_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___elam__0___redArg___boxed(lean_object* v___x_276_, lean_object* v_inst_277_, lean_object* v_ext_278_, lean_object* v_env_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_main___elam__0___redArg(v___x_276_, v_inst_277_, v_ext_278_, v_env_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0(lean_object* v___x_282_, lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_00_u03c3_285_, lean_object* v_inst_286_, lean_object* v_ext_287_, lean_object* v_env_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_main___elam__0___redArg(v___x_282_, v_inst_286_, v_ext_287_, v_env_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_main___elam__0___boxed(lean_object* v___x_291_, lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_00_u03c3_294_, lean_object* v_inst_295_, lean_object* v_ext_296_, lean_object* v_env_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_main___elam__0(v___x_291_, v_00_u03b1_292_, v_00_u03b2_293_, v_00_u03c3_294_, v_inst_295_, v_ext_296_, v_env_297_);
return v_res_299_;
}
}
static lean_object* _init_l_panic___at___00main_spec__5___closed__0(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_instInhabitedError;
v___x_301_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_301_, 0, lean_box(0));
lean_closure_set(v___x_301_, 1, lean_box(0));
lean_closure_set(v___x_301_, 2, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5(lean_object* v_msg_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_20091__overap_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_panic___at___00main_spec__5___closed__0, &l_panic___at___00main_spec__5___closed__0_once, _init_l_panic___at___00main_spec__5___closed__0);
v___x_20091__overap_305_ = lean_panic_fn_borrowed(v___x_304_, v_msg_302_);
v___x_306_ = lean_apply_1(v___x_20091__overap_305_, lean_box(0));
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00main_spec__5___boxed(lean_object* v_msg_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_panic___at___00main_spec__5(v_msg_307_);
return v_res_309_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00main_spec__8(lean_object* v_opts_310_, lean_object* v_opt_311_){
_start:
{
lean_object* v_name_312_; lean_object* v_defValue_313_; lean_object* v_map_314_; lean_object* v___x_315_; 
v_name_312_ = lean_ctor_get(v_opt_311_, 0);
v_defValue_313_ = lean_ctor_get(v_opt_311_, 1);
v_map_314_ = lean_ctor_get(v_opts_310_, 0);
v___x_315_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_314_, v_name_312_);
if (lean_obj_tag(v___x_315_) == 0)
{
uint8_t v___x_316_; 
v___x_316_ = lean_unbox(v_defValue_313_);
return v___x_316_;
}
else
{
lean_object* v_val_317_; 
v_val_317_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v___x_315_);
if (lean_obj_tag(v_val_317_) == 1)
{
uint8_t v_v_318_; 
v_v_318_ = lean_ctor_get_uint8(v_val_317_, 0);
lean_dec_ref(v_val_317_);
return v_v_318_;
}
else
{
uint8_t v___x_319_; 
lean_dec(v_val_317_);
v___x_319_ = lean_unbox(v_defValue_313_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__8___boxed(lean_object* v_opts_320_, lean_object* v_opt_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Lean_Option_get___at___00main_spec__8(v_opts_320_, v_opt_321_);
lean_dec_ref(v_opt_321_);
lean_dec_ref(v_opts_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9(lean_object* v_opts_324_, lean_object* v_opt_325_){
_start:
{
lean_object* v_name_326_; lean_object* v_defValue_327_; lean_object* v_map_328_; lean_object* v___x_329_; 
v_name_326_ = lean_ctor_get(v_opt_325_, 0);
v_defValue_327_ = lean_ctor_get(v_opt_325_, 1);
v_map_328_ = lean_ctor_get(v_opts_324_, 0);
v___x_329_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_328_, v_name_326_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_inc(v_defValue_327_);
return v_defValue_327_;
}
else
{
lean_object* v_val_330_; 
v_val_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_330_);
lean_dec_ref(v___x_329_);
if (lean_obj_tag(v_val_330_) == 3)
{
lean_object* v_v_331_; 
v_v_331_ = lean_ctor_get(v_val_330_, 0);
lean_inc(v_v_331_);
lean_dec_ref(v_val_330_);
return v_v_331_;
}
else
{
lean_dec(v_val_330_);
lean_inc(v_defValue_327_);
return v_defValue_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00main_spec__9___boxed(lean_object* v_opts_332_, lean_object* v_opt_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Option_get___at___00main_spec__9(v_opts_332_, v_opt_333_);
lean_dec_ref(v_opt_333_);
lean_dec_ref(v_opts_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(lean_object* v___x_335_, lean_object* v_a_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_dec(v_a_336_);
return v_x_337_;
}
else
{
lean_object* v_key_338_; lean_object* v_value_339_; lean_object* v_tail_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_387_; 
v_key_338_ = lean_ctor_get(v_x_337_, 0);
v_value_339_ = lean_ctor_get(v_x_337_, 1);
v_tail_340_ = lean_ctor_get(v_x_337_, 2);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_387_ == 0)
{
v___x_342_ = v_x_337_;
v_isShared_343_ = v_isSharedCheck_387_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_tail_340_);
lean_inc(v_value_339_);
lean_inc(v_key_338_);
lean_dec(v_x_337_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_387_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v___x_344_; 
v___x_344_ = lean_name_eq(v_key_338_, v_a_336_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_335_, v_a_336_, v_tail_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 2, v___x_345_);
v___x_347_ = v___x_342_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_key_338_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_value_339_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v_toEffectiveImport_349_; lean_object* v_toImport_350_; lean_object* v_parts_351_; lean_object* v_irData_x3f_352_; uint8_t v_needsIRTrans_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_key_338_);
v_toEffectiveImport_349_ = lean_ctor_get(v_value_339_, 0);
lean_inc_ref(v_toEffectiveImport_349_);
v_toImport_350_ = lean_ctor_get(v_toEffectiveImport_349_, 0);
lean_inc_ref(v_toImport_350_);
v_parts_351_ = lean_ctor_get(v_value_339_, 1);
v_irData_x3f_352_ = lean_ctor_get(v_value_339_, 2);
v_needsIRTrans_353_ = lean_ctor_get_uint8(v_value_339_, sizeof(void*)*3);
v_isSharedCheck_385_ = !lean_is_exclusive(v_value_339_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_value_339_, 0);
lean_dec(v_unused_386_);
v___x_355_ = v_value_339_;
v_isShared_356_ = v_isSharedCheck_385_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_irData_x3f_352_);
lean_inc(v_parts_351_);
lean_dec(v_value_339_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_385_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
uint8_t v_hasData_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_383_; 
v_hasData_357_ = lean_ctor_get_uint8(v_toEffectiveImport_349_, sizeof(void*)*1 + 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_toEffectiveImport_349_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_toEffectiveImport_349_, 0);
lean_dec(v_unused_384_);
v___x_359_ = v_toEffectiveImport_349_;
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
else
{
lean_dec(v_toEffectiveImport_349_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v_module_361_; uint8_t v___x_362_; 
v_module_361_ = lean_ctor_get(v_toImport_350_, 0);
v___x_362_ = lean_name_eq(v_module_361_, v___x_335_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; lean_object* v___x_365_; 
v___x_363_ = 2;
if (v_isShared_360_ == 0)
{
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_toImport_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*1 + 1, v_hasData_357_);
v___x_365_ = v_reuseFailAlloc_372_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_363_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_365_);
v___x_367_ = v___x_355_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_parts_351_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_irData_x3f_352_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*3, v_needsIRTrans_353_);
v___x_367_ = v_reuseFailAlloc_371_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_369_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_367_);
lean_ctor_set(v___x_342_, 0, v_a_336_);
v___x_369_ = v___x_342_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_tail_340_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
uint8_t v___x_373_; lean_object* v___x_375_; 
v___x_373_ = 0;
if (v_isShared_360_ == 0)
{
v___x_375_ = v___x_359_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_toImport_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_382_, sizeof(void*)*1 + 1, v_hasData_357_);
v___x_375_ = v_reuseFailAlloc_382_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_373_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_375_);
v___x_377_ = v___x_355_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_parts_351_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_irData_x3f_352_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*3, v_needsIRTrans_353_);
v___x_377_ = v_reuseFailAlloc_381_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_379_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_377_);
lean_ctor_set(v___x_342_, 0, v_a_336_);
v___x_379_ = v___x_342_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_tail_340_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5___boxed(lean_object* v___x_388_, lean_object* v_a_389_, lean_object* v_x_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_388_, v_a_389_, v_x_390_);
lean_dec(v___x_388_);
return v_res_391_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0(void){
_start:
{
lean_object* v___x_392_; uint64_t v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1723u);
v___x_393_ = lean_uint64_of_nat(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(lean_object* v___x_394_, lean_object* v_m_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_size_397_; lean_object* v_buckets_398_; lean_object* v___x_399_; uint64_t v___y_401_; 
v_size_397_ = lean_ctor_get(v_m_395_, 0);
v_buckets_398_ = lean_ctor_get(v_m_395_, 1);
v___x_399_ = lean_array_get_size(v_buckets_398_);
if (lean_obj_tag(v_a_396_) == 0)
{
uint64_t v___x_428_; 
v___x_428_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___closed__0);
v___y_401_ = v___x_428_;
goto v___jp_400_;
}
else
{
uint64_t v_hash_429_; 
v_hash_429_ = lean_ctor_get_uint64(v_a_396_, sizeof(void*)*2);
v___y_401_ = v_hash_429_;
goto v___jp_400_;
}
v___jp_400_:
{
uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v_fold_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v_bucket_413_; uint8_t v___x_414_; 
v___x_402_ = 32ULL;
v___x_403_ = lean_uint64_shift_right(v___y_401_, v___x_402_);
v_fold_404_ = lean_uint64_xor(v___y_401_, v___x_403_);
v___x_405_ = 16ULL;
v___x_406_ = lean_uint64_shift_right(v_fold_404_, v___x_405_);
v___x_407_ = lean_uint64_xor(v_fold_404_, v___x_406_);
v___x_408_ = lean_uint64_to_usize(v___x_407_);
v___x_409_ = lean_usize_of_nat(v___x_399_);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_sub(v___x_409_, v___x_410_);
v___x_412_ = lean_usize_land(v___x_408_, v___x_411_);
v_bucket_413_ = lean_array_uget_borrowed(v_buckets_398_, v___x_412_);
v___x_414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_396_, v_bucket_413_);
if (v___x_414_ == 0)
{
lean_dec(v_a_396_);
return v_m_395_;
}
else
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_425_; 
lean_inc(v_bucket_413_);
lean_inc_ref(v_buckets_398_);
lean_inc(v_size_397_);
v_isSharedCheck_425_ = !lean_is_exclusive(v_m_395_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; lean_object* v_unused_427_; 
v_unused_426_ = lean_ctor_get(v_m_395_, 1);
lean_dec(v_unused_426_);
v_unused_427_ = lean_ctor_get(v_m_395_, 0);
lean_dec(v_unused_427_);
v___x_416_ = v_m_395_;
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
else
{
lean_dec(v_m_395_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v_buckets_419_; lean_object* v_bucket_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_418_ = lean_box(0);
v_buckets_419_ = lean_array_uset(v_buckets_398_, v___x_412_, v___x_418_);
v_bucket_420_ = l_Std_DHashMap_Internal_AssocList_Const_modify___at___00Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4_spec__5(v___x_394_, v_a_396_, v_bucket_413_);
v___x_421_ = lean_array_uset(v_buckets_419_, v___x_412_, v_bucket_420_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_421_);
v___x_423_ = v___x_416_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_size_397_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4___boxed(lean_object* v___x_430_, lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v___x_430_, v_m_431_, v_a_432_);
lean_dec(v___x_430_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v___x_434_, lean_object* v___x_435_, uint8_t v___x_436_, lean_object* v___x_437_, uint8_t v___y_438_, lean_object* v_name_439_, lean_object* v___x_440_, uint8_t v___x_441_, uint8_t v___x_442_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_st_mk_ref(v___x_434_);
v___x_445_ = l_Lean_importModulesCore(v___x_435_, v___x_436_, v___x_437_, v___y_438_, v___x_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; lean_object* v_moduleNameMap_447_; lean_object* v_moduleNames_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref(v___x_445_);
v___x_446_ = lean_st_ref_get(v___x_444_);
lean_dec(v___x_444_);
v_moduleNameMap_447_ = lean_ctor_get(v___x_446_, 0);
v_moduleNames_448_ = lean_ctor_get(v___x_446_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_461_ == 0)
{
v___x_450_ = v___x_446_;
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_moduleNames_448_);
lean_inc(v_moduleNameMap_447_);
lean_dec(v___x_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_461_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
lean_inc(v_name_439_);
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___at___00main_spec__4(v_name_439_, v_moduleNameMap_447_, v_name_439_);
lean_dec(v_name_439_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_moduleNames_448_);
v___x_454_ = v_reuseFailAlloc_460_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
uint32_t v___x_455_; uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_455_ = 0;
v___x_456_ = 0;
v___x_457_ = l_Lean_instDecidableEqOLeanLevel(v___x_456_, v___x_436_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_finalizeImport(v___x_454_, v___x_435_, v___x_440_, v___x_455_, v___x_441_, v___x_442_, v___x_456_, v___x_441_);
lean_dec_ref(v___x_454_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_finalizeImport(v___x_454_, v___x_435_, v___x_440_, v___x_455_, v___x_441_, v___x_442_, v___x_456_, v___x_442_);
lean_dec_ref(v___x_454_);
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v___x_444_);
lean_dec_ref(v___x_440_);
lean_dec(v_name_439_);
lean_dec_ref(v___x_435_);
v_a_462_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_445_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_445_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
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
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v___y_474_, lean_object* v_name_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v___y_479_){
_start:
{
uint8_t v___x_36305__boxed_480_; uint8_t v___y_36307__boxed_481_; uint8_t v___x_36309__boxed_482_; uint8_t v___x_36310__boxed_483_; lean_object* v_res_484_; 
v___x_36305__boxed_480_ = lean_unbox(v___x_472_);
v___y_36307__boxed_481_ = lean_unbox(v___y_474_);
v___x_36309__boxed_482_ = lean_unbox(v___x_477_);
v___x_36310__boxed_483_ = lean_unbox(v___x_478_);
v_res_484_ = l_main___lam__0(v___x_470_, v___x_471_, v___x_36305__boxed_480_, v___x_473_, v___y_36307__boxed_481_, v_name_475_, v___x_476_, v___x_36309__boxed_482_, v___x_36310__boxed_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_main___lam__1(lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v___x_488_, lean_object* v_name_489_, lean_object* v_a_490_, lean_object* v___x_491_, lean_object* v_head_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v___x_499_, lean_object* v___x_500_, uint8_t v___x_501_, uint8_t v___x_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_env_508_; lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v_fileName_512_; lean_object* v_fileMap_513_; lean_object* v_currRecDepth_514_; lean_object* v_ref_515_; lean_object* v_currNamespace_516_; lean_object* v_openDecls_517_; lean_object* v_initHeartbeats_518_; lean_object* v_maxHeartbeats_519_; lean_object* v_quotContext_520_; lean_object* v_currMacroScope_521_; lean_object* v_cancelTk_x3f_522_; uint8_t v_suppressElabErrors_523_; lean_object* v_inheritedTraceOptions_524_; lean_object* v___y_525_; uint8_t v___y_554_; uint8_t v___x_574_; 
v___x_504_ = lean_io_get_num_heartbeats();
v___x_505_ = lean_st_mk_ref(v___x_486_);
v___x_506_ = lean_st_ref_get(v___x_487_);
v___x_507_ = lean_st_ref_get(v___x_505_);
v_env_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_ref(v_env_508_);
lean_dec(v___x_507_);
v___x_509_ = l_Lean_diagnostics;
v___x_510_ = l_Lean_Option_get___at___00main_spec__8(v___x_488_, v___x_509_);
v___x_574_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_508_);
lean_dec_ref(v_env_508_);
if (v___x_574_ == 0)
{
if (v___x_510_ == 0)
{
v___y_554_ = v___x_502_;
goto v___jp_553_;
}
else
{
v___y_554_ = v___x_574_;
goto v___jp_553_;
}
}
else
{
v___y_554_ = v___x_510_;
goto v___jp_553_;
}
v___jp_511_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = l_Lean_maxRecDepth;
v___x_527_ = l_Lean_Option_get___at___00main_spec__9(v___x_488_, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_528_, 0, v_fileName_512_);
lean_ctor_set(v___x_528_, 1, v_fileMap_513_);
lean_ctor_set(v___x_528_, 2, v___x_488_);
lean_ctor_set(v___x_528_, 3, v_currRecDepth_514_);
lean_ctor_set(v___x_528_, 4, v___x_527_);
lean_ctor_set(v___x_528_, 5, v_ref_515_);
lean_ctor_set(v___x_528_, 6, v_currNamespace_516_);
lean_ctor_set(v___x_528_, 7, v_openDecls_517_);
lean_ctor_set(v___x_528_, 8, v_initHeartbeats_518_);
lean_ctor_set(v___x_528_, 9, v_maxHeartbeats_519_);
lean_ctor_set(v___x_528_, 10, v_quotContext_520_);
lean_ctor_set(v___x_528_, 11, v_currMacroScope_521_);
lean_ctor_set(v___x_528_, 12, v_cancelTk_x3f_522_);
lean_ctor_set(v___x_528_, 13, v_inheritedTraceOptions_524_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*14, v___x_510_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*14 + 1, v_suppressElabErrors_523_);
v___x_529_ = l_Lean_Compiler_LCNF_emitC(v_name_489_, v___x_528_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___x_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref(v___x_529_);
v___x_531_ = lean_st_ref_get(v___x_505_);
lean_dec(v___x_505_);
lean_dec(v___x_531_);
v___x_532_ = lean_string_to_utf8(v_a_530_);
lean_dec(v_a_530_);
v___x_533_ = lean_io_prim_handle_write(v_a_490_, v___x_532_);
lean_dec_ref(v___x_532_);
return v___x_533_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_552_; 
lean_dec(v___x_505_);
v_a_534_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_552_ == 0)
{
v___x_536_ = v___x_529_;
v_isShared_537_ = v_isSharedCheck_552_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_529_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_552_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
if (lean_obj_tag(v_a_534_) == 0)
{
lean_object* v_msg_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v_msg_538_ = lean_ctor_get(v_a_534_, 1);
lean_inc_ref(v_msg_538_);
lean_dec_ref(v_a_534_);
v___x_539_ = l_Lean_MessageData_toString(v_msg_538_);
v___x_540_ = lean_mk_io_user_error(v___x_539_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_540_);
v___x_542_ = v___x_536_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v_id_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v_id_544_ = lean_ctor_get(v_a_534_, 0);
lean_inc(v_id_544_);
lean_dec_ref(v_a_534_);
v___x_545_ = ((lean_object*)(l_main___lam__1___closed__0));
v___x_546_ = l_Nat_reprFast(v_id_544_);
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = lean_mk_io_user_error(v___x_547_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_548_);
v___x_550_ = v___x_536_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
v___jp_553_:
{
if (v___y_554_ == 0)
{
lean_object* v___x_555_; lean_object* v_env_556_; lean_object* v_nextMacroScope_557_; lean_object* v_ngen_558_; lean_object* v_auxDeclNGen_559_; lean_object* v_traceState_560_; lean_object* v_messages_561_; lean_object* v_infoState_562_; lean_object* v_snapshotTasks_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
v___x_555_ = lean_st_ref_take(v___x_505_);
v_env_556_ = lean_ctor_get(v___x_555_, 0);
v_nextMacroScope_557_ = lean_ctor_get(v___x_555_, 1);
v_ngen_558_ = lean_ctor_get(v___x_555_, 2);
v_auxDeclNGen_559_ = lean_ctor_get(v___x_555_, 3);
v_traceState_560_ = lean_ctor_get(v___x_555_, 4);
v_messages_561_ = lean_ctor_get(v___x_555_, 6);
v_infoState_562_ = lean_ctor_get(v___x_555_, 7);
v_snapshotTasks_563_ = lean_ctor_get(v___x_555_, 8);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_555_, 5);
lean_dec(v_unused_573_);
v___x_565_ = v___x_555_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snapshotTasks_563_);
lean_inc(v_infoState_562_);
lean_inc(v_messages_561_);
lean_inc(v_traceState_560_);
lean_inc(v_auxDeclNGen_559_);
lean_inc(v_ngen_558_);
lean_inc(v_nextMacroScope_557_);
lean_inc(v_env_556_);
lean_dec(v___x_555_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = l_Lean_Kernel_enableDiag(v_env_556_, v___x_510_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 5, v___x_491_);
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_nextMacroScope_557_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_ngen_558_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_auxDeclNGen_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_traceState_560_);
lean_ctor_set(v_reuseFailAlloc_571_, 5, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_571_, 6, v_messages_561_);
lean_ctor_set(v_reuseFailAlloc_571_, 7, v_infoState_562_);
lean_ctor_set(v_reuseFailAlloc_571_, 8, v_snapshotTasks_563_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; 
v___x_570_ = lean_st_ref_set(v___x_505_, v___x_569_);
lean_inc(v___x_505_);
lean_inc(v___x_496_);
v_fileName_512_ = v_head_492_;
v_fileMap_513_ = v___x_493_;
v_currRecDepth_514_ = v___x_494_;
v_ref_515_ = v___x_495_;
v_currNamespace_516_ = v___x_496_;
v_openDecls_517_ = v___x_497_;
v_initHeartbeats_518_ = v___x_504_;
v_maxHeartbeats_519_ = v___x_498_;
v_quotContext_520_ = v___x_496_;
v_currMacroScope_521_ = v___x_499_;
v_cancelTk_x3f_522_ = v___x_500_;
v_suppressElabErrors_523_ = v___x_501_;
v_inheritedTraceOptions_524_ = v___x_506_;
v___y_525_ = v___x_505_;
goto v___jp_511_;
}
}
}
else
{
lean_dec_ref(v___x_491_);
lean_inc(v___x_505_);
lean_inc(v___x_496_);
v_fileName_512_ = v_head_492_;
v_fileMap_513_ = v___x_493_;
v_currRecDepth_514_ = v___x_494_;
v_ref_515_ = v___x_495_;
v_currNamespace_516_ = v___x_496_;
v_openDecls_517_ = v___x_497_;
v_initHeartbeats_518_ = v___x_504_;
v_maxHeartbeats_519_ = v___x_498_;
v_quotContext_520_ = v___x_496_;
v_currMacroScope_521_ = v___x_499_;
v_cancelTk_x3f_522_ = v___x_500_;
v_suppressElabErrors_523_ = v___x_501_;
v_inheritedTraceOptions_524_ = v___x_506_;
v___y_525_ = v___x_505_;
goto v___jp_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__1___boxed(lean_object** _args){
lean_object* v___x_575_ = _args[0];
lean_object* v___x_576_ = _args[1];
lean_object* v___x_577_ = _args[2];
lean_object* v_name_578_ = _args[3];
lean_object* v_a_579_ = _args[4];
lean_object* v___x_580_ = _args[5];
lean_object* v_head_581_ = _args[6];
lean_object* v___x_582_ = _args[7];
lean_object* v___x_583_ = _args[8];
lean_object* v___x_584_ = _args[9];
lean_object* v___x_585_ = _args[10];
lean_object* v___x_586_ = _args[11];
lean_object* v___x_587_ = _args[12];
lean_object* v___x_588_ = _args[13];
lean_object* v___x_589_ = _args[14];
lean_object* v___x_590_ = _args[15];
lean_object* v___x_591_ = _args[16];
lean_object* v___y_592_ = _args[17];
_start:
{
uint8_t v___x_36395__boxed_593_; uint8_t v___x_36396__boxed_594_; lean_object* v_res_595_; 
v___x_36395__boxed_593_ = lean_unbox(v___x_590_);
v___x_36396__boxed_594_ = lean_unbox(v___x_591_);
v_res_595_ = l_main___lam__1(v___x_575_, v___x_576_, v___x_577_, v_name_578_, v_a_579_, v___x_580_, v_head_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___x_589_, v___x_36395__boxed_593_, v___x_36396__boxed_594_);
lean_dec(v_a_579_);
lean_dec(v___x_576_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(lean_object* v_s_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_putStr_599_; lean_object* v___x_600_; 
v___x_598_ = lean_get_stderr();
v_putStr_599_ = lean_ctor_get(v___x_598_, 4);
lean_inc_ref(v_putStr_599_);
lean_dec_ref(v___x_598_);
v___x_600_ = lean_apply_2(v_putStr_599_, v_s_596_, lean_box(0));
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8___boxed(lean_object* v_s_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v_s_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6(lean_object* v_s_604_){
_start:
{
uint32_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = 10;
v___x_607_ = lean_string_push(v_s_604_, v___x_606_);
v___x_608_ = l_IO_eprint___at___00IO_eprintln___at___00main_spec__6_spec__8(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00main_spec__6___boxed(lean_object* v_s_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_IO_eprintln___at___00main_spec__6(v_s_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(lean_object* v_o_615_, lean_object* v_k_616_, lean_object* v_v_617_){
_start:
{
lean_object* v_map_618_; uint8_t v_hasTrace_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_633_; 
v_map_618_ = lean_ctor_get(v_o_615_, 0);
v_hasTrace_619_ = lean_ctor_get_uint8(v_o_615_, sizeof(void*)*1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_o_615_);
if (v_isSharedCheck_633_ == 0)
{
v___x_621_ = v_o_615_;
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_map_618_);
lean_dec(v_o_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_623_, 0, v_v_617_);
lean_inc(v_k_616_);
v___x_624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_616_, v___x_623_, v_map_618_);
if (v_hasTrace_619_ == 0)
{
lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_628_; 
v___x_625_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_626_ = l_Lean_Name_isPrefixOf(v___x_625_, v_k_616_);
lean_dec(v_k_616_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_624_);
v___x_628_ = v___x_621_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_624_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*1, v___x_626_);
return v___x_628_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v_k_616_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_624_);
v___x_631_ = v___x_621_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_624_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*1, v_hasTrace_619_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00main_spec__3(lean_object* v_opts_634_, lean_object* v_opt_635_, lean_object* v_val_636_){
_start:
{
lean_object* v_name_637_; lean_object* v___x_638_; 
v_name_637_ = lean_ctor_get(v_opt_635_, 0);
lean_inc(v_name_637_);
lean_dec_ref(v_opt_635_);
v___x_638_ = l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3(v_opts_634_, v_name_637_, v_val_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(lean_object* v___y_640_, lean_object* v_as_641_, size_t v_i_642_, size_t v_stop_643_, lean_object* v_b_644_){
_start:
{
lean_object* v___y_646_; uint8_t v___x_650_; 
v___x_650_ = lean_usize_dec_eq(v_i_642_, v_stop_643_);
if (v___x_650_ == 0)
{
lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___y_656_; 
v_fst_651_ = lean_ctor_get(v_b_644_, 0);
v_snd_652_ = lean_ctor_get(v_b_644_, 1);
v___x_653_ = lean_array_uget_borrowed(v_as_641_, v_i_642_);
v___x_654_ = l_Lean_IR_Decl_name(v___x_653_);
if (lean_obj_tag(v___x_654_) == 1)
{
lean_object* v_pre_669_; lean_object* v_str_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_pre_669_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_pre_669_);
v_str_670_ = lean_ctor_get(v___x_654_, 1);
lean_inc_ref(v_str_670_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___closed__0));
v___x_672_ = lean_string_dec_eq(v_str_670_, v___x_671_);
lean_dec_ref(v_str_670_);
if (v___x_672_ == 0)
{
lean_dec(v_pre_669_);
lean_inc_ref(v___x_654_);
v___y_656_ = v___x_654_;
goto v___jp_655_;
}
else
{
v___y_656_ = v_pre_669_;
goto v___jp_655_;
}
}
else
{
lean_inc(v___x_654_);
v___y_656_ = v___x_654_;
goto v___jp_655_;
}
v___jp_655_:
{
uint8_t v___x_657_; 
lean_inc_ref(v___y_640_);
v___x_657_ = l_Lean_isExtern(v___y_640_, v___y_656_);
if (v___x_657_ == 0)
{
lean_dec(v___x_654_);
v___y_646_ = v_b_644_;
goto v___jp_645_;
}
else
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_666_; 
lean_inc(v_snd_652_);
lean_inc(v_fst_651_);
v_isSharedCheck_666_ = !lean_is_exclusive(v_b_644_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; lean_object* v_unused_668_; 
v_unused_667_ = lean_ctor_get(v_b_644_, 1);
lean_dec(v_unused_667_);
v_unused_668_ = lean_ctor_get(v_b_644_, 0);
lean_dec(v_unused_668_);
v___x_659_ = v_b_644_;
v_isShared_660_ = v_isSharedCheck_666_;
goto v_resetjp_658_;
}
else
{
lean_dec(v_b_644_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_666_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_inc_n(v___x_653_, 2);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_653_);
lean_ctor_set(v___x_661_, 1, v_fst_651_);
v___x_662_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_652_, v___x_654_, v___x_653_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 1, v___x_662_);
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_664_ = v___x_659_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v___y_646_ = v___x_664_;
goto v___jp_645_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_640_);
return v_b_644_;
}
v___jp_645_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_642_, v___x_647_);
v_i_642_ = v___x_648_;
v_b_644_ = v___y_646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16___boxed(lean_object* v___y_673_, lean_object* v_as_674_, lean_object* v_i_675_, lean_object* v_stop_676_, lean_object* v_b_677_){
_start:
{
size_t v_i_boxed_678_; size_t v_stop_boxed_679_; lean_object* v_res_680_; 
v_i_boxed_678_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_stop_boxed_679_ = lean_unbox_usize(v_stop_676_);
lean_dec(v_stop_676_);
v_res_680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_673_, v_as_674_, v_i_boxed_678_, v_stop_boxed_679_, v_b_677_);
lean_dec_ref(v_as_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_as_x27_682_, lean_object* v_b_683_){
_start:
{
if (lean_obj_tag(v_as_x27_682_) == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_683_);
return v___x_685_;
}
else
{
lean_object* v_head_686_; lean_object* v_tail_687_; lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_714_; 
v_head_686_ = lean_ctor_get(v_as_x27_682_, 0);
v_tail_687_ = lean_ctor_get(v_as_x27_682_, 1);
v_fst_688_ = lean_ctor_get(v_b_683_, 0);
v_snd_689_ = lean_ctor_get(v_b_683_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_b_683_);
if (v_isSharedCheck_714_ == 0)
{
v___x_691_ = v_b_683_;
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_inc(v_fst_688_);
lean_dec(v_b_683_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_714_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_694_ = lean_string_dec_eq(v_head_686_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_inc(v_head_686_);
v___x_695_ = l___private_LeanIR_0__setConfigOption(v_snd_689_, v_head_686_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_a_696_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_fst_688_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_a_696_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
v_as_x27_682_ = v_tail_687_;
v_b_683_ = v___x_698_;
goto _start;
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_691_);
lean_dec(v_fst_688_);
v_a_701_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_695_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_695_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec(v_fst_688_);
v___x_709_ = lean_box(v___x_694_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_709_);
v___x_711_ = v___x_691_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_snd_689_);
v___x_711_ = v_reuseFailAlloc_713_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
v_as_x27_682_ = v_tail_687_;
v_b_683_ = v___x_711_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_as_x27_715_, lean_object* v_b_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_715_, v_b_716_);
lean_dec(v_as_x27_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(lean_object* v_as_719_, size_t v_i_720_, size_t v_stop_721_, lean_object* v_b_722_){
_start:
{
uint8_t v___x_723_; 
v___x_723_ = lean_usize_dec_eq(v_i_720_, v_stop_721_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v_toEnvExtension_725_; lean_object* v_asyncMode_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; size_t v___x_730_; size_t v___x_731_; 
v___x_724_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_725_ = lean_ctor_get(v___x_724_, 0);
v_asyncMode_726_ = lean_ctor_get(v_toEnvExtension_725_, 2);
v___x_727_ = lean_box(0);
v___x_728_ = lean_array_uget_borrowed(v_as_719_, v_i_720_);
lean_inc(v___x_728_);
v___x_729_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_724_, v_b_722_, v___x_728_, v_asyncMode_726_, v___x_727_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_720_, v___x_730_);
v_i_720_ = v___x_731_;
v_b_722_ = v___x_729_;
goto _start;
}
else
{
return v_b_722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18___boxed(lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_stop_735_, lean_object* v_b_736_){
_start:
{
size_t v_i_boxed_737_; size_t v_stop_boxed_738_; lean_object* v_res_739_; 
v_i_boxed_737_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_stop_boxed_738_ = lean_unbox_usize(v_stop_735_);
lean_dec(v_stop_735_);
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v_as_733_, v_i_boxed_737_, v_stop_boxed_738_, v_b_736_);
lean_dec_ref(v_as_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(lean_object* v_as_743_, size_t v_sz_744_, size_t v_i_745_, lean_object* v_b_746_, lean_object* v___y_747_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_lt(v_i_745_, v_sz_744_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_b_746_);
return v___x_750_;
}
else
{
uint8_t v___x_751_; lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_b_746_);
v___x_751_ = 0;
v_a_752_ = lean_array_uget_borrowed(v_as_743_, v_i_745_);
lean_inc(v_a_752_);
v___x_753_ = l_Lean_Message_toString(v_a_752_, v___x_751_);
v___x_754_ = l_IO_eprintln___at___00main_spec__6(v___x_753_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; 
lean_dec_ref(v___x_754_);
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_745_, v___x_756_);
v_i_745_ = v___x_757_;
v_b_746_ = v___x_755_;
goto _start;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_771_; 
v_a_759_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_771_ == 0)
{
v___x_761_ = v___x_754_;
v_isShared_762_ = v_isSharedCheck_771_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_754_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_771_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_ref_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v_ref_763_ = lean_ctor_get(v___y_747_, 5);
v___x_764_ = lean_io_error_to_string(v_a_759_);
v___x_765_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
v___x_766_ = l_Lean_MessageData_ofFormat(v___x_765_);
lean_inc(v_ref_763_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_ref_763_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_767_);
v___x_769_ = v___x_761_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___boxed(lean_object* v_as_772_, lean_object* v_sz_773_, lean_object* v_i_774_, lean_object* v_b_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
size_t v_sz_boxed_778_; size_t v_i_boxed_779_; lean_object* v_res_780_; 
v_sz_boxed_778_ = lean_unbox_usize(v_sz_773_);
lean_dec(v_sz_773_);
v_i_boxed_779_ = lean_unbox_usize(v_i_774_);
lean_dec(v_i_774_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_772_, v_sz_boxed_778_, v_i_boxed_779_, v_b_775_, v___y_776_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v_as_772_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(lean_object* v_as_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_b_784_);
return v___x_789_;
}
else
{
uint8_t v___x_790_; lean_object* v_a_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v_b_784_);
v___x_790_ = 0;
v_a_791_ = lean_array_uget_borrowed(v_as_781_, v_i_783_);
lean_inc(v_a_791_);
v___x_792_ = l_Lean_Message_toString(v_a_791_, v___x_790_);
v___x_793_ = l_IO_eprintln___at___00main_spec__6(v___x_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v___x_793_);
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_795_ = ((size_t)1ULL);
v___x_796_ = lean_usize_add(v_i_783_, v___x_795_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_781_, v_sz_782_, v___x_796_, v___x_794_, v___y_785_);
return v___x_797_;
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_810_; 
v_a_798_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_810_ == 0)
{
v___x_800_ = v___x_793_;
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_793_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_ref_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v_ref_802_ = lean_ctor_get(v___y_785_, 5);
v___x_803_ = lean_io_error_to_string(v_a_798_);
v___x_804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = l_Lean_MessageData_ofFormat(v___x_804_);
lean_inc(v_ref_802_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_ref_802_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_806_);
v___x_808_ = v___x_800_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27___boxed(lean_object* v_as_811_, lean_object* v_sz_812_, lean_object* v_i_813_, lean_object* v_b_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
size_t v_sz_boxed_818_; size_t v_i_boxed_819_; lean_object* v_res_820_; 
v_sz_boxed_818_ = lean_unbox_usize(v_sz_812_);
lean_dec(v_sz_812_);
v_i_boxed_819_ = lean_unbox_usize(v_i_813_);
lean_dec(v_i_813_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_as_811_, v_sz_boxed_818_, v_i_boxed_819_, v_b_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec_ref(v_as_811_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(lean_object* v_as_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_b_827_, lean_object* v___y_828_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v_b_827_);
return v___x_831_;
}
else
{
uint8_t v___x_832_; lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_b_827_);
v___x_832_ = 0;
v_a_833_ = lean_array_uget_borrowed(v_as_824_, v_i_826_);
lean_inc(v_a_833_);
v___x_834_ = l_Lean_Message_toString(v_a_833_, v___x_832_);
v___x_835_ = l_IO_eprintln___at___00main_spec__6(v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; 
lean_dec_ref(v___x_835_);
v___x_836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_826_, v___x_837_);
v_i_826_ = v___x_838_;
v_b_827_ = v___x_836_;
goto _start;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_852_; 
v_a_840_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_852_ == 0)
{
v___x_842_ = v___x_835_;
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_835_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_852_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_ref_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_ref_844_ = lean_ctor_get(v___y_828_, 5);
v___x_845_ = lean_io_error_to_string(v_a_840_);
v___x_846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
v___x_847_ = l_Lean_MessageData_ofFormat(v___x_846_);
lean_inc(v_ref_844_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_ref_844_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_848_);
v___x_850_ = v___x_842_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___boxed(lean_object* v_as_853_, lean_object* v_sz_854_, lean_object* v_i_855_, lean_object* v_b_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
size_t v_sz_boxed_859_; size_t v_i_boxed_860_; lean_object* v_res_861_; 
v_sz_boxed_859_ = lean_unbox_usize(v_sz_854_);
lean_dec(v_sz_854_);
v_i_boxed_860_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_853_, v_sz_boxed_859_, v_i_boxed_860_, v_b_856_, v___y_857_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_as_853_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(lean_object* v_as_862_, size_t v_sz_863_, size_t v_i_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
uint8_t v___x_869_; 
v___x_869_ = lean_usize_dec_lt(v_i_864_, v_sz_863_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v_b_865_);
return v___x_870_;
}
else
{
uint8_t v___x_871_; lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref(v_b_865_);
v___x_871_ = 0;
v_a_872_ = lean_array_uget_borrowed(v_as_862_, v_i_864_);
lean_inc(v_a_872_);
v___x_873_ = l_Lean_Message_toString(v_a_872_, v___x_871_);
v___x_874_ = l_IO_eprintln___at___00main_spec__6(v___x_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; 
lean_dec_ref(v___x_874_);
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_864_, v___x_876_);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_862_, v_sz_863_, v___x_877_, v___x_875_, v___y_866_);
return v___x_878_;
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_891_; 
v_a_879_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_891_ == 0)
{
v___x_881_ = v___x_874_;
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_874_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_ref_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v_ref_883_ = lean_ctor_get(v___y_866_, 5);
v___x_884_ = lean_io_error_to_string(v_a_879_);
v___x_885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
v___x_886_ = l_Lean_MessageData_ofFormat(v___x_885_);
lean_inc(v_ref_883_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_ref_883_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_887_);
v___x_889_ = v___x_881_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38___boxed(lean_object* v_as_892_, lean_object* v_sz_893_, lean_object* v_i_894_, lean_object* v_b_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_893_);
lean_dec(v_sz_893_);
v_i_boxed_900_ = lean_unbox_usize(v_i_894_);
lean_dec(v_i_894_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_as_892_, v_sz_boxed_899_, v_i_boxed_900_, v_b_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec_ref(v_as_892_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(lean_object* v_init_902_, lean_object* v_n_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
if (lean_obj_tag(v_n_903_) == 0)
{
lean_object* v_cs_908_; lean_object* v___x_909_; lean_object* v___x_910_; size_t v_sz_911_; size_t v___x_912_; lean_object* v___x_913_; 
v_cs_908_ = lean_ctor_get(v_n_903_, 0);
v___x_909_ = lean_box(0);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v_b_904_);
v_sz_911_ = lean_array_size(v_cs_908_);
v___x_912_ = ((size_t)0ULL);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_902_, v_cs_908_, v_sz_911_, v___x_912_, v___x_910_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_928_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_928_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_928_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_928_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_fst_918_; 
v_fst_918_ = lean_ctor_get(v_a_914_, 0);
if (lean_obj_tag(v_fst_918_) == 0)
{
lean_object* v_snd_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v_snd_919_ = lean_ctor_get(v_a_914_, 1);
lean_inc(v_snd_919_);
lean_dec(v_a_914_);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v_snd_919_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_920_);
v___x_922_ = v___x_916_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v_val_924_; lean_object* v___x_926_; 
lean_inc_ref(v_fst_918_);
lean_dec(v_a_914_);
v_val_924_ = lean_ctor_get(v_fst_918_, 0);
lean_inc(v_val_924_);
lean_dec_ref(v_fst_918_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v_val_924_);
v___x_926_ = v___x_916_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_val_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
v_a_929_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_913_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_913_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_vs_937_; lean_object* v___x_938_; lean_object* v___x_939_; size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; 
v_vs_937_ = lean_ctor_get(v_n_903_, 0);
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_b_904_);
v_sz_940_ = lean_array_size(v_vs_937_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38(v_vs_937_, v_sz_940_, v___x_941_, v___x_939_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_957_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_957_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_957_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_fst_947_; 
v_fst_947_ = lean_ctor_get(v_a_943_, 0);
if (lean_obj_tag(v_fst_947_) == 0)
{
lean_object* v_snd_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v_snd_948_ = lean_ctor_get(v_a_943_, 1);
lean_inc(v_snd_948_);
lean_dec(v_a_943_);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v_snd_948_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_949_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
else
{
lean_object* v_val_953_; lean_object* v___x_955_; 
lean_inc_ref(v_fst_947_);
lean_dec(v_a_943_);
v_val_953_ = lean_ctor_get(v_fst_947_, 0);
lean_inc(v_val_953_);
lean_dec_ref(v_fst_947_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_val_953_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_val_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_a_958_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_942_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_942_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(lean_object* v_init_966_, lean_object* v_as_967_, size_t v_sz_968_, size_t v_i_969_, lean_object* v_b_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = lean_usize_dec_lt(v_i_969_, v_sz_968_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_b_970_);
return v___x_975_;
}
else
{
lean_object* v_snd_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1010_; 
v_snd_976_ = lean_ctor_get(v_b_970_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_b_970_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_b_970_, 0);
lean_dec(v_unused_1011_);
v___x_978_ = v_b_970_;
v_isShared_979_ = v_isSharedCheck_1010_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snd_976_);
lean_dec(v_b_970_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1010_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_array_uget_borrowed(v_as_967_, v_i_969_);
lean_inc(v_snd_976_);
v___x_981_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_966_, v_a_980_, v_snd_976_, v___y_971_, v___y_972_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1001_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1001_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1001_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
if (lean_obj_tag(v_a_982_) == 0)
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_a_982_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_986_);
v___x_988_ = v___x_978_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_snd_976_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_988_);
v___x_990_ = v___x_984_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
lean_del_object(v___x_984_);
lean_dec(v_snd_976_);
v_a_993_ = lean_ctor_get(v_a_982_, 0);
lean_inc(v_a_993_);
lean_dec_ref(v_a_982_);
v___x_994_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v_a_993_);
lean_ctor_set(v___x_978_, 0, v___x_994_);
v___x_996_ = v___x_978_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_a_993_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
size_t v___x_997_; size_t v___x_998_; 
v___x_997_ = ((size_t)1ULL);
v___x_998_ = lean_usize_add(v_i_969_, v___x_997_);
v_i_969_ = v___x_998_;
v_b_970_ = v___x_996_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_del_object(v___x_978_);
lean_dec(v_snd_976_);
v_a_1002_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_981_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_981_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37___boxed(lean_object* v_init_1012_, lean_object* v_as_1013_, lean_object* v_sz_1014_, lean_object* v_i_1015_, lean_object* v_b_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
size_t v_sz_boxed_1020_; size_t v_i_boxed_1021_; lean_object* v_res_1022_; 
v_sz_boxed_1020_ = lean_unbox_usize(v_sz_1014_);
lean_dec(v_sz_1014_);
v_i_boxed_1021_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__37(v_init_1012_, v_as_1013_, v_sz_boxed_1020_, v_i_boxed_1021_, v_b_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_as_1013_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26___boxed(lean_object* v_init_1023_, lean_object* v_n_1024_, lean_object* v_b_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1023_, v_n_1024_, v_b_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec_ref(v_n_1024_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12(lean_object* v_t_1030_, lean_object* v_init_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_root_1035_; lean_object* v_tail_1036_; lean_object* v___x_1037_; 
v_root_1035_ = lean_ctor_get(v_t_1030_, 0);
v_tail_1036_ = lean_ctor_get(v_t_1030_, 1);
v___x_1037_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26(v_init_1031_, v_root_1035_, v_init_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1074_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1074_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1074_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
if (lean_obj_tag(v_a_1038_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; 
v_a_1042_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_a_1042_);
lean_dec_ref(v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v_a_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; size_t v_sz_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
lean_del_object(v___x_1040_);
v_a_1046_ = lean_ctor_get(v_a_1038_, 0);
lean_inc(v_a_1046_);
lean_dec_ref(v_a_1038_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v_a_1046_);
v_sz_1049_ = lean_array_size(v_tail_1036_);
v___x_1050_ = ((size_t)0ULL);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27(v_tail_1036_, v_sz_1049_, v___x_1050_, v___x_1048_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1065_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1065_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1065_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_fst_1056_; 
v_fst_1056_ = lean_ctor_get(v_a_1052_, 0);
if (lean_obj_tag(v_fst_1056_) == 0)
{
lean_object* v_snd_1057_; lean_object* v___x_1059_; 
v_snd_1057_ = lean_ctor_get(v_a_1052_, 1);
lean_inc(v_snd_1057_);
lean_dec(v_a_1052_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v_snd_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_snd_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
else
{
lean_object* v_val_1061_; lean_object* v___x_1063_; 
lean_inc_ref(v_fst_1056_);
lean_dec(v_a_1052_);
v_val_1061_ = lean_ctor_get(v_fst_1056_, 0);
lean_inc(v_val_1061_);
lean_dec_ref(v_fst_1056_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v_val_1061_);
v___x_1063_ = v___x_1054_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_val_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_a_1066_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1051_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1051_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1037_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1037_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__12___boxed(lean_object* v_t_1083_, lean_object* v_init_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_t_1083_, v_init_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v_t_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(uint8_t v___x_1096_, uint8_t v_suppressElabErrors_1097_, lean_object* v___x_1098_, lean_object* v_x_1099_){
_start:
{
if (lean_obj_tag(v_x_1099_) == 1)
{
lean_object* v_pre_1100_; 
v_pre_1100_ = lean_ctor_get(v_x_1099_, 0);
switch(lean_obj_tag(v_pre_1100_))
{
case 1:
{
lean_object* v_pre_1101_; 
v_pre_1101_ = lean_ctor_get(v_pre_1100_, 0);
switch(lean_obj_tag(v_pre_1101_))
{
case 0:
{
lean_object* v_str_1102_; lean_object* v_str_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_str_1102_ = lean_ctor_get(v_x_1099_, 1);
v_str_1103_ = lean_ctor_get(v_pre_1100_, 1);
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_1105_ = lean_string_dec_eq(v_str_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_1107_ = lean_string_dec_eq(v_str_1103_, v___x_1106_);
if (v___x_1107_ == 0)
{
return v___x_1096_;
}
else
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_1109_ = lean_string_dec_eq(v_str_1102_, v___x_1108_);
if (v___x_1109_ == 0)
{
return v___x_1096_;
}
else
{
return v_suppressElabErrors_1097_;
}
}
}
else
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_1111_ = lean_string_dec_eq(v_str_1102_, v___x_1110_);
if (v___x_1111_ == 0)
{
return v___x_1096_;
}
else
{
return v_suppressElabErrors_1097_;
}
}
}
case 1:
{
lean_object* v_pre_1112_; 
v_pre_1112_ = lean_ctor_get(v_pre_1101_, 0);
if (lean_obj_tag(v_pre_1112_) == 0)
{
lean_object* v_str_1113_; lean_object* v_str_1114_; lean_object* v_str_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_str_1113_ = lean_ctor_get(v_x_1099_, 1);
v_str_1114_ = lean_ctor_get(v_pre_1100_, 1);
v_str_1115_ = lean_ctor_get(v_pre_1101_, 1);
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_1117_ = lean_string_dec_eq(v_str_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
return v___x_1096_;
}
else
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_1119_ = lean_string_dec_eq(v_str_1114_, v___x_1118_);
if (v___x_1119_ == 0)
{
return v___x_1096_;
}
else
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_1121_ = lean_string_dec_eq(v_str_1113_, v___x_1120_);
if (v___x_1121_ == 0)
{
return v___x_1096_;
}
else
{
return v_suppressElabErrors_1097_;
}
}
}
}
else
{
return v___x_1096_;
}
}
default: 
{
return v___x_1096_;
}
}
}
case 0:
{
lean_object* v_str_1122_; uint8_t v___x_1123_; 
v_str_1122_ = lean_ctor_get(v_x_1099_, 1);
v___x_1123_ = lean_string_dec_eq(v_str_1122_, v___x_1098_);
if (v___x_1123_ == 0)
{
return v___x_1096_;
}
else
{
return v_suppressElabErrors_1097_;
}
}
default: 
{
return v___x_1096_;
}
}
}
else
{
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed(lean_object* v___x_1124_, lean_object* v_suppressElabErrors_1125_, lean_object* v___x_1126_, lean_object* v_x_1127_){
_start:
{
uint8_t v___x_37262__boxed_1128_; uint8_t v_suppressElabErrors_boxed_1129_; uint8_t v_res_1130_; lean_object* v_r_1131_; 
v___x_37262__boxed_1128_ = lean_unbox(v___x_1124_);
v_suppressElabErrors_boxed_1129_ = lean_unbox(v_suppressElabErrors_1125_);
v_res_1130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0(v___x_37262__boxed_1128_, v_suppressElabErrors_boxed_1129_, v___x_1126_, v_x_1127_);
lean_dec(v_x_1127_);
lean_dec_ref(v___x_1126_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0(void){
_start:
{
lean_object* v___x_1132_; double v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_float_of_nat(v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(uint8_t v___x_1135_, lean_object* v_as_1136_, size_t v_sz_1137_, size_t v_i_1138_, lean_object* v_b_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_a_1144_; uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_lt(v_i_1138_, v_sz_1137_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_b_1139_);
return v___x_1149_;
}
else
{
lean_object* v_a_1150_; lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1228_; 
v_a_1150_ = lean_array_uget(v_as_1136_, v_i_1138_);
v_fst_1151_ = lean_ctor_get(v_a_1150_, 0);
v_snd_1152_ = lean_ctor_get(v_a_1150_, 1);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_a_1150_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1154_ = v_a_1150_;
v_isShared_1155_ = v_isSharedCheck_1228_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_inc(v_fst_1151_);
lean_dec(v_a_1150_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1228_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1227_; 
v_fst_1156_ = lean_ctor_get(v_fst_1151_, 0);
v_snd_1157_ = lean_ctor_get(v_fst_1151_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_fst_1151_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1159_ = v_fst_1151_;
v_isShared_1160_ = v_isSharedCheck_1227_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_inc(v_fst_1156_);
lean_dec(v_fst_1151_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1227_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; double v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_fileName_1166_; lean_object* v_fileMap_1167_; uint8_t v_suppressElabErrors_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__0);
v___x_1164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
v___x_1165_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1165_, 0, v___x_1161_);
lean_ctor_set(v___x_1165_, 1, v___x_1162_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
lean_ctor_set_float(v___x_1165_, sizeof(void*)*3, v___x_1163_);
lean_ctor_set_float(v___x_1165_, sizeof(void*)*3 + 8, v___x_1163_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*3 + 16, v___x_1148_);
v_fileName_1166_ = lean_ctor_get(v___y_1140_, 0);
v_fileMap_1167_ = lean_ctor_get(v___y_1140_, 1);
v_suppressElabErrors_1168_ = lean_ctor_get_uint8(v___y_1140_, sizeof(void*)*14 + 1);
v___x_1169_ = lean_box(0);
v___x_1170_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_1171_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__1));
v___x_1172_ = l_Lean_MessageData_nil;
v___x_1173_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1165_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
lean_ctor_set(v___x_1173_, 2, v_snd_1152_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 8);
lean_ctor_set(v___x_1159_, 1, v___x_1173_);
lean_ctor_set(v___x_1159_, 0, v___x_1171_);
v___x_1175_ = v___x_1159_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___y_1179_; lean_object* v___y_1180_; 
v___x_1176_ = 0;
lean_inc_ref(v_fileMap_1167_);
lean_inc_ref(v_fileName_1166_);
v___x_1177_ = l_Lean_Elab_mkMessageCore(v_fileName_1166_, v_fileMap_1167_, v___x_1175_, v___x_1176_, v_fst_1156_, v_snd_1157_);
lean_dec(v_snd_1157_);
lean_dec(v_fst_1156_);
if (v_suppressElabErrors_1168_ == 0)
{
v___y_1179_ = v___y_1140_;
v___y_1180_ = v___y_1141_;
goto v___jp_1178_;
}
else
{
lean_object* v_data_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; uint8_t v___x_1225_; 
v_data_1221_ = lean_ctor_get(v___x_1177_, 4);
lean_inc(v_data_1221_);
v___x_1222_ = lean_box(v___x_1135_);
v___x_1223_ = lean_box(v_suppressElabErrors_1168_);
v___f_1224_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1224_, 0, v___x_1222_);
lean_closure_set(v___f_1224_, 1, v___x_1223_);
lean_closure_set(v___f_1224_, 2, v___x_1170_);
v___x_1225_ = l_Lean_MessageData_hasTag(v___f_1224_, v_data_1221_);
if (v___x_1225_ == 0)
{
lean_dec_ref(v___x_1177_);
lean_del_object(v___x_1154_);
v_a_1144_ = v___x_1169_;
goto v___jp_1143_;
}
else
{
v___y_1179_ = v___y_1140_;
v___y_1180_ = v___y_1141_;
goto v___jp_1178_;
}
}
v___jp_1178_:
{
lean_object* v___x_1181_; lean_object* v_fileName_1182_; lean_object* v_pos_1183_; lean_object* v_endPos_1184_; uint8_t v_keepFullRange_1185_; uint8_t v_severity_1186_; uint8_t v_isSilent_1187_; lean_object* v_caption_1188_; lean_object* v_data_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1220_; 
v___x_1181_ = lean_st_ref_take(v___y_1180_);
v_fileName_1182_ = lean_ctor_get(v___x_1177_, 0);
v_pos_1183_ = lean_ctor_get(v___x_1177_, 1);
v_endPos_1184_ = lean_ctor_get(v___x_1177_, 2);
v_keepFullRange_1185_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*5);
v_severity_1186_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*5 + 1);
v_isSilent_1187_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*5 + 2);
v_caption_1188_ = lean_ctor_get(v___x_1177_, 3);
v_data_1189_ = lean_ctor_get(v___x_1177_, 4);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1191_ = v___x_1177_;
v_isShared_1192_ = v_isSharedCheck_1220_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_data_1189_);
lean_inc(v_caption_1188_);
lean_inc(v_endPos_1184_);
lean_inc(v_pos_1183_);
lean_inc(v_fileName_1182_);
lean_dec(v___x_1177_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1220_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_currNamespace_1193_; lean_object* v_openDecls_1194_; lean_object* v_env_1195_; lean_object* v_nextMacroScope_1196_; lean_object* v_ngen_1197_; lean_object* v_auxDeclNGen_1198_; lean_object* v_traceState_1199_; lean_object* v_cache_1200_; lean_object* v_messages_1201_; lean_object* v_infoState_1202_; lean_object* v_snapshotTasks_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1219_; 
v_currNamespace_1193_ = lean_ctor_get(v___y_1179_, 6);
v_openDecls_1194_ = lean_ctor_get(v___y_1179_, 7);
v_env_1195_ = lean_ctor_get(v___x_1181_, 0);
v_nextMacroScope_1196_ = lean_ctor_get(v___x_1181_, 1);
v_ngen_1197_ = lean_ctor_get(v___x_1181_, 2);
v_auxDeclNGen_1198_ = lean_ctor_get(v___x_1181_, 3);
v_traceState_1199_ = lean_ctor_get(v___x_1181_, 4);
v_cache_1200_ = lean_ctor_get(v___x_1181_, 5);
v_messages_1201_ = lean_ctor_get(v___x_1181_, 6);
v_infoState_1202_ = lean_ctor_get(v___x_1181_, 7);
v_snapshotTasks_1203_ = lean_ctor_get(v___x_1181_, 8);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1205_ = v___x_1181_;
v_isShared_1206_ = v_isSharedCheck_1219_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_snapshotTasks_1203_);
lean_inc(v_infoState_1202_);
lean_inc(v_messages_1201_);
lean_inc(v_cache_1200_);
lean_inc(v_traceState_1199_);
lean_inc(v_auxDeclNGen_1198_);
lean_inc(v_ngen_1197_);
lean_inc(v_nextMacroScope_1196_);
lean_inc(v_env_1195_);
lean_dec(v___x_1181_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1219_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
lean_inc(v_openDecls_1194_);
lean_inc(v_currNamespace_1193_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_openDecls_1194_);
lean_ctor_set(v___x_1154_, 0, v_currNamespace_1193_);
v___x_1208_ = v___x_1154_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_currNamespace_1193_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_openDecls_1194_);
v___x_1208_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v_data_1189_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 4, v___x_1209_);
v___x_1211_ = v___x_1191_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_fileName_1182_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_pos_1183_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_endPos_1184_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_caption_1188_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v___x_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*5, v_keepFullRange_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*5 + 1, v_severity_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1217_, sizeof(void*)*5 + 2, v_isSilent_1187_);
v___x_1211_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = l_Lean_MessageLog_add(v___x_1211_, v_messages_1201_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 6, v___x_1212_);
v___x_1214_ = v___x_1205_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_env_1195_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_nextMacroScope_1196_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_ngen_1197_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_auxDeclNGen_1198_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_traceState_1199_);
lean_ctor_set(v_reuseFailAlloc_1216_, 5, v_cache_1200_);
lean_ctor_set(v_reuseFailAlloc_1216_, 6, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1216_, 7, v_infoState_1202_);
lean_ctor_set(v_reuseFailAlloc_1216_, 8, v_snapshotTasks_1203_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_st_ref_set(v___y_1180_, v___x_1214_);
v_a_1144_ = v___x_1169_;
goto v___jp_1143_;
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
v___jp_1143_:
{
size_t v___x_1145_; size_t v___x_1146_; 
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1138_, v___x_1145_);
v_i_1138_ = v___x_1146_;
v_b_1139_ = v_a_1144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___boxed(lean_object* v___x_1229_, lean_object* v_as_1230_, lean_object* v_sz_1231_, lean_object* v_i_1232_, lean_object* v_b_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v___x_37335__boxed_1237_; size_t v_sz_boxed_1238_; size_t v_i_boxed_1239_; lean_object* v_res_1240_; 
v___x_37335__boxed_1237_ = lean_unbox(v___x_1229_);
v_sz_boxed_1238_ = lean_unbox_usize(v_sz_1231_);
lean_dec(v_sz_1231_);
v_i_boxed_1239_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_37335__boxed_1237_, v_as_1230_, v_sz_boxed_1238_, v_i_boxed_1239_, v_b_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v_as_1230_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(lean_object* v_opts_1241_, lean_object* v_opt_1242_){
_start:
{
lean_object* v_name_1243_; lean_object* v_map_1244_; lean_object* v___x_1245_; 
v_name_1243_ = lean_ctor_get(v_opt_1242_, 0);
v_map_1244_ = lean_ctor_get(v_opts_1241_, 0);
v___x_1245_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1244_, v_name_1243_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; 
v___x_1246_ = lean_box(0);
return v___x_1246_;
}
else
{
lean_object* v_val_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1256_; 
v_val_1247_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1249_ = v___x_1245_;
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_val_1247_);
lean_dec(v___x_1245_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
if (lean_obj_tag(v_val_1247_) == 0)
{
lean_object* v_v_1251_; lean_object* v___x_1253_; 
v_v_1251_ = lean_ctor_get(v_val_1247_, 0);
lean_inc_ref(v_v_1251_);
lean_dec_ref(v_val_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_v_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_v_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
else
{
lean_object* v___x_1255_; 
lean_del_object(v___x_1249_);
lean_dec(v_val_1247_);
v___x_1255_ = lean_box(0);
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15___boxed(lean_object* v_opts_1257_, lean_object* v_opt_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_opts_1257_, v_opt_1258_);
lean_dec_ref(v_opt_1258_);
lean_dec_ref(v_opts_1257_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(lean_object* v_a_1260_, lean_object* v_fallback_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
lean_inc(v_fallback_1261_);
return v_fallback_1261_;
}
else
{
lean_object* v_key_1263_; lean_object* v_value_1264_; lean_object* v_tail_1265_; uint8_t v___y_1267_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; uint8_t v___x_1273_; 
v_key_1263_ = lean_ctor_get(v_x_1262_, 0);
v_value_1264_ = lean_ctor_get(v_x_1262_, 1);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
v_fst_1269_ = lean_ctor_get(v_key_1263_, 0);
v_snd_1270_ = lean_ctor_get(v_key_1263_, 1);
v_fst_1271_ = lean_ctor_get(v_a_1260_, 0);
v_snd_1272_ = lean_ctor_get(v_a_1260_, 1);
v___x_1273_ = lean_nat_dec_eq(v_fst_1269_, v_fst_1271_);
if (v___x_1273_ == 0)
{
v___y_1267_ = v___x_1273_;
goto v___jp_1266_;
}
else
{
uint8_t v___x_1274_; 
v___x_1274_ = lean_nat_dec_eq(v_snd_1270_, v_snd_1272_);
v___y_1267_ = v___x_1274_;
goto v___jp_1266_;
}
v___jp_1266_:
{
if (v___y_1267_ == 0)
{
v_x_1262_ = v_tail_1265_;
goto _start;
}
else
{
lean_inc(v_value_1264_);
return v_value_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg___boxed(lean_object* v_a_1275_, lean_object* v_fallback_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1275_, v_fallback_1276_, v_x_1277_);
lean_dec(v_x_1277_);
lean_dec(v_fallback_1276_);
lean_dec_ref(v_a_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(lean_object* v_m_1279_, lean_object* v_a_1280_, lean_object* v_fallback_1281_){
_start:
{
lean_object* v_buckets_1282_; lean_object* v_fst_1283_; lean_object* v_snd_1284_; lean_object* v___x_1285_; uint64_t v___x_1286_; uint64_t v___x_1287_; uint64_t v___x_1288_; uint64_t v___x_1289_; uint64_t v___x_1290_; uint64_t v_fold_1291_; uint64_t v___x_1292_; uint64_t v___x_1293_; uint64_t v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_buckets_1282_ = lean_ctor_get(v_m_1279_, 1);
v_fst_1283_ = lean_ctor_get(v_a_1280_, 0);
v_snd_1284_ = lean_ctor_get(v_a_1280_, 1);
v___x_1285_ = lean_array_get_size(v_buckets_1282_);
v___x_1286_ = l_String_instHashableRaw_hash(v_fst_1283_);
v___x_1287_ = l_String_instHashableRaw_hash(v_snd_1284_);
v___x_1288_ = lean_uint64_mix_hash(v___x_1286_, v___x_1287_);
v___x_1289_ = 32ULL;
v___x_1290_ = lean_uint64_shift_right(v___x_1288_, v___x_1289_);
v_fold_1291_ = lean_uint64_xor(v___x_1288_, v___x_1290_);
v___x_1292_ = 16ULL;
v___x_1293_ = lean_uint64_shift_right(v_fold_1291_, v___x_1292_);
v___x_1294_ = lean_uint64_xor(v_fold_1291_, v___x_1293_);
v___x_1295_ = lean_uint64_to_usize(v___x_1294_);
v___x_1296_ = lean_usize_of_nat(v___x_1285_);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_sub(v___x_1296_, v___x_1297_);
v___x_1299_ = lean_usize_land(v___x_1295_, v___x_1298_);
v___x_1300_ = lean_array_uget_borrowed(v_buckets_1282_, v___x_1299_);
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_1280_, v_fallback_1281_, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg___boxed(lean_object* v_m_1302_, lean_object* v_a_1303_, lean_object* v_fallback_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_1302_, v_a_1303_, v_fallback_1304_);
lean_dec(v_fallback_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_m_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(lean_object* v_x_1306_, lean_object* v_x_1307_){
_start:
{
if (lean_obj_tag(v_x_1307_) == 0)
{
return v_x_1306_;
}
else
{
lean_object* v_key_1308_; lean_object* v_value_1309_; lean_object* v_tail_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1337_; 
v_key_1308_ = lean_ctor_get(v_x_1307_, 0);
v_value_1309_ = lean_ctor_get(v_x_1307_, 1);
v_tail_1310_ = lean_ctor_get(v_x_1307_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1307_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1312_ = v_x_1307_;
v_isShared_1313_ = v_isSharedCheck_1337_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_tail_1310_);
lean_inc(v_value_1309_);
lean_inc(v_key_1308_);
lean_dec(v_x_1307_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1337_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; uint64_t v_fold_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v_fst_1314_ = lean_ctor_get(v_key_1308_, 0);
v_snd_1315_ = lean_ctor_get(v_key_1308_, 1);
v___x_1316_ = lean_array_get_size(v_x_1306_);
v___x_1317_ = l_String_instHashableRaw_hash(v_fst_1314_);
v___x_1318_ = l_String_instHashableRaw_hash(v_snd_1315_);
v___x_1319_ = lean_uint64_mix_hash(v___x_1317_, v___x_1318_);
v___x_1320_ = 32ULL;
v___x_1321_ = lean_uint64_shift_right(v___x_1319_, v___x_1320_);
v_fold_1322_ = lean_uint64_xor(v___x_1319_, v___x_1321_);
v___x_1323_ = 16ULL;
v___x_1324_ = lean_uint64_shift_right(v_fold_1322_, v___x_1323_);
v___x_1325_ = lean_uint64_xor(v_fold_1322_, v___x_1324_);
v___x_1326_ = lean_uint64_to_usize(v___x_1325_);
v___x_1327_ = lean_usize_of_nat(v___x_1316_);
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_sub(v___x_1327_, v___x_1328_);
v___x_1330_ = lean_usize_land(v___x_1326_, v___x_1329_);
v___x_1331_ = lean_array_uget_borrowed(v_x_1306_, v___x_1330_);
lean_inc(v___x_1331_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 2, v___x_1331_);
v___x_1333_ = v___x_1312_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_key_1308_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_value_1309_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_array_uset(v_x_1306_, v___x_1330_, v___x_1333_);
v_x_1306_ = v___x_1334_;
v_x_1307_ = v_tail_1310_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(lean_object* v_i_1338_, lean_object* v_source_1339_, lean_object* v_target_1340_){
_start:
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = lean_array_get_size(v_source_1339_);
v___x_1342_ = lean_nat_dec_lt(v_i_1338_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v_source_1339_);
lean_dec(v_i_1338_);
return v_target_1340_;
}
else
{
lean_object* v_es_1343_; lean_object* v___x_1344_; lean_object* v_source_1345_; lean_object* v_target_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_es_1343_ = lean_array_fget(v_source_1339_, v_i_1338_);
v___x_1344_ = lean_box(0);
v_source_1345_ = lean_array_fset(v_source_1339_, v_i_1338_, v___x_1344_);
v_target_1346_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_target_1340_, v_es_1343_);
v___x_1347_ = lean_unsigned_to_nat(1u);
v___x_1348_ = lean_nat_add(v_i_1338_, v___x_1347_);
lean_dec(v_i_1338_);
v_i_1338_ = v___x_1348_;
v_source_1339_ = v_source_1345_;
v_target_1340_ = v_target_1346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(lean_object* v_data_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_nbuckets_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1351_ = lean_array_get_size(v_data_1350_);
v___x_1352_ = lean_unsigned_to_nat(2u);
v_nbuckets_1353_ = lean_nat_mul(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_mk_array(v_nbuckets_1353_, v___x_1355_);
v___x_1357_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v___x_1354_, v_data_1350_, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(lean_object* v_a_1358_, lean_object* v_b_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1360_) == 0)
{
lean_dec(v_b_1359_);
lean_dec_ref(v_a_1358_);
return v_x_1360_;
}
else
{
lean_object* v_key_1361_; lean_object* v_value_1362_; lean_object* v_tail_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1382_; 
v_key_1361_ = lean_ctor_get(v_x_1360_, 0);
v_value_1362_ = lean_ctor_get(v_x_1360_, 1);
v_tail_1363_ = lean_ctor_get(v_x_1360_, 2);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1365_ = v_x_1360_;
v_isShared_1366_ = v_isSharedCheck_1382_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_tail_1363_);
lean_inc(v_value_1362_);
lean_inc(v_key_1361_);
lean_dec(v_x_1360_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1382_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
uint8_t v___y_1368_; lean_object* v_fst_1376_; lean_object* v_snd_1377_; lean_object* v_fst_1378_; lean_object* v_snd_1379_; uint8_t v___x_1380_; 
v_fst_1376_ = lean_ctor_get(v_key_1361_, 0);
v_snd_1377_ = lean_ctor_get(v_key_1361_, 1);
v_fst_1378_ = lean_ctor_get(v_a_1358_, 0);
v_snd_1379_ = lean_ctor_get(v_a_1358_, 1);
v___x_1380_ = lean_nat_dec_eq(v_fst_1376_, v_fst_1378_);
if (v___x_1380_ == 0)
{
v___y_1368_ = v___x_1380_;
goto v___jp_1367_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_eq(v_snd_1377_, v_snd_1379_);
v___y_1368_ = v___x_1381_;
goto v___jp_1367_;
}
v___jp_1367_:
{
if (v___y_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1358_, v_b_1359_, v_tail_1363_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 2, v___x_1369_);
v___x_1371_ = v___x_1365_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_key_1361_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_value_1362_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
else
{
lean_object* v___x_1374_; 
lean_dec(v_value_1362_);
lean_dec(v_key_1361_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_b_1359_);
lean_ctor_set(v___x_1365_, 0, v_a_1358_);
v___x_1374_ = v___x_1365_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1358_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_b_1359_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_tail_1363_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(lean_object* v_a_1383_, lean_object* v_x_1384_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
uint8_t v___x_1385_; 
v___x_1385_ = 0;
return v___x_1385_;
}
else
{
lean_object* v_key_1386_; lean_object* v_tail_1387_; uint8_t v___y_1389_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v_fst_1393_; lean_object* v_snd_1394_; uint8_t v___x_1395_; 
v_key_1386_ = lean_ctor_get(v_x_1384_, 0);
v_tail_1387_ = lean_ctor_get(v_x_1384_, 2);
v_fst_1391_ = lean_ctor_get(v_key_1386_, 0);
v_snd_1392_ = lean_ctor_get(v_key_1386_, 1);
v_fst_1393_ = lean_ctor_get(v_a_1383_, 0);
v_snd_1394_ = lean_ctor_get(v_a_1383_, 1);
v___x_1395_ = lean_nat_dec_eq(v_fst_1391_, v_fst_1393_);
if (v___x_1395_ == 0)
{
v___y_1389_ = v___x_1395_;
goto v___jp_1388_;
}
else
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_nat_dec_eq(v_snd_1392_, v_snd_1394_);
v___y_1389_ = v___x_1396_;
goto v___jp_1388_;
}
v___jp_1388_:
{
if (v___y_1389_ == 0)
{
v_x_1384_ = v_tail_1387_;
goto _start;
}
else
{
return v___y_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg___boxed(lean_object* v_a_1397_, lean_object* v_x_1398_){
_start:
{
uint8_t v_res_1399_; lean_object* v_r_1400_; 
v_res_1399_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1397_, v_x_1398_);
lean_dec(v_x_1398_);
lean_dec_ref(v_a_1397_);
v_r_1400_ = lean_box(v_res_1399_);
return v_r_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(lean_object* v_m_1401_, lean_object* v_a_1402_, lean_object* v_b_1403_){
_start:
{
lean_object* v_size_1404_; lean_object* v_buckets_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1452_; 
v_size_1404_ = lean_ctor_get(v_m_1401_, 0);
v_buckets_1405_ = lean_ctor_get(v_m_1401_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_m_1401_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1407_ = v_m_1401_;
v_isShared_1408_ = v_isSharedCheck_1452_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_buckets_1405_);
lean_inc(v_size_1404_);
lean_dec(v_m_1401_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1452_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1411_; uint64_t v___x_1412_; uint64_t v___x_1413_; uint64_t v___x_1414_; uint64_t v___x_1415_; uint64_t v___x_1416_; uint64_t v_fold_1417_; uint64_t v___x_1418_; uint64_t v___x_1419_; uint64_t v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; size_t v___x_1425_; lean_object* v_bkt_1426_; uint8_t v___x_1427_; 
v_fst_1409_ = lean_ctor_get(v_a_1402_, 0);
v_snd_1410_ = lean_ctor_get(v_a_1402_, 1);
v___x_1411_ = lean_array_get_size(v_buckets_1405_);
v___x_1412_ = l_String_instHashableRaw_hash(v_fst_1409_);
v___x_1413_ = l_String_instHashableRaw_hash(v_snd_1410_);
v___x_1414_ = lean_uint64_mix_hash(v___x_1412_, v___x_1413_);
v___x_1415_ = 32ULL;
v___x_1416_ = lean_uint64_shift_right(v___x_1414_, v___x_1415_);
v_fold_1417_ = lean_uint64_xor(v___x_1414_, v___x_1416_);
v___x_1418_ = 16ULL;
v___x_1419_ = lean_uint64_shift_right(v_fold_1417_, v___x_1418_);
v___x_1420_ = lean_uint64_xor(v_fold_1417_, v___x_1419_);
v___x_1421_ = lean_uint64_to_usize(v___x_1420_);
v___x_1422_ = lean_usize_of_nat(v___x_1411_);
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_sub(v___x_1422_, v___x_1423_);
v___x_1425_ = lean_usize_land(v___x_1421_, v___x_1424_);
v_bkt_1426_ = lean_array_uget_borrowed(v_buckets_1405_, v___x_1425_);
v___x_1427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_1402_, v_bkt_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v_size_x27_1429_; lean_object* v___x_1430_; lean_object* v_buckets_x27_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
v_size_x27_1429_ = lean_nat_add(v_size_1404_, v___x_1428_);
lean_dec(v_size_1404_);
lean_inc(v_bkt_1426_);
v___x_1430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1430_, 0, v_a_1402_);
lean_ctor_set(v___x_1430_, 1, v_b_1403_);
lean_ctor_set(v___x_1430_, 2, v_bkt_1426_);
v_buckets_x27_1431_ = lean_array_uset(v_buckets_1405_, v___x_1425_, v___x_1430_);
v___x_1432_ = lean_unsigned_to_nat(4u);
v___x_1433_ = lean_nat_mul(v_size_x27_1429_, v___x_1432_);
v___x_1434_ = lean_unsigned_to_nat(3u);
v___x_1435_ = lean_nat_div(v___x_1433_, v___x_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_array_get_size(v_buckets_x27_1431_);
v___x_1437_ = lean_nat_dec_le(v___x_1435_, v___x_1436_);
lean_dec(v___x_1435_);
if (v___x_1437_ == 0)
{
lean_object* v_val_1438_; lean_object* v___x_1440_; 
v_val_1438_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_buckets_x27_1431_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v_val_1438_);
lean_ctor_set(v___x_1407_, 0, v_size_x27_1429_);
v___x_1440_ = v___x_1407_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_size_x27_1429_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_val_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v___x_1443_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v_buckets_x27_1431_);
lean_ctor_set(v___x_1407_, 0, v_size_x27_1429_);
v___x_1443_ = v___x_1407_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_size_x27_1429_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_buckets_x27_1431_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v_buckets_x27_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_inc(v_bkt_1426_);
v___x_1445_ = lean_box(0);
v_buckets_x27_1446_ = lean_array_uset(v_buckets_1405_, v___x_1425_, v___x_1445_);
v___x_1447_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_1402_, v_b_1403_, v_bkt_1426_);
v___x_1448_ = lean_array_uset(v_buckets_x27_1446_, v___x_1425_, v___x_1447_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v___x_1448_);
v___x_1450_ = v___x_1407_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_size_1404_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(uint8_t v___x_1455_, lean_object* v_as_1456_, size_t v_sz_1457_, size_t v_i_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_lt(v_i_1458_, v_sz_1457_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1459_);
return v___x_1463_;
}
else
{
lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1501_; 
v_snd_1464_ = lean_ctor_get(v_b_1459_, 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_b_1459_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_b_1459_, 0);
lean_dec(v_unused_1502_);
v___x_1466_ = v_b_1459_;
v_isShared_1467_ = v_isSharedCheck_1501_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_dec(v_b_1459_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1501_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_ref_1468_; lean_object* v_a_1469_; lean_object* v_ref_1470_; lean_object* v_msg_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1500_; 
v_ref_1468_ = lean_ctor_get(v___y_1460_, 5);
v_a_1469_ = lean_array_uget(v_as_1456_, v_i_1458_);
v_ref_1470_ = lean_ctor_get(v_a_1469_, 0);
v_msg_1471_ = lean_ctor_get(v_a_1469_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1473_ = v_a_1469_;
v_isShared_1474_ = v_isSharedCheck_1500_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_msg_1471_);
lean_inc(v_ref_1470_);
lean_dec(v_a_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1500_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v_ref_1492_; lean_object* v___y_1494_; lean_object* v___x_1497_; 
v___x_1475_ = lean_box(0);
v_ref_1492_ = l_Lean_replaceRef(v_ref_1470_, v_ref_1468_);
lean_dec(v_ref_1470_);
v___x_1497_ = l_Lean_Syntax_getPos_x3f(v_ref_1492_, v___x_1455_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
v___y_1494_ = v___x_1498_;
goto v___jp_1493_;
}
else
{
lean_object* v_val_1499_; 
v_val_1499_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1499_);
lean_dec_ref(v___x_1497_);
v___y_1494_ = v_val_1499_;
goto v___jp_1493_;
}
v___jp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___y_1478_);
lean_ctor_set(v___x_1466_, 0, v___y_1477_);
v___x_1480_ = v___x_1466_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___y_1477_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___y_1478_);
v___x_1480_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_pos2traces_1484_; lean_object* v___x_1486_; 
v___x_1481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1464_, v___x_1480_, v___x_1481_);
v___x_1483_ = lean_array_push(v___x_1482_, v_msg_1471_);
v_pos2traces_1484_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1464_, v___x_1480_, v___x_1483_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v_pos2traces_1484_);
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1486_ = v___x_1473_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_pos2traces_1484_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
size_t v___x_1487_; size_t v___x_1488_; 
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_add(v_i_1458_, v___x_1487_);
v_i_1458_ = v___x_1488_;
v_b_1459_ = v___x_1486_;
goto _start;
}
}
}
v___jp_1493_:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1492_, v___x_1455_);
lean_dec(v_ref_1492_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_inc(v___y_1494_);
v___y_1477_ = v___y_1494_;
v___y_1478_ = v___y_1494_;
goto v___jp_1476_;
}
else
{
lean_object* v_val_1496_; 
v_val_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_val_1496_);
lean_dec_ref(v___x_1495_);
v___y_1477_ = v___y_1494_;
v___y_1478_ = v_val_1496_;
goto v___jp_1476_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___boxed(lean_object* v___x_1503_, lean_object* v_as_1504_, lean_object* v_sz_1505_, lean_object* v_i_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v___x_37815__boxed_1510_; size_t v_sz_boxed_1511_; size_t v_i_boxed_1512_; lean_object* v_res_1513_; 
v___x_37815__boxed_1510_ = lean_unbox(v___x_1503_);
v_sz_boxed_1511_ = lean_unbox_usize(v_sz_1505_);
lean_dec(v_sz_1505_);
v_i_boxed_1512_ = lean_unbox_usize(v_i_1506_);
lean_dec(v_i_1506_);
v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_37815__boxed_1510_, v_as_1504_, v_sz_boxed_1511_, v_i_boxed_1512_, v_b_1507_, v___y_1508_);
lean_dec_ref(v___y_1508_);
lean_dec_ref(v_as_1504_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(uint8_t v___x_1514_, lean_object* v_as_1515_, size_t v_sz_1516_, size_t v_i_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1517_, v_sz_1516_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_b_1518_);
return v___x_1523_;
}
else
{
lean_object* v_snd_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1561_; 
v_snd_1524_ = lean_ctor_get(v_b_1518_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_b_1518_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v_b_1518_, 0);
lean_dec(v_unused_1562_);
v___x_1526_ = v_b_1518_;
v_isShared_1527_ = v_isSharedCheck_1561_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snd_1524_);
lean_dec(v_b_1518_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1561_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_ref_1528_; lean_object* v_a_1529_; lean_object* v_ref_1530_; lean_object* v_msg_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1560_; 
v_ref_1528_ = lean_ctor_get(v___y_1519_, 5);
v_a_1529_ = lean_array_uget(v_as_1515_, v_i_1517_);
v_ref_1530_ = lean_ctor_get(v_a_1529_, 0);
v_msg_1531_ = lean_ctor_get(v_a_1529_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_a_1529_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1533_ = v_a_1529_;
v_isShared_1534_ = v_isSharedCheck_1560_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_msg_1531_);
lean_inc(v_ref_1530_);
lean_dec(v_a_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1560_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v_ref_1552_; lean_object* v___y_1554_; lean_object* v___x_1557_; 
v___x_1535_ = lean_box(0);
v_ref_1552_ = l_Lean_replaceRef(v_ref_1530_, v_ref_1528_);
lean_dec(v_ref_1530_);
v___x_1557_ = l_Lean_Syntax_getPos_x3f(v_ref_1552_, v___x_1514_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_unsigned_to_nat(0u);
v___y_1554_ = v___x_1558_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1559_; 
v_val_1559_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1559_);
lean_dec_ref(v___x_1557_);
v___y_1554_ = v_val_1559_;
goto v___jp_1553_;
}
v___jp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 1, v___y_1538_);
lean_ctor_set(v___x_1526_, 0, v___y_1537_);
v___x_1540_ = v___x_1526_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___y_1537_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___y_1538_);
v___x_1540_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_pos2traces_1544_; lean_object* v___x_1546_; 
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1524_, v___x_1540_, v___x_1541_);
v___x_1543_ = lean_array_push(v___x_1542_, v_msg_1531_);
v_pos2traces_1544_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1524_, v___x_1540_, v___x_1543_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v_pos2traces_1544_);
lean_ctor_set(v___x_1533_, 0, v___x_1535_);
v___x_1546_ = v___x_1533_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_pos2traces_1544_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1517_, v___x_1547_);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_1514_, v_as_1515_, v_sz_1516_, v___x_1548_, v___x_1546_, v___y_1519_);
return v___x_1549_;
}
}
}
v___jp_1553_:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1552_, v___x_1514_);
lean_dec(v_ref_1552_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_inc(v___y_1554_);
v___y_1537_ = v___y_1554_;
v___y_1538_ = v___y_1554_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1556_; 
v_val_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_val_1556_);
lean_dec_ref(v___x_1555_);
v___y_1537_ = v___y_1554_;
v___y_1538_ = v_val_1556_;
goto v___jp_1536_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40___boxed(lean_object* v___x_1563_, lean_object* v_as_1564_, lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v___x_37896__boxed_1571_; size_t v_sz_boxed_1572_; size_t v_i_boxed_1573_; lean_object* v_res_1574_; 
v___x_37896__boxed_1571_ = lean_unbox(v___x_1563_);
v_sz_boxed_1572_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_37896__boxed_1571_, v_as_1564_, v_sz_boxed_1572_, v_i_boxed_1573_, v_b_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec_ref(v_as_1564_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(lean_object* v_init_1575_, uint8_t v___x_1576_, lean_object* v_n_1577_, lean_object* v_b_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
if (lean_obj_tag(v_n_1577_) == 0)
{
lean_object* v_cs_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v_cs_1582_ = lean_ctor_get(v_n_1577_, 0);
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_b_1578_);
v_sz_1585_ = lean_array_size(v_cs_1582_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1575_, v___x_1576_, v_cs_1582_, v_sz_1585_, v___x_1586_, v___x_1584_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1602_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1602_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1602_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v_fst_1592_; 
v_fst_1592_ = lean_ctor_get(v_a_1588_, 0);
if (lean_obj_tag(v_fst_1592_) == 0)
{
lean_object* v_snd_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v_snd_1593_ = lean_ctor_get(v_a_1588_, 1);
lean_inc(v_snd_1593_);
lean_dec(v_a_1588_);
v___x_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_snd_1593_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1594_);
v___x_1596_ = v___x_1590_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1600_; 
lean_inc_ref(v_fst_1592_);
lean_dec(v_a_1588_);
v_val_1598_ = lean_ctor_get(v_fst_1592_, 0);
lean_inc(v_val_1598_);
lean_dec_ref(v_fst_1592_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v_val_1598_);
v___x_1600_ = v___x_1590_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_val_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1587_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1587_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_vs_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; size_t v_sz_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
v_vs_1611_ = lean_ctor_get(v_n_1577_, 0);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v_b_1578_);
v_sz_1614_ = lean_array_size(v_vs_1611_);
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40(v___x_1576_, v_vs_1611_, v_sz_1614_, v___x_1615_, v___x_1613_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1631_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1631_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1631_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_fst_1621_; 
v_fst_1621_ = lean_ctor_get(v_a_1617_, 0);
if (lean_obj_tag(v_fst_1621_) == 0)
{
lean_object* v_snd_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v_snd_1622_ = lean_ctor_get(v_a_1617_, 1);
lean_inc(v_snd_1622_);
lean_dec(v_a_1617_);
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_snd_1622_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1623_);
v___x_1625_ = v___x_1619_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v_val_1627_; lean_object* v___x_1629_; 
lean_inc_ref(v_fst_1621_);
lean_dec(v_a_1617_);
v_val_1627_ = lean_ctor_get(v_fst_1621_, 0);
lean_inc(v_val_1627_);
lean_dec_ref(v_fst_1621_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_val_1627_);
v___x_1629_ = v___x_1619_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_val_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1616_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1616_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(lean_object* v_init_1640_, uint8_t v___x_1641_, lean_object* v_as_1642_, size_t v_sz_1643_, size_t v_i_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_usize_dec_lt(v_i_1644_, v_sz_1643_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_b_1645_);
return v___x_1650_;
}
else
{
lean_object* v_snd_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1685_; 
v_snd_1651_ = lean_ctor_get(v_b_1645_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_b_1645_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v_b_1645_, 0);
lean_dec(v_unused_1686_);
v___x_1653_ = v_b_1645_;
v_isShared_1654_ = v_isSharedCheck_1685_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_snd_1651_);
lean_dec(v_b_1645_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1685_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v_a_1655_; lean_object* v___x_1656_; 
v_a_1655_ = lean_array_uget_borrowed(v_as_1642_, v_i_1644_);
lean_inc(v_snd_1651_);
v___x_1656_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1640_, v___x_1641_, v_a_1655_, v_snd_1651_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1676_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1676_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1676_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
if (lean_obj_tag(v_a_1657_) == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_a_1657_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1661_);
v___x_1663_ = v___x_1653_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_snd_1651_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1663_);
v___x_1665_ = v___x_1659_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_del_object(v___x_1659_);
lean_dec(v_snd_1651_);
v_a_1668_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v_a_1657_);
v___x_1669_ = lean_box(0);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v_a_1668_);
lean_ctor_set(v___x_1653_, 0, v___x_1669_);
v___x_1671_ = v___x_1653_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_a_1668_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
size_t v___x_1672_; size_t v___x_1673_; 
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1644_, v___x_1672_);
v_i_1644_ = v___x_1673_;
v_b_1645_ = v___x_1671_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_del_object(v___x_1653_);
lean_dec(v_snd_1651_);
v_a_1677_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1656_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1656_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39___boxed(lean_object* v_init_1687_, lean_object* v___x_1688_, lean_object* v_as_1689_, lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
uint8_t v___x_37977__boxed_1696_; size_t v_sz_boxed_1697_; size_t v_i_boxed_1698_; lean_object* v_res_1699_; 
v___x_37977__boxed_1696_ = lean_unbox(v___x_1688_);
v_sz_boxed_1697_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1698_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__39(v_init_1687_, v___x_37977__boxed_1696_, v_as_1689_, v_sz_boxed_1697_, v_i_boxed_1698_, v_b_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec_ref(v_as_1689_);
lean_dec_ref(v_init_1687_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27___boxed(lean_object* v_init_1700_, lean_object* v___x_1701_, lean_object* v_n_1702_, lean_object* v_b_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_37997__boxed_1707_; lean_object* v_res_1708_; 
v___x_37997__boxed_1707_ = lean_unbox(v___x_1701_);
v_res_1708_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1700_, v___x_37997__boxed_1707_, v_n_1702_, v_b_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec_ref(v_n_1702_);
lean_dec_ref(v_init_1700_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(uint8_t v___x_1709_, lean_object* v_as_1710_, size_t v_sz_1711_, size_t v_i_1712_, lean_object* v_b_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_lt(v_i_1712_, v_sz_1711_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_b_1713_);
return v___x_1717_;
}
else
{
lean_object* v_snd_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1755_; 
v_snd_1718_ = lean_ctor_get(v_b_1713_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_b_1713_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_b_1713_, 0);
lean_dec(v_unused_1756_);
v___x_1720_ = v_b_1713_;
v_isShared_1721_ = v_isSharedCheck_1755_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_snd_1718_);
lean_dec(v_b_1713_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1755_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_ref_1722_; lean_object* v_a_1723_; lean_object* v_ref_1724_; lean_object* v_msg_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1754_; 
v_ref_1722_ = lean_ctor_get(v___y_1714_, 5);
v_a_1723_ = lean_array_uget(v_as_1710_, v_i_1712_);
v_ref_1724_ = lean_ctor_get(v_a_1723_, 0);
v_msg_1725_ = lean_ctor_get(v_a_1723_, 1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_a_1723_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1727_ = v_a_1723_;
v_isShared_1728_ = v_isSharedCheck_1754_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_msg_1725_);
lean_inc(v_ref_1724_);
lean_dec(v_a_1723_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1754_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v_ref_1746_; lean_object* v___y_1748_; lean_object* v___x_1751_; 
v___x_1729_ = lean_box(0);
v_ref_1746_ = l_Lean_replaceRef(v_ref_1724_, v_ref_1722_);
lean_dec(v_ref_1724_);
v___x_1751_ = l_Lean_Syntax_getPos_x3f(v_ref_1746_, v___x_1709_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_unsigned_to_nat(0u);
v___y_1748_ = v___x_1752_;
goto v___jp_1747_;
}
else
{
lean_object* v_val_1753_; 
v_val_1753_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1753_);
lean_dec_ref(v___x_1751_);
v___y_1748_ = v_val_1753_;
goto v___jp_1747_;
}
v___jp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___y_1732_);
lean_ctor_set(v___x_1720_, 0, v___y_1731_);
v___x_1734_ = v___x_1720_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___y_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___y_1732_);
v___x_1734_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_pos2traces_1738_; lean_object* v___x_1740_; 
v___x_1735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1718_, v___x_1734_, v___x_1735_);
v___x_1737_ = lean_array_push(v___x_1736_, v_msg_1725_);
v_pos2traces_1738_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1718_, v___x_1734_, v___x_1737_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v_pos2traces_1738_);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1740_ = v___x_1727_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_pos2traces_1738_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
size_t v___x_1741_; size_t v___x_1742_; 
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1712_, v___x_1741_);
v_i_1712_ = v___x_1742_;
v_b_1713_ = v___x_1740_;
goto _start;
}
}
}
v___jp_1747_:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1746_, v___x_1709_);
lean_dec(v_ref_1746_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_inc(v___y_1748_);
v___y_1731_ = v___y_1748_;
v___y_1732_ = v___y_1748_;
goto v___jp_1730_;
}
else
{
lean_object* v_val_1750_; 
v_val_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_val_1750_);
lean_dec_ref(v___x_1749_);
v___y_1731_ = v___y_1748_;
v___y_1732_ = v_val_1750_;
goto v___jp_1730_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg___boxed(lean_object* v___x_1757_, lean_object* v_as_1758_, lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v___x_38180__boxed_1764_; size_t v_sz_boxed_1765_; size_t v_i_boxed_1766_; lean_object* v_res_1767_; 
v___x_38180__boxed_1764_ = lean_unbox(v___x_1757_);
v_sz_boxed_1765_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1766_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_38180__boxed_1764_, v_as_1758_, v_sz_boxed_1765_, v_i_boxed_1766_, v_b_1761_, v___y_1762_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v_as_1758_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(uint8_t v___x_1768_, lean_object* v_as_1769_, size_t v_sz_1770_, size_t v_i_1771_, lean_object* v_b_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
uint8_t v___x_1776_; 
v___x_1776_ = lean_usize_dec_lt(v_i_1771_, v_sz_1770_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_b_1772_);
return v___x_1777_;
}
else
{
lean_object* v_snd_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1815_; 
v_snd_1778_ = lean_ctor_get(v_b_1772_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_b_1772_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v_b_1772_, 0);
lean_dec(v_unused_1816_);
v___x_1780_ = v_b_1772_;
v_isShared_1781_ = v_isSharedCheck_1815_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_snd_1778_);
lean_dec(v_b_1772_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1815_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_ref_1782_; lean_object* v_a_1783_; lean_object* v_ref_1784_; lean_object* v_msg_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1814_; 
v_ref_1782_ = lean_ctor_get(v___y_1773_, 5);
v_a_1783_ = lean_array_uget(v_as_1769_, v_i_1771_);
v_ref_1784_ = lean_ctor_get(v_a_1783_, 0);
v_msg_1785_ = lean_ctor_get(v_a_1783_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1787_ = v_a_1783_;
v_isShared_1788_ = v_isSharedCheck_1814_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_msg_1785_);
lean_inc(v_ref_1784_);
lean_dec(v_a_1783_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1814_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v_ref_1806_; lean_object* v___y_1808_; lean_object* v___x_1811_; 
v___x_1789_ = lean_box(0);
v_ref_1806_ = l_Lean_replaceRef(v_ref_1784_, v_ref_1782_);
lean_dec(v_ref_1784_);
v___x_1811_ = l_Lean_Syntax_getPos_x3f(v_ref_1806_, v___x_1768_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___y_1808_ = v___x_1812_;
goto v___jp_1807_;
}
else
{
lean_object* v_val_1813_; 
v_val_1813_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1813_);
lean_dec_ref(v___x_1811_);
v___y_1808_ = v_val_1813_;
goto v___jp_1807_;
}
v___jp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v___y_1792_);
lean_ctor_set(v___x_1780_, 0, v___y_1791_);
v___x_1794_ = v___x_1780_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___y_1791_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___y_1792_);
v___x_1794_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v_pos2traces_1798_; lean_object* v___x_1800_; 
v___x_1795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg___closed__0));
v___x_1796_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_snd_1778_, v___x_1794_, v___x_1795_);
v___x_1797_ = lean_array_push(v___x_1796_, v_msg_1785_);
v_pos2traces_1798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_snd_1778_, v___x_1794_, v___x_1797_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v_pos2traces_1798_);
lean_ctor_set(v___x_1787_, 0, v___x_1789_);
v___x_1800_ = v___x_1787_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_pos2traces_1798_);
v___x_1800_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((size_t)1ULL);
v___x_1802_ = lean_usize_add(v_i_1771_, v___x_1801_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_1768_, v_as_1769_, v_sz_1770_, v___x_1802_, v___x_1800_, v___y_1773_);
return v___x_1803_;
}
}
}
v___jp_1807_:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1806_, v___x_1768_);
lean_dec(v_ref_1806_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_inc(v___y_1808_);
v___y_1791_ = v___y_1808_;
v___y_1792_ = v___y_1808_;
goto v___jp_1790_;
}
else
{
lean_object* v_val_1810_; 
v_val_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_val_1810_);
lean_dec_ref(v___x_1809_);
v___y_1791_ = v___y_1808_;
v___y_1792_ = v_val_1810_;
goto v___jp_1790_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28___boxed(lean_object* v___x_1817_, lean_object* v_as_1818_, lean_object* v_sz_1819_, lean_object* v_i_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v___x_38260__boxed_1825_; size_t v_sz_boxed_1826_; size_t v_i_boxed_1827_; lean_object* v_res_1828_; 
v___x_38260__boxed_1825_ = lean_unbox(v___x_1817_);
v_sz_boxed_1826_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v_i_boxed_1827_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_res_1828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_38260__boxed_1825_, v_as_1818_, v_sz_boxed_1826_, v_i_boxed_1827_, v_b_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_as_1818_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(uint8_t v___x_1829_, lean_object* v_t_1830_, lean_object* v_init_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_root_1835_; lean_object* v_tail_1836_; lean_object* v___x_1837_; 
v_root_1835_ = lean_ctor_get(v_t_1830_, 0);
v_tail_1836_ = lean_ctor_get(v_t_1830_, 1);
lean_inc_ref(v_init_1831_);
v___x_1837_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27(v_init_1831_, v___x_1829_, v_root_1835_, v_init_1831_, v___y_1832_, v___y_1833_);
lean_dec_ref(v_init_1831_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1874_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1874_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1874_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
if (lean_obj_tag(v_a_1838_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; 
v_a_1842_ = lean_ctor_get(v_a_1838_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v_a_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v_a_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; size_t v_sz_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1840_);
v_a_1846_ = lean_ctor_get(v_a_1838_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v_a_1838_);
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v_a_1846_);
v_sz_1849_ = lean_array_size(v_tail_1836_);
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28(v___x_1829_, v_tail_1836_, v_sz_1849_, v___x_1850_, v___x_1848_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1865_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1865_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1865_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v_fst_1856_; 
v_fst_1856_ = lean_ctor_get(v_a_1852_, 0);
if (lean_obj_tag(v_fst_1856_) == 0)
{
lean_object* v_snd_1857_; lean_object* v___x_1859_; 
v_snd_1857_ = lean_ctor_get(v_a_1852_, 1);
lean_inc(v_snd_1857_);
lean_dec(v_a_1852_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_snd_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_snd_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_object* v_val_1861_; lean_object* v___x_1863_; 
lean_inc_ref(v_fst_1856_);
lean_dec(v_a_1852_);
v_val_1861_ = lean_ctor_get(v_fst_1856_, 0);
lean_inc(v_val_1861_);
lean_dec_ref(v_fst_1856_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_val_1861_);
v___x_1863_ = v___x_1854_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_val_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1851_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1851_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1837_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1837_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19___boxed(lean_object* v___x_1883_, lean_object* v_t_1884_, lean_object* v_init_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
uint8_t v___x_38341__boxed_1889_; lean_object* v_res_1890_; 
v___x_38341__boxed_1889_ = lean_unbox(v___x_1883_);
v_res_1890_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_38341__boxed_1889_, v_t_1884_, v_init_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_t_1884_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
if (lean_obj_tag(v_x_1892_) == 0)
{
return v_x_1891_;
}
else
{
lean_object* v_key_1893_; lean_object* v_value_1894_; lean_object* v_tail_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_key_1893_ = lean_ctor_get(v_x_1892_, 0);
v_value_1894_ = lean_ctor_get(v_x_1892_, 1);
v_tail_1895_ = lean_ctor_get(v_x_1892_, 2);
lean_inc(v_value_1894_);
lean_inc(v_key_1893_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_key_1893_);
lean_ctor_set(v___x_1896_, 1, v_value_1894_);
v___x_1897_ = lean_array_push(v_x_1891_, v___x_1896_);
v_x_1891_ = v___x_1897_;
v_x_1892_ = v_tail_1895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22___boxed(lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_x_1899_, v_x_1900_);
lean_dec(v_x_1900_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(lean_object* v_as_1902_, size_t v_i_1903_, size_t v_stop_1904_, lean_object* v_b_1905_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_usize_dec_eq(v_i_1903_, v_stop_1904_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; 
v___x_1907_ = lean_array_uget_borrowed(v_as_1902_, v_i_1903_);
v___x_1908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__22(v_b_1905_, v___x_1907_);
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1903_, v___x_1909_);
v_i_1903_ = v___x_1910_;
v_b_1905_ = v___x_1908_;
goto _start;
}
else
{
return v_b_1905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23___boxed(lean_object* v_as_1912_, lean_object* v_i_1913_, lean_object* v_stop_1914_, lean_object* v_b_1915_){
_start:
{
size_t v_i_boxed_1916_; size_t v_stop_boxed_1917_; lean_object* v_res_1918_; 
v_i_boxed_1916_ = lean_unbox_usize(v_i_1913_);
lean_dec(v_i_1913_);
v_stop_boxed_1917_ = lean_unbox_usize(v_stop_1914_);
lean_dec(v_stop_1914_);
v_res_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_as_1912_, v_i_boxed_1916_, v_stop_boxed_1917_, v_b_1915_);
lean_dec_ref(v_as_1912_);
return v_res_1918_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = lean_unsigned_to_nat(32u);
v___x_1920_ = lean_mk_empty_array_with_capacity(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1(void){
_start:
{
size_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1922_ = ((size_t)5ULL);
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_unsigned_to_nat(32u);
v___x_1925_ = lean_mk_empty_array_with_capacity(v___x_1924_);
v___x_1926_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__0);
v___x_1927_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1925_);
lean_ctor_set(v___x_1927_, 2, v___x_1923_);
lean_ctor_set(v___x_1927_, 3, v___x_1923_);
lean_ctor_set_usize(v___x_1927_, 4, v___x_1922_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v_traceState_1931_; lean_object* v_traces_1932_; lean_object* v___x_1933_; lean_object* v_traceState_1934_; lean_object* v_env_1935_; lean_object* v_nextMacroScope_1936_; lean_object* v_ngen_1937_; lean_object* v_auxDeclNGen_1938_; lean_object* v_cache_1939_; lean_object* v_messages_1940_; lean_object* v_infoState_1941_; lean_object* v_snapshotTasks_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1961_; 
v___x_1930_ = lean_st_ref_get(v___y_1928_);
v_traceState_1931_ = lean_ctor_get(v___x_1930_, 4);
lean_inc_ref(v_traceState_1931_);
lean_dec(v___x_1930_);
v_traces_1932_ = lean_ctor_get(v_traceState_1931_, 0);
lean_inc_ref(v_traces_1932_);
lean_dec_ref(v_traceState_1931_);
v___x_1933_ = lean_st_ref_take(v___y_1928_);
v_traceState_1934_ = lean_ctor_get(v___x_1933_, 4);
v_env_1935_ = lean_ctor_get(v___x_1933_, 0);
v_nextMacroScope_1936_ = lean_ctor_get(v___x_1933_, 1);
v_ngen_1937_ = lean_ctor_get(v___x_1933_, 2);
v_auxDeclNGen_1938_ = lean_ctor_get(v___x_1933_, 3);
v_cache_1939_ = lean_ctor_get(v___x_1933_, 5);
v_messages_1940_ = lean_ctor_get(v___x_1933_, 6);
v_infoState_1941_ = lean_ctor_get(v___x_1933_, 7);
v_snapshotTasks_1942_ = lean_ctor_get(v___x_1933_, 8);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1961_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_snapshotTasks_1942_);
lean_inc(v_infoState_1941_);
lean_inc(v_messages_1940_);
lean_inc(v_cache_1939_);
lean_inc(v_traceState_1934_);
lean_inc(v_auxDeclNGen_1938_);
lean_inc(v_ngen_1937_);
lean_inc(v_nextMacroScope_1936_);
lean_inc(v_env_1935_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1961_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
uint64_t v_tid_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1959_; 
v_tid_1946_ = lean_ctor_get_uint64(v_traceState_1934_, sizeof(void*)*1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_traceState_1934_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v_traceState_1934_, 0);
lean_dec(v_unused_1960_);
v___x_1948_ = v_traceState_1934_;
v_isShared_1949_ = v_isSharedCheck_1959_;
goto v_resetjp_1947_;
}
else
{
lean_dec(v_traceState_1934_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1959_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1950_);
v___x_1952_ = v___x_1948_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1950_);
lean_ctor_set_uint64(v_reuseFailAlloc_1958_, sizeof(void*)*1, v_tid_1946_);
v___x_1952_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_1952_);
v___x_1954_ = v___x_1944_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_env_1935_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_nextMacroScope_1936_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_ngen_1937_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_auxDeclNGen_1938_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1957_, 5, v_cache_1939_);
lean_ctor_set(v_reuseFailAlloc_1957_, 6, v_messages_1940_);
lean_ctor_set(v_reuseFailAlloc_1957_, 7, v_infoState_1941_);
lean_ctor_set(v_reuseFailAlloc_1957_, 8, v_snapshotTasks_1942_);
v___x_1954_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_st_ref_set(v___y_1928_, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v_traces_1932_);
return v___x_1956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___boxed(lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_1962_);
lean_dec(v___y_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(lean_object* v_hi_1965_, lean_object* v_pivot_1966_, lean_object* v_as_1967_, lean_object* v_i_1968_, lean_object* v_k_1969_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_nat_dec_lt(v_k_1969_, v_hi_1965_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_dec(v_k_1969_);
v___x_1971_ = lean_array_fswap(v_as_1967_, v_i_1968_, v_hi_1965_);
v___x_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1972_, 0, v_i_1968_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
return v___x_1972_;
}
else
{
lean_object* v___x_1973_; lean_object* v_fst_1974_; lean_object* v_fst_1975_; lean_object* v_fst_1976_; lean_object* v_fst_1977_; uint8_t v___x_1978_; 
v___x_1973_ = lean_array_fget_borrowed(v_as_1967_, v_k_1969_);
v_fst_1974_ = lean_ctor_get(v___x_1973_, 0);
v_fst_1975_ = lean_ctor_get(v_pivot_1966_, 0);
v_fst_1976_ = lean_ctor_get(v_fst_1974_, 0);
v_fst_1977_ = lean_ctor_get(v_fst_1975_, 0);
v___x_1978_ = lean_nat_dec_lt(v_fst_1976_, v_fst_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_add(v_k_1969_, v___x_1979_);
lean_dec(v_k_1969_);
v_k_1969_ = v___x_1980_;
goto _start;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_array_fswap(v_as_1967_, v_i_1968_, v_k_1969_);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_add(v_i_1968_, v___x_1983_);
lean_dec(v_i_1968_);
v___x_1985_ = lean_nat_add(v_k_1969_, v___x_1983_);
lean_dec(v_k_1969_);
v_as_1967_ = v___x_1982_;
v_i_1968_ = v___x_1984_;
v_k_1969_ = v___x_1985_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg___boxed(lean_object* v_hi_1987_, lean_object* v_pivot_1988_, lean_object* v_as_1989_, lean_object* v_i_1990_, lean_object* v_k_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_1987_, v_pivot_1988_, v_as_1989_, v_i_1990_, v_k_1991_);
lean_dec_ref(v_pivot_1988_);
lean_dec(v_hi_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
lean_object* v_fst_1995_; lean_object* v_fst_1996_; lean_object* v_fst_1997_; lean_object* v_fst_1998_; uint8_t v___x_1999_; 
v_fst_1995_ = lean_ctor_get(v_x_1993_, 0);
v_fst_1996_ = lean_ctor_get(v_x_1994_, 0);
v_fst_1997_ = lean_ctor_get(v_fst_1995_, 0);
v_fst_1998_ = lean_ctor_get(v_fst_1996_, 0);
v___x_1999_ = lean_nat_dec_lt(v_fst_1997_, v_fst_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0___boxed(lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_res_2002_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v_x_2000_, v_x_2001_);
lean_dec_ref(v_x_2001_);
lean_dec_ref(v_x_2000_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(lean_object* v_n_2004_, lean_object* v_as_2005_, lean_object* v_lo_2006_, lean_object* v_hi_2007_){
_start:
{
lean_object* v___y_2009_; uint8_t v___x_2019_; 
v___x_2019_ = lean_nat_dec_lt(v_lo_2006_, v_hi_2007_);
if (v___x_2019_ == 0)
{
lean_dec(v_lo_2006_);
return v_as_2005_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v_mid_2022_; lean_object* v___y_2024_; lean_object* v___y_2030_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2020_ = lean_nat_add(v_lo_2006_, v_hi_2007_);
v___x_2021_ = lean_unsigned_to_nat(1u);
v_mid_2022_ = lean_nat_shiftr(v___x_2020_, v___x_2021_);
lean_dec(v___x_2020_);
v___x_2035_ = lean_array_fget_borrowed(v_as_2005_, v_mid_2022_);
v___x_2036_ = lean_array_fget_borrowed(v_as_2005_, v_lo_2006_);
v___x_2037_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
v___y_2030_ = v_as_2005_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_array_fswap(v_as_2005_, v_lo_2006_, v_mid_2022_);
v___y_2030_ = v___x_2038_;
goto v___jp_2029_;
}
v___jp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = lean_array_fget_borrowed(v___y_2024_, v_mid_2022_);
v___x_2026_ = lean_array_fget_borrowed(v___y_2024_, v_hi_2007_);
v___x_2027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_dec(v_mid_2022_);
v___y_2009_ = v___y_2024_;
goto v___jp_2008_;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_array_fswap(v___y_2024_, v_mid_2022_, v_hi_2007_);
lean_dec(v_mid_2022_);
v___y_2009_ = v___x_2028_;
goto v___jp_2008_;
}
}
v___jp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2031_ = lean_array_fget_borrowed(v___y_2030_, v_hi_2007_);
v___x_2032_ = lean_array_fget_borrowed(v___y_2030_, v_lo_2006_);
v___x_2033_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___lam__0(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
v___y_2024_ = v___y_2030_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_array_fswap(v___y_2030_, v_lo_2006_, v_hi_2007_);
v___y_2024_ = v___x_2034_;
goto v___jp_2023_;
}
}
}
v___jp_2008_:
{
lean_object* v_pivot_2010_; lean_object* v___x_2011_; lean_object* v_fst_2012_; lean_object* v_snd_2013_; uint8_t v___x_2014_; 
v_pivot_2010_ = lean_array_fget(v___y_2009_, v_hi_2007_);
lean_inc_n(v_lo_2006_, 2);
v___x_2011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_2007_, v_pivot_2010_, v___y_2009_, v_lo_2006_, v_lo_2006_);
lean_dec(v_pivot_2010_);
v_fst_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_fst_2012_);
v_snd_2013_ = lean_ctor_get(v___x_2011_, 1);
lean_inc(v_snd_2013_);
lean_dec_ref(v___x_2011_);
v___x_2014_ = lean_nat_dec_le(v_hi_2007_, v_fst_2012_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2004_, v_snd_2013_, v_lo_2006_, v_fst_2012_);
v___x_2016_ = lean_unsigned_to_nat(1u);
v___x_2017_ = lean_nat_add(v_fst_2012_, v___x_2016_);
lean_dec(v_fst_2012_);
v_as_2005_ = v___x_2015_;
v_lo_2006_ = v___x_2017_;
goto _start;
}
else
{
lean_dec(v_fst_2012_);
lean_dec(v_lo_2006_);
return v_snd_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg___boxed(lean_object* v_n_2039_, lean_object* v_as_2040_, lean_object* v_lo_2041_, lean_object* v_hi_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_2039_, v_as_2040_, v_lo_2041_, v_hi_2042_);
lean_dec(v_hi_2042_);
lean_dec(v_n_2039_);
return v_res_2043_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_unsigned_to_nat(16u);
v___x_2046_ = lean_mk_array(v___x_2045_, v___x_2044_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v_pos2traces_2049_; 
v___x_2047_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__0);
v___x_2048_ = lean_unsigned_to_nat(0u);
v_pos2traces_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_pos2traces_2049_, 0, v___x_2048_);
lean_ctor_set(v_pos2traces_2049_, 1, v___x_2047_);
return v_pos2traces_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10(lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_options_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_options_2053_ = lean_ctor_get(v___y_2050_, 2);
v___x_2054_ = l_Lean_trace_profiler_output;
v___x_2055_ = l_Lean_Option_get_x3f___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__15(v_options_2053_, v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2123_; 
v___x_2056_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_2051_);
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2123_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2123_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
uint8_t v___x_2061_; 
v___x_2061_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_2057_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v_pos2traces_2063_; lean_object* v___x_2064_; 
lean_del_object(v___x_2059_);
v___x_2062_ = lean_unsigned_to_nat(0u);
v_pos2traces_2063_ = lean_obj_once(&l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1, &l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1_once, _init_l_Lean_addTraceAsMessages___at___00main_spec__10___closed__1);
v___x_2064_ = l_Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19(v___x_2061_, v_a_2057_, v_pos2traces_2063_, v___y_2050_, v___y_2051_);
lean_dec(v_a_2057_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___y_2067_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2093_; lean_object* v_size_2099_; lean_object* v_buckets_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref(v___x_2064_);
v_size_2099_ = lean_ctor_get(v_a_2065_, 0);
lean_inc(v_size_2099_);
v_buckets_2100_ = lean_ctor_get(v_a_2065_, 1);
lean_inc_ref(v_buckets_2100_);
lean_dec(v_a_2065_);
v___x_2101_ = lean_mk_empty_array_with_capacity(v_size_2099_);
lean_dec(v_size_2099_);
v___x_2102_ = lean_array_get_size(v_buckets_2100_);
v___x_2103_ = lean_nat_dec_lt(v___x_2062_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_dec_ref(v_buckets_2100_);
v___y_2093_ = v___x_2101_;
goto v___jp_2092_;
}
else
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_nat_dec_le(v___x_2102_, v___x_2102_);
if (v___x_2104_ == 0)
{
if (v___x_2103_ == 0)
{
lean_dec_ref(v_buckets_2100_);
v___y_2093_ = v___x_2101_;
goto v___jp_2092_;
}
else
{
size_t v___x_2105_; size_t v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = lean_usize_of_nat(v___x_2102_);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2100_, v___x_2105_, v___x_2106_, v___x_2101_);
lean_dec_ref(v_buckets_2100_);
v___y_2093_ = v___x_2107_;
goto v___jp_2092_;
}
}
else
{
size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = ((size_t)0ULL);
v___x_2109_ = lean_usize_of_nat(v___x_2102_);
v___x_2110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__23(v_buckets_2100_, v___x_2108_, v___x_2109_, v___x_2101_);
lean_dec_ref(v_buckets_2100_);
v___y_2093_ = v___x_2110_;
goto v___jp_2092_;
}
}
v___jp_2066_:
{
lean_object* v___x_2068_; size_t v_sz_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2068_ = lean_box(0);
v_sz_2069_ = lean_array_size(v___y_2067_);
v___x_2070_ = ((size_t)0ULL);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20(v___x_2061_, v___y_2067_, v_sz_2069_, v___x_2070_, v___x_2068_, v___y_2050_, v___y_2051_);
lean_dec_ref(v___y_2067_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2079_);
v___x_2073_ = v___x_2071_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v___x_2071_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2068_);
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2068_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
return v___x_2071_;
}
}
v___jp_2080_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v___y_2082_, v___y_2083_, v___y_2081_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec(v___y_2082_);
v___y_2067_ = v___x_2085_;
goto v___jp_2066_;
}
v___jp_2086_:
{
uint8_t v___x_2091_; 
v___x_2091_ = lean_nat_dec_le(v___y_2090_, v___y_2089_);
if (v___x_2091_ == 0)
{
lean_dec(v___y_2089_);
lean_inc(v___y_2090_);
v___y_2081_ = v___y_2090_;
v___y_2082_ = v___y_2087_;
v___y_2083_ = v___y_2088_;
v___y_2084_ = v___y_2090_;
goto v___jp_2080_;
}
else
{
v___y_2081_ = v___y_2090_;
v___y_2082_ = v___y_2087_;
v___y_2083_ = v___y_2088_;
v___y_2084_ = v___y_2089_;
goto v___jp_2080_;
}
}
v___jp_2092_:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = lean_array_get_size(v___y_2093_);
v___x_2095_ = lean_nat_dec_eq(v___x_2094_, v___x_2062_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2096_ = lean_unsigned_to_nat(1u);
v___x_2097_ = lean_nat_sub(v___x_2094_, v___x_2096_);
v___x_2098_ = lean_nat_dec_le(v___x_2062_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_inc(v___x_2097_);
v___y_2087_ = v___x_2094_;
v___y_2088_ = v___y_2093_;
v___y_2089_ = v___x_2097_;
v___y_2090_ = v___x_2097_;
goto v___jp_2086_;
}
else
{
v___y_2087_ = v___x_2094_;
v___y_2088_ = v___y_2093_;
v___y_2089_ = v___x_2097_;
v___y_2090_ = v___x_2062_;
goto v___jp_2086_;
}
}
else
{
v___y_2067_ = v___y_2093_;
goto v___jp_2066_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2064_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2064_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_dec(v_a_2057_);
v___x_2119_ = lean_box(0);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2119_);
v___x_2121_ = v___x_2059_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2055_, 0);
lean_dec(v_unused_2132_);
v___x_2125_ = v___x_2055_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v___x_2055_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_box(0);
if (v_isShared_2126_ == 0)
{
lean_ctor_set_tag(v___x_2125_, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTraceAsMessages___at___00main_spec__10___boxed(lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(lean_object* v_as_2137_, size_t v_sz_2138_, size_t v_i_2139_, lean_object* v_b_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v___x_2144_; 
v___x_2144_ = lean_usize_dec_lt(v_i_2139_, v_sz_2138_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_b_2140_);
return v___x_2145_;
}
else
{
lean_object* v_options_2146_; lean_object* v_a_2147_; lean_object* v___x_2148_; 
v_options_2146_ = lean_ctor_get(v___y_2141_, 2);
v_a_2147_ = lean_array_uget_borrowed(v_as_2137_, v_i_2139_);
lean_inc_ref(v_options_2146_);
lean_inc(v_a_2147_);
v___x_2148_ = l_Lean_Compiler_LCNF_resumeCompilation(v_a_2147_, v_options_2146_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; 
lean_dec_ref(v___x_2148_);
v___x_2149_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v___x_2150_; size_t v___x_2151_; size_t v___x_2152_; 
lean_dec_ref(v___x_2149_);
v___x_2150_ = lean_box(0);
v___x_2151_ = ((size_t)1ULL);
v___x_2152_ = lean_usize_add(v_i_2139_, v___x_2151_);
v_i_2139_ = v___x_2152_;
v_b_2140_ = v___x_2150_;
goto _start;
}
else
{
return v___x_2149_;
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2148_);
v___x_2155_ = l_Lean_addTraceAsMessages___at___00main_spec__10(v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v___x_2155_, 0);
lean_dec(v_unused_2163_);
v___x_2157_ = v___x_2155_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_dec(v___x_2155_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 1);
lean_ctor_set(v___x_2157_, 0, v_a_2154_);
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2154_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
else
{
lean_dec(v_a_2154_);
return v___x_2155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11___boxed(lean_object* v_as_2164_, lean_object* v_sz_2165_, lean_object* v_i_2166_, lean_object* v_b_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
size_t v_sz_boxed_2171_; size_t v_i_boxed_2172_; lean_object* v_res_2173_; 
v_sz_boxed_2171_ = lean_unbox_usize(v_sz_2165_);
lean_dec(v_sz_2165_);
v_i_boxed_2172_ = lean_unbox_usize(v_i_2166_);
lean_dec(v_i_2166_);
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_as_2164_, v_sz_boxed_2171_, v_i_boxed_2172_, v_b_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec_ref(v_as_2164_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(lean_object* v_as_2174_, size_t v_sz_2175_, size_t v_i_2176_, lean_object* v_b_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_usize_dec_lt(v_i_2176_, v_sz_2175_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_b_2177_);
return v___x_2182_;
}
else
{
lean_object* v_a_2183_; lean_object* v_declNames_2184_; lean_object* v___x_2185_; size_t v_sz_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
v_a_2183_ = lean_array_uget_borrowed(v_as_2174_, v_i_2176_);
v_declNames_2184_ = lean_ctor_get(v_a_2183_, 0);
v___x_2185_ = lean_box(0);
v_sz_2186_ = lean_array_size(v_declNames_2184_);
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__11(v_declNames_2184_, v_sz_2186_, v___x_2187_, v___x_2185_, v___y_2178_, v___y_2179_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v___x_2189_; 
lean_dec_ref(v___x_2188_);
v___x_2189_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v___y_2179_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v_unreported_2191_; lean_object* v___x_2192_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___x_2189_);
v_unreported_2191_ = lean_ctor_get(v_a_2190_, 1);
lean_inc_ref(v_unreported_2191_);
lean_dec(v_a_2190_);
v___x_2192_ = l_Lean_PersistentArray_forIn___at___00main_spec__12(v_unreported_2191_, v___x_2185_, v___y_2178_, v___y_2179_);
lean_dec_ref(v_unreported_2191_);
if (lean_obj_tag(v___x_2192_) == 0)
{
size_t v___x_2193_; size_t v___x_2194_; 
lean_dec_ref(v___x_2192_);
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2176_, v___x_2193_);
v_i_2176_ = v___x_2194_;
v_b_2177_ = v___x_2185_;
goto _start;
}
else
{
return v___x_2192_;
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_a_2196_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2189_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2189_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
return v___x_2188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13___boxed(lean_object* v_as_2204_, lean_object* v_sz_2205_, lean_object* v_i_2206_, lean_object* v_b_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
size_t v_sz_boxed_2211_; size_t v_i_boxed_2212_; lean_object* v_res_2213_; 
v_sz_boxed_2211_ = lean_unbox_usize(v_sz_2205_);
lean_dec(v_sz_2205_);
v_i_boxed_2212_ = lean_unbox_usize(v_i_2206_);
lean_dec(v_i_2206_);
v_res_2213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v_as_2204_, v_sz_boxed_2211_, v_i_boxed_2212_, v_b_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec_ref(v_as_2204_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(lean_object* v_as_2214_, size_t v_i_2215_, size_t v_stop_2216_, lean_object* v_b_2217_){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_usize_dec_eq(v_i_2215_, v_stop_2216_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v_name_2220_; lean_object* v___x_2221_; size_t v___x_2222_; size_t v___x_2223_; 
v___x_2219_ = lean_array_uget_borrowed(v_as_2214_, v_i_2215_);
v_name_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_name_2220_);
v___x_2221_ = l_Lean_Compiler_LCNF_setDeclPublic(v_b_2217_, v_name_2220_);
v___x_2222_ = ((size_t)1ULL);
v___x_2223_ = lean_usize_add(v_i_2215_, v___x_2222_);
v_i_2215_ = v___x_2223_;
v_b_2217_ = v___x_2221_;
goto _start;
}
else
{
return v_b_2217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17___boxed(lean_object* v_as_2225_, lean_object* v_i_2226_, lean_object* v_stop_2227_, lean_object* v_b_2228_){
_start:
{
size_t v_i_boxed_2229_; size_t v_stop_boxed_2230_; lean_object* v_res_2231_; 
v_i_boxed_2229_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_stop_boxed_2230_ = lean_unbox_usize(v_stop_2227_);
lean_dec(v_stop_2227_);
v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v_as_2225_, v_i_boxed_2229_, v_stop_boxed_2230_, v_b_2228_);
lean_dec_ref(v_as_2225_);
return v_res_2231_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(uint8_t v___y_2232_, uint8_t v_suppressElabErrors_2233_, lean_object* v_x_2234_){
_start:
{
if (lean_obj_tag(v_x_2234_) == 1)
{
lean_object* v_pre_2235_; 
v_pre_2235_ = lean_ctor_get(v_x_2234_, 0);
switch(lean_obj_tag(v_pre_2235_))
{
case 1:
{
lean_object* v_pre_2236_; 
v_pre_2236_ = lean_ctor_get(v_pre_2235_, 0);
switch(lean_obj_tag(v_pre_2236_))
{
case 0:
{
lean_object* v_str_2237_; lean_object* v_str_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_str_2237_ = lean_ctor_get(v_x_2234_, 1);
v_str_2238_ = lean_ctor_get(v_pre_2235_, 1);
v___x_2239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__0));
v___x_2240_ = lean_string_dec_eq(v_str_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__1));
v___x_2242_ = lean_string_dec_eq(v_str_2238_, v___x_2241_);
if (v___x_2242_ == 0)
{
return v___y_2232_;
}
else
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__2));
v___x_2244_ = lean_string_dec_eq(v_str_2237_, v___x_2243_);
if (v___x_2244_ == 0)
{
return v___y_2232_;
}
else
{
return v_suppressElabErrors_2233_;
}
}
}
else
{
lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__3));
v___x_2246_ = lean_string_dec_eq(v_str_2237_, v___x_2245_);
if (v___x_2246_ == 0)
{
return v___y_2232_;
}
else
{
return v_suppressElabErrors_2233_;
}
}
}
case 1:
{
lean_object* v_pre_2247_; 
v_pre_2247_ = lean_ctor_get(v_pre_2236_, 0);
if (lean_obj_tag(v_pre_2247_) == 0)
{
lean_object* v_str_2248_; lean_object* v_str_2249_; lean_object* v_str_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v_str_2248_ = lean_ctor_get(v_x_2234_, 1);
v_str_2249_ = lean_ctor_get(v_pre_2235_, 1);
v_str_2250_ = lean_ctor_get(v_pre_2236_, 1);
v___x_2251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__4));
v___x_2252_ = lean_string_dec_eq(v_str_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
return v___y_2232_;
}
else
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__5));
v___x_2254_ = lean_string_dec_eq(v_str_2249_, v___x_2253_);
if (v___x_2254_ == 0)
{
return v___y_2232_;
}
else
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___lam__0___closed__6));
v___x_2256_ = lean_string_dec_eq(v_str_2248_, v___x_2255_);
if (v___x_2256_ == 0)
{
return v___y_2232_;
}
else
{
return v_suppressElabErrors_2233_;
}
}
}
}
else
{
return v___y_2232_;
}
}
default: 
{
return v___y_2232_;
}
}
}
case 0:
{
lean_object* v_str_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v_str_2257_ = lean_ctor_get(v_x_2234_, 1);
v___x_2258_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00main_spec__3_spec__3___closed__0));
v___x_2259_ = lean_string_dec_eq(v_str_2257_, v___x_2258_);
if (v___x_2259_ == 0)
{
return v___y_2232_;
}
else
{
return v_suppressElabErrors_2233_;
}
}
default: 
{
return v___y_2232_;
}
}
}
else
{
return v___y_2232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed(lean_object* v___y_2260_, lean_object* v_suppressElabErrors_2261_, lean_object* v_x_2262_){
_start:
{
uint8_t v___y_38953__boxed_2263_; uint8_t v_suppressElabErrors_boxed_2264_; uint8_t v_res_2265_; lean_object* v_r_2266_; 
v___y_38953__boxed_2263_ = lean_unbox(v___y_2260_);
v_suppressElabErrors_boxed_2264_ = lean_unbox(v_suppressElabErrors_2261_);
v_res_2265_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0(v___y_38953__boxed_2263_, v_suppressElabErrors_boxed_2264_, v_x_2262_);
lean_dec(v_x_2262_);
v_r_2266_ = lean_box(v_res_2265_);
return v_r_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(lean_object* v_ref_2267_, lean_object* v_msgData_2268_, uint8_t v_severity_2269_, uint8_t v_isSilent_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___y_2275_; lean_object* v___y_2276_; uint8_t v___y_2277_; uint8_t v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2311_; uint8_t v___y_2312_; uint8_t v___y_2313_; uint8_t v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2336_; lean_object* v___y_2337_; uint8_t v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; uint8_t v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2347_; uint8_t v___y_2348_; uint8_t v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; uint8_t v___y_2353_; uint8_t v___x_2358_; uint8_t v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; uint8_t v___y_2365_; uint8_t v___y_2366_; uint8_t v___y_2368_; uint8_t v___x_2383_; 
v___x_2358_ = 2;
v___x_2383_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2269_, v___x_2358_);
if (v___x_2383_ == 0)
{
v___y_2368_ = v___x_2383_;
goto v___jp_2367_;
}
else
{
uint8_t v___x_2384_; 
lean_inc_ref(v_msgData_2268_);
v___x_2384_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2268_);
v___y_2368_ = v___x_2384_;
goto v___jp_2367_;
}
v___jp_2274_:
{
lean_object* v___x_2284_; lean_object* v_currNamespace_2285_; lean_object* v_openDecls_2286_; lean_object* v_env_2287_; lean_object* v_nextMacroScope_2288_; lean_object* v_ngen_2289_; lean_object* v_auxDeclNGen_2290_; lean_object* v_traceState_2291_; lean_object* v_cache_2292_; lean_object* v_messages_2293_; lean_object* v_infoState_2294_; lean_object* v_snapshotTasks_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2309_; 
v___x_2284_ = lean_st_ref_take(v___y_2283_);
v_currNamespace_2285_ = lean_ctor_get(v___y_2282_, 6);
v_openDecls_2286_ = lean_ctor_get(v___y_2282_, 7);
v_env_2287_ = lean_ctor_get(v___x_2284_, 0);
v_nextMacroScope_2288_ = lean_ctor_get(v___x_2284_, 1);
v_ngen_2289_ = lean_ctor_get(v___x_2284_, 2);
v_auxDeclNGen_2290_ = lean_ctor_get(v___x_2284_, 3);
v_traceState_2291_ = lean_ctor_get(v___x_2284_, 4);
v_cache_2292_ = lean_ctor_get(v___x_2284_, 5);
v_messages_2293_ = lean_ctor_get(v___x_2284_, 6);
v_infoState_2294_ = lean_ctor_get(v___x_2284_, 7);
v_snapshotTasks_2295_ = lean_ctor_get(v___x_2284_, 8);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2297_ = v___x_2284_;
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_snapshotTasks_2295_);
lean_inc(v_infoState_2294_);
lean_inc(v_messages_2293_);
lean_inc(v_cache_2292_);
lean_inc(v_traceState_2291_);
lean_inc(v_auxDeclNGen_2290_);
lean_inc(v_ngen_2289_);
lean_inc(v_nextMacroScope_2288_);
lean_inc(v_env_2287_);
lean_dec(v___x_2284_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
lean_inc(v_openDecls_2286_);
lean_inc(v_currNamespace_2285_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v_currNamespace_2285_);
lean_ctor_set(v___x_2299_, 1, v_openDecls_2286_);
v___x_2300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___y_2279_);
lean_inc_ref(v___y_2276_);
lean_inc_ref(v___y_2280_);
v___x_2301_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2301_, 0, v___y_2280_);
lean_ctor_set(v___x_2301_, 1, v___y_2275_);
lean_ctor_set(v___x_2301_, 2, v___y_2281_);
lean_ctor_set(v___x_2301_, 3, v___y_2276_);
lean_ctor_set(v___x_2301_, 4, v___x_2300_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*5, v___y_2278_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*5 + 1, v___y_2277_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*5 + 2, v_isSilent_2270_);
v___x_2302_ = l_Lean_MessageLog_add(v___x_2301_, v_messages_2293_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 6, v___x_2302_);
v___x_2304_ = v___x_2297_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_env_2287_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_nextMacroScope_2288_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_ngen_2289_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_auxDeclNGen_2290_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_traceState_2291_);
lean_ctor_set(v_reuseFailAlloc_2308_, 5, v_cache_2292_);
lean_ctor_set(v_reuseFailAlloc_2308_, 6, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2308_, 7, v_infoState_2294_);
lean_ctor_set(v_reuseFailAlloc_2308_, 8, v_snapshotTasks_2295_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_st_ref_set(v___y_2283_, v___x_2304_);
v___x_2306_ = lean_box(0);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
}
v___jp_2310_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2334_; 
v___x_2319_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2268_);
v___x_2320_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v___x_2319_, v___y_2271_, v___y_2272_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2334_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_inc_ref_n(v___y_2315_, 2);
v___x_2325_ = l_Lean_FileMap_toPosition(v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
v___x_2326_ = l_Lean_FileMap_toPosition(v___y_2315_, v___y_2318_);
lean_dec(v___y_2318_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
v___x_2328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__20___closed__1));
if (v___y_2312_ == 0)
{
lean_del_object(v___x_2323_);
lean_dec_ref(v___y_2311_);
v___y_2275_ = v___x_2325_;
v___y_2276_ = v___x_2328_;
v___y_2277_ = v___y_2313_;
v___y_2278_ = v___y_2314_;
v___y_2279_ = v_a_2321_;
v___y_2280_ = v___y_2317_;
v___y_2281_ = v___x_2327_;
v___y_2282_ = v___y_2271_;
v___y_2283_ = v___y_2272_;
goto v___jp_2274_;
}
else
{
uint8_t v___x_2329_; 
lean_inc(v_a_2321_);
v___x_2329_ = l_Lean_MessageData_hasTag(v___y_2311_, v_a_2321_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec_ref(v___x_2327_);
lean_dec_ref(v___x_2325_);
lean_dec(v_a_2321_);
v___x_2330_ = lean_box(0);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2330_);
v___x_2332_ = v___x_2323_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
else
{
lean_del_object(v___x_2323_);
v___y_2275_ = v___x_2325_;
v___y_2276_ = v___x_2328_;
v___y_2277_ = v___y_2313_;
v___y_2278_ = v___y_2314_;
v___y_2279_ = v_a_2321_;
v___y_2280_ = v___y_2317_;
v___y_2281_ = v___x_2327_;
v___y_2282_ = v___y_2271_;
v___y_2283_ = v___y_2272_;
goto v___jp_2274_;
}
}
}
}
v___jp_2335_:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Syntax_getTailPos_x3f(v___y_2337_, v___y_2341_);
lean_dec(v___y_2337_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_inc(v___y_2343_);
v___y_2311_ = v___y_2336_;
v___y_2312_ = v___y_2338_;
v___y_2313_ = v___y_2339_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2340_;
v___y_2316_ = v___y_2343_;
v___y_2317_ = v___y_2342_;
v___y_2318_ = v___y_2343_;
goto v___jp_2310_;
}
else
{
lean_object* v_val_2345_; 
v_val_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_val_2345_);
lean_dec_ref(v___x_2344_);
v___y_2311_ = v___y_2336_;
v___y_2312_ = v___y_2338_;
v___y_2313_ = v___y_2339_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2340_;
v___y_2316_ = v___y_2343_;
v___y_2317_ = v___y_2342_;
v___y_2318_ = v_val_2345_;
goto v___jp_2310_;
}
}
v___jp_2346_:
{
lean_object* v_ref_2354_; lean_object* v___x_2355_; 
v_ref_2354_ = l_Lean_replaceRef(v_ref_2267_, v___y_2351_);
v___x_2355_ = l_Lean_Syntax_getPos_x3f(v_ref_2354_, v___y_2349_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_unsigned_to_nat(0u);
v___y_2336_ = v___y_2347_;
v___y_2337_ = v_ref_2354_;
v___y_2338_ = v___y_2348_;
v___y_2339_ = v___y_2353_;
v___y_2340_ = v___y_2350_;
v___y_2341_ = v___y_2349_;
v___y_2342_ = v___y_2352_;
v___y_2343_ = v___x_2356_;
goto v___jp_2335_;
}
else
{
lean_object* v_val_2357_; 
v_val_2357_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_val_2357_);
lean_dec_ref(v___x_2355_);
v___y_2336_ = v___y_2347_;
v___y_2337_ = v_ref_2354_;
v___y_2338_ = v___y_2348_;
v___y_2339_ = v___y_2353_;
v___y_2340_ = v___y_2350_;
v___y_2341_ = v___y_2349_;
v___y_2342_ = v___y_2352_;
v___y_2343_ = v_val_2357_;
goto v___jp_2335_;
}
}
v___jp_2359_:
{
if (v___y_2366_ == 0)
{
v___y_2347_ = v___y_2364_;
v___y_2348_ = v___y_2360_;
v___y_2349_ = v___y_2365_;
v___y_2350_ = v___y_2361_;
v___y_2351_ = v___y_2362_;
v___y_2352_ = v___y_2363_;
v___y_2353_ = v_severity_2269_;
goto v___jp_2346_;
}
else
{
v___y_2347_ = v___y_2364_;
v___y_2348_ = v___y_2360_;
v___y_2349_ = v___y_2365_;
v___y_2350_ = v___y_2361_;
v___y_2351_ = v___y_2362_;
v___y_2352_ = v___y_2363_;
v___y_2353_ = v___x_2358_;
goto v___jp_2346_;
}
}
v___jp_2367_:
{
if (v___y_2368_ == 0)
{
lean_object* v_fileName_2369_; lean_object* v_fileMap_2370_; lean_object* v_options_2371_; lean_object* v_ref_2372_; uint8_t v_suppressElabErrors_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___f_2376_; uint8_t v___x_2377_; uint8_t v___x_2378_; 
v_fileName_2369_ = lean_ctor_get(v___y_2271_, 0);
v_fileMap_2370_ = lean_ctor_get(v___y_2271_, 1);
v_options_2371_ = lean_ctor_get(v___y_2271_, 2);
v_ref_2372_ = lean_ctor_get(v___y_2271_, 5);
v_suppressElabErrors_2373_ = lean_ctor_get_uint8(v___y_2271_, sizeof(void*)*14 + 1);
v___x_2374_ = lean_box(v___y_2368_);
v___x_2375_ = lean_box(v_suppressElabErrors_2373_);
v___f_2376_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2376_, 0, v___x_2374_);
lean_closure_set(v___f_2376_, 1, v___x_2375_);
v___x_2377_ = 1;
v___x_2378_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2269_, v___x_2377_);
if (v___x_2378_ == 0)
{
v___y_2360_ = v_suppressElabErrors_2373_;
v___y_2361_ = v_fileMap_2370_;
v___y_2362_ = v_ref_2372_;
v___y_2363_ = v_fileName_2369_;
v___y_2364_ = v___f_2376_;
v___y_2365_ = v___y_2368_;
v___y_2366_ = v___x_2378_;
goto v___jp_2359_;
}
else
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = l_Lean_warningAsError;
v___x_2380_ = l_Lean_Option_get___at___00main_spec__8(v_options_2371_, v___x_2379_);
v___y_2360_ = v_suppressElabErrors_2373_;
v___y_2361_ = v_fileMap_2370_;
v___y_2362_ = v_ref_2372_;
v___y_2363_ = v_fileName_2369_;
v___y_2364_ = v___f_2376_;
v___y_2365_ = v___y_2368_;
v___y_2366_ = v___x_2380_;
goto v___jp_2359_;
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v_msgData_2268_);
v___x_2381_ = lean_box(0);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44___boxed(lean_object* v_ref_2385_, lean_object* v_msgData_2386_, lean_object* v_severity_2387_, lean_object* v_isSilent_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v_severity_boxed_2392_; uint8_t v_isSilent_boxed_2393_; lean_object* v_res_2394_; 
v_severity_boxed_2392_ = lean_unbox(v_severity_2387_);
v_isSilent_boxed_2393_ = lean_unbox(v_isSilent_2388_);
v_res_2394_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2385_, v_msgData_2386_, v_severity_boxed_2392_, v_isSilent_boxed_2393_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_ref_2385_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(lean_object* v_msgData_2395_, uint8_t v_severity_2396_, uint8_t v_isSilent_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_ref_2401_; lean_object* v___x_2402_; 
v_ref_2401_ = lean_ctor_get(v___y_2398_, 5);
v___x_2402_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30_spec__44(v_ref_2401_, v_msgData_2395_, v_severity_2396_, v_isSilent_2397_, v___y_2398_, v___y_2399_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30___boxed(lean_object* v_msgData_2403_, lean_object* v_severity_2404_, lean_object* v_isSilent_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v_severity_boxed_2409_; uint8_t v_isSilent_boxed_2410_; lean_object* v_res_2411_; 
v_severity_boxed_2409_ = lean_unbox(v_severity_2404_);
v_isSilent_boxed_2410_ = lean_unbox(v_isSilent_2405_);
v_res_2411_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2403_, v_severity_boxed_2409_, v_isSilent_boxed_2410_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14(lean_object* v_msgData_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
uint8_t v___x_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = 2;
v___x_2417_ = 0;
v___x_2418_ = l_Lean_log___at___00Lean_logError___at___00main_spec__14_spec__30(v_msgData_2412_, v___x_2416_, v___x_2417_, v___y_2413_, v___y_2414_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00main_spec__14___boxed(lean_object* v_msgData_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_logError___at___00main_spec__14(v_msgData_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(lean_object* v_x2_2424_, lean_object* v_as_2425_, size_t v_i_2426_, size_t v_stop_2427_, lean_object* v_b_2428_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_usize_dec_eq(v_i_2426_, v_stop_2427_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; 
v___x_2430_ = lean_array_uget_borrowed(v_as_2425_, v_i_2426_);
lean_inc_ref(v_x2_2424_);
lean_inc(v___x_2430_);
v___x_2431_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2430_, v_x2_2424_, v_b_2428_);
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_add(v_i_2426_, v___x_2432_);
v_i_2426_ = v___x_2433_;
v_b_2428_ = v___x_2431_;
goto _start;
}
else
{
lean_dec_ref(v_x2_2424_);
return v_b_2428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2___boxed(lean_object* v_x2_2435_, lean_object* v_as_2436_, lean_object* v_i_2437_, lean_object* v_stop_2438_, lean_object* v_b_2439_){
_start:
{
size_t v_i_boxed_2440_; size_t v_stop_boxed_2441_; lean_object* v_res_2442_; 
v_i_boxed_2440_ = lean_unbox_usize(v_i_2437_);
lean_dec(v_i_2437_);
v_stop_boxed_2441_ = lean_unbox_usize(v_stop_2438_);
lean_dec(v_stop_2438_);
v_res_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v_x2_2435_, v_as_2436_, v_i_boxed_2440_, v_stop_boxed_2441_, v_b_2439_);
lean_dec_ref(v_as_2436_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(lean_object* v_as_2443_, size_t v_i_2444_, size_t v_stop_2445_, lean_object* v_b_2446_){
_start:
{
lean_object* v___y_2448_; uint8_t v___x_2452_; 
v___x_2452_ = lean_usize_dec_eq(v_i_2444_, v_stop_2445_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v_declNames_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2453_ = lean_array_uget_borrowed(v_as_2443_, v_i_2444_);
v_declNames_2454_ = lean_ctor_get(v___x_2453_, 0);
v___x_2455_ = lean_unsigned_to_nat(0u);
v___x_2456_ = lean_array_get_size(v_declNames_2454_);
v___x_2457_ = lean_nat_dec_lt(v___x_2455_, v___x_2456_);
if (v___x_2457_ == 0)
{
v___y_2448_ = v_b_2446_;
goto v___jp_2447_;
}
else
{
uint8_t v___x_2458_; 
v___x_2458_ = lean_nat_dec_le(v___x_2456_, v___x_2456_);
if (v___x_2458_ == 0)
{
if (v___x_2457_ == 0)
{
v___y_2448_ = v_b_2446_;
goto v___jp_2447_;
}
else
{
size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = ((size_t)0ULL);
v___x_2460_ = lean_usize_of_nat(v___x_2456_);
lean_inc(v___x_2453_);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2453_, v_declNames_2454_, v___x_2459_, v___x_2460_, v_b_2446_);
v___y_2448_ = v___x_2461_;
goto v___jp_2447_;
}
}
else
{
size_t v___x_2462_; size_t v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = ((size_t)0ULL);
v___x_2463_ = lean_usize_of_nat(v___x_2456_);
lean_inc(v___x_2453_);
v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__2(v___x_2453_, v_declNames_2454_, v___x_2462_, v___x_2463_, v_b_2446_);
v___y_2448_ = v___x_2464_;
goto v___jp_2447_;
}
}
}
else
{
return v_b_2446_;
}
v___jp_2447_:
{
size_t v___x_2449_; size_t v___x_2450_; 
v___x_2449_ = ((size_t)1ULL);
v___x_2450_ = lean_usize_add(v_i_2444_, v___x_2449_);
v_i_2444_ = v___x_2450_;
v_b_2446_ = v___y_2448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15___boxed(lean_object* v_as_2465_, lean_object* v_i_2466_, lean_object* v_stop_2467_, lean_object* v_b_2468_){
_start:
{
size_t v_i_boxed_2469_; size_t v_stop_boxed_2470_; lean_object* v_res_2471_; 
v_i_boxed_2469_ = lean_unbox_usize(v_i_2466_);
lean_dec(v_i_2466_);
v_stop_boxed_2470_ = lean_unbox_usize(v_stop_2467_);
lean_dec(v_stop_2467_);
v_res_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v_as_2465_, v_i_boxed_2469_, v_stop_boxed_2470_, v_b_2468_);
lean_dec_ref(v_as_2465_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(lean_object* v_a_2472_, lean_object* v_as_2473_, size_t v_i_2474_, size_t v_stop_2475_, lean_object* v_b_2476_){
_start:
{
lean_object* v___y_2478_; uint8_t v___x_2482_; 
v___x_2482_ = lean_usize_dec_eq(v_i_2474_, v_stop_2475_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v_name_2484_; uint8_t v___x_2485_; 
v___x_2483_ = lean_array_uget_borrowed(v_as_2473_, v_i_2474_);
v_name_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_name_2484_);
lean_inc_ref(v_a_2472_);
v___x_2485_ = l_Lean_isExtern(v_a_2472_, v_name_2484_);
if (v___x_2485_ == 0)
{
v___y_2478_ = v_b_2476_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2486_; 
lean_inc(v___x_2483_);
v___x_2486_ = lean_array_push(v_b_2476_, v___x_2483_);
v___y_2478_ = v___x_2486_;
goto v___jp_2477_;
}
}
else
{
lean_dec_ref(v_a_2472_);
return v_b_2476_;
}
v___jp_2477_:
{
size_t v___x_2479_; size_t v___x_2480_; 
v___x_2479_ = ((size_t)1ULL);
v___x_2480_ = lean_usize_add(v_i_2474_, v___x_2479_);
v_i_2474_ = v___x_2480_;
v_b_2476_ = v___y_2478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19___boxed(lean_object* v_a_2487_, lean_object* v_as_2488_, lean_object* v_i_2489_, lean_object* v_stop_2490_, lean_object* v_b_2491_){
_start:
{
size_t v_i_boxed_2492_; size_t v_stop_boxed_2493_; lean_object* v_res_2494_; 
v_i_boxed_2492_ = lean_unbox_usize(v_i_2489_);
lean_dec(v_i_2489_);
v_stop_boxed_2493_ = lean_unbox_usize(v_stop_2490_);
lean_dec(v_stop_2490_);
v_res_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_2487_, v_as_2488_, v_i_boxed_2492_, v_stop_boxed_2493_, v_b_2491_);
lean_dec_ref(v_as_2488_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(lean_object* v_as_2495_, size_t v_sz_2496_, size_t v_i_2497_, lean_object* v_b_2498_){
_start:
{
uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_lt(v_i_2497_, v_sz_2496_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_b_2498_);
return v___x_2501_;
}
else
{
uint8_t v___x_2502_; lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec_ref(v_b_2498_);
v___x_2502_ = 0;
v_a_2503_ = lean_array_uget_borrowed(v_as_2495_, v_i_2497_);
lean_inc(v_a_2503_);
v___x_2504_ = l_Lean_Message_toString(v_a_2503_, v___x_2502_);
v___x_2505_ = l_IO_eprintln___at___00main_spec__6(v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2506_; size_t v___x_2507_; size_t v___x_2508_; 
lean_dec_ref(v___x_2505_);
v___x_2506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_add(v_i_2497_, v___x_2507_);
v_i_2497_ = v___x_2508_;
v_b_2498_ = v___x_2506_;
goto _start;
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_a_2510_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2505_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2505_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27___boxed(lean_object* v_as_2518_, lean_object* v_sz_2519_, lean_object* v_i_2520_, lean_object* v_b_2521_, lean_object* v___y_2522_){
_start:
{
size_t v_sz_boxed_2523_; size_t v_i_boxed_2524_; lean_object* v_res_2525_; 
v_sz_boxed_2523_ = lean_unbox_usize(v_sz_2519_);
lean_dec(v_sz_2519_);
v_i_boxed_2524_ = lean_unbox_usize(v_i_2520_);
lean_dec(v_i_2520_);
v_res_2525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2518_, v_sz_boxed_2523_, v_i_boxed_2524_, v_b_2521_);
lean_dec_ref(v_as_2518_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(lean_object* v_as_2526_, size_t v_sz_2527_, size_t v_i_2528_, lean_object* v_b_2529_){
_start:
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_usize_dec_lt(v_i_2528_, v_sz_2527_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_b_2529_);
return v___x_2532_;
}
else
{
uint8_t v___x_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref(v_b_2529_);
v___x_2533_ = 0;
v_a_2534_ = lean_array_uget_borrowed(v_as_2526_, v_i_2528_);
lean_inc(v_a_2534_);
v___x_2535_ = l_Lean_Message_toString(v_a_2534_, v___x_2533_);
v___x_2536_ = l_IO_eprintln___at___00main_spec__6(v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2537_; size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
lean_dec_ref(v___x_2536_);
v___x_2537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg___closed__0));
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2528_, v___x_2538_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14_spec__27(v_as_2526_, v_sz_2527_, v___x_2539_, v___x_2537_);
return v___x_2540_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
v_a_2541_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2536_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2536_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14___boxed(lean_object* v_as_2549_, lean_object* v_sz_2550_, lean_object* v_i_2551_, lean_object* v_b_2552_, lean_object* v___y_2553_){
_start:
{
size_t v_sz_boxed_2554_; size_t v_i_boxed_2555_; lean_object* v_res_2556_; 
v_sz_boxed_2554_ = lean_unbox_usize(v_sz_2550_);
lean_dec(v_sz_2550_);
v_i_boxed_2555_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_as_2549_, v_sz_boxed_2554_, v_i_boxed_2555_, v_b_2552_);
lean_dec_ref(v_as_2549_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(lean_object* v_init_2557_, lean_object* v_n_2558_, lean_object* v_b_2559_){
_start:
{
if (lean_obj_tag(v_n_2558_) == 0)
{
lean_object* v_cs_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; size_t v_sz_2564_; size_t v___x_2565_; lean_object* v___x_2566_; 
v_cs_2561_ = lean_ctor_get(v_n_2558_, 0);
v___x_2562_ = lean_box(0);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v_b_2559_);
v_sz_2564_ = lean_array_size(v_cs_2561_);
v___x_2565_ = ((size_t)0ULL);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2557_, v_cs_2561_, v_sz_2564_, v___x_2565_, v___x_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2581_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2581_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2581_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_fst_2571_; 
v_fst_2571_ = lean_ctor_get(v_a_2567_, 0);
if (lean_obj_tag(v_fst_2571_) == 0)
{
lean_object* v_snd_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v_snd_2572_ = lean_ctor_get(v_a_2567_, 1);
lean_inc(v_snd_2572_);
lean_dec(v_a_2567_);
v___x_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_snd_2572_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2573_);
v___x_2575_ = v___x_2569_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
else
{
lean_object* v_val_2577_; lean_object* v___x_2579_; 
lean_inc_ref(v_fst_2571_);
lean_dec(v_a_2567_);
v_val_2577_ = lean_ctor_get(v_fst_2571_, 0);
lean_inc(v_val_2577_);
lean_dec_ref(v_fst_2571_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v_val_2577_);
v___x_2579_ = v___x_2569_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_val_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2582_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2566_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2566_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_object* v_vs_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; size_t v_sz_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
v_vs_2590_ = lean_ctor_get(v_n_2558_, 0);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v_b_2559_);
v_sz_2593_ = lean_array_size(v_vs_2590_);
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__14(v_vs_2590_, v_sz_2593_, v___x_2594_, v___x_2592_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2610_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_fst_2600_; 
v_fst_2600_ = lean_ctor_get(v_a_2596_, 0);
if (lean_obj_tag(v_fst_2600_) == 0)
{
lean_object* v_snd_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v_snd_2601_ = lean_ctor_get(v_a_2596_, 1);
lean_inc(v_snd_2601_);
lean_dec(v_a_2596_);
v___x_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2602_, 0, v_snd_2601_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2602_);
v___x_2604_ = v___x_2598_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
else
{
lean_object* v_val_2606_; lean_object* v___x_2608_; 
lean_inc_ref(v_fst_2600_);
lean_dec(v_a_2596_);
v_val_2606_ = lean_ctor_get(v_fst_2600_, 0);
lean_inc(v_val_2606_);
lean_dec_ref(v_fst_2600_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v_val_2606_);
v___x_2608_ = v___x_2598_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_val_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2595_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2595_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(lean_object* v_init_2619_, lean_object* v_as_2620_, size_t v_sz_2621_, size_t v_i_2622_, lean_object* v_b_2623_){
_start:
{
uint8_t v___x_2625_; 
v___x_2625_ = lean_usize_dec_lt(v_i_2622_, v_sz_2621_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_b_2623_);
return v___x_2626_;
}
else
{
lean_object* v_snd_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2661_; 
v_snd_2627_ = lean_ctor_get(v_b_2623_, 1);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_b_2623_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; 
v_unused_2662_ = lean_ctor_get(v_b_2623_, 0);
lean_dec(v_unused_2662_);
v___x_2629_ = v_b_2623_;
v_isShared_2630_ = v_isSharedCheck_2661_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_snd_2627_);
lean_dec(v_b_2623_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2661_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_a_2631_; lean_object* v___x_2632_; 
v_a_2631_ = lean_array_uget_borrowed(v_as_2620_, v_i_2622_);
lean_inc(v_snd_2627_);
v___x_2632_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2619_, v_a_2631_, v_snd_2627_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2652_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2652_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2652_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
if (lean_obj_tag(v_a_2633_) == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v_a_2633_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2637_);
v___x_2639_ = v___x_2629_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_snd_2627_);
v___x_2639_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2641_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2639_);
v___x_2641_ = v___x_2635_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_del_object(v___x_2635_);
lean_dec(v_snd_2627_);
v_a_2644_ = lean_ctor_get(v_a_2633_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v_a_2633_);
v___x_2645_ = lean_box(0);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v_a_2644_);
lean_ctor_set(v___x_2629_, 0, v___x_2645_);
v___x_2647_ = v___x_2629_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_a_2644_);
v___x_2647_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
size_t v___x_2648_; size_t v___x_2649_; 
v___x_2648_ = ((size_t)1ULL);
v___x_2649_ = lean_usize_add(v_i_2622_, v___x_2648_);
v_i_2622_ = v___x_2649_;
v_b_2623_ = v___x_2647_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_del_object(v___x_2629_);
lean_dec(v_snd_2627_);
v_a_2653_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2632_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2632_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13___boxed(lean_object* v_init_2663_, lean_object* v_as_2664_, lean_object* v_sz_2665_, lean_object* v_i_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_){
_start:
{
size_t v_sz_boxed_2669_; size_t v_i_boxed_2670_; lean_object* v_res_2671_; 
v_sz_boxed_2669_ = lean_unbox_usize(v_sz_2665_);
lean_dec(v_sz_2665_);
v_i_boxed_2670_ = lean_unbox_usize(v_i_2666_);
lean_dec(v_i_2666_);
v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10_spec__13(v_init_2663_, v_as_2664_, v_sz_boxed_2669_, v_i_boxed_2670_, v_b_2667_);
lean_dec_ref(v_as_2664_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10___boxed(lean_object* v_init_2672_, lean_object* v_n_2673_, lean_object* v_b_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2672_, v_n_2673_, v_b_2674_);
lean_dec_ref(v_n_2673_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(lean_object* v_as_2677_, size_t v_sz_2678_, size_t v_i_2679_, lean_object* v_b_2680_){
_start:
{
uint8_t v___x_2682_; 
v___x_2682_ = lean_usize_dec_lt(v_i_2679_, v_sz_2678_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_b_2680_);
return v___x_2683_;
}
else
{
uint8_t v___x_2684_; lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec_ref(v_b_2680_);
v___x_2684_ = 0;
v_a_2685_ = lean_array_uget_borrowed(v_as_2677_, v_i_2679_);
lean_inc(v_a_2685_);
v___x_2686_ = l_Lean_Message_toString(v_a_2685_, v___x_2684_);
v___x_2687_ = l_IO_eprintln___at___00main_spec__6(v___x_2686_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2688_; size_t v___x_2689_; size_t v___x_2690_; 
lean_dec_ref(v___x_2687_);
v___x_2688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2689_ = ((size_t)1ULL);
v___x_2690_ = lean_usize_add(v_i_2679_, v___x_2689_);
v_i_2679_ = v___x_2690_;
v_b_2680_ = v___x_2688_;
goto _start;
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v_a_2692_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2687_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2687_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16___boxed(lean_object* v_as_2700_, lean_object* v_sz_2701_, lean_object* v_i_2702_, lean_object* v_b_2703_, lean_object* v___y_2704_){
_start:
{
size_t v_sz_boxed_2705_; size_t v_i_boxed_2706_; lean_object* v_res_2707_; 
v_sz_boxed_2705_ = lean_unbox_usize(v_sz_2701_);
lean_dec(v_sz_2701_);
v_i_boxed_2706_ = lean_unbox_usize(v_i_2702_);
lean_dec(v_i_2702_);
v_res_2707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2700_, v_sz_boxed_2705_, v_i_boxed_2706_, v_b_2703_);
lean_dec_ref(v_as_2700_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(lean_object* v_as_2708_, size_t v_sz_2709_, size_t v_i_2710_, lean_object* v_b_2711_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_usize_dec_lt(v_i_2710_, v_sz_2709_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v_b_2711_);
return v___x_2714_;
}
else
{
uint8_t v___x_2715_; lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec_ref(v_b_2711_);
v___x_2715_ = 0;
v_a_2716_ = lean_array_uget_borrowed(v_as_2708_, v_i_2710_);
lean_inc(v_a_2716_);
v___x_2717_ = l_Lean_Message_toString(v_a_2716_, v___x_2715_);
v___x_2718_ = l_IO_eprintln___at___00main_spec__6(v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; size_t v___x_2720_; size_t v___x_2721_; lean_object* v___x_2722_; 
lean_dec_ref(v___x_2718_);
v___x_2719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg___closed__0));
v___x_2720_ = ((size_t)1ULL);
v___x_2721_ = lean_usize_add(v_i_2710_, v___x_2720_);
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11_spec__16(v_as_2708_, v_sz_2709_, v___x_2721_, v___x_2719_);
return v___x_2722_;
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_a_2723_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2718_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2718_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11___boxed(lean_object* v_as_2731_, lean_object* v_sz_2732_, lean_object* v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2732_);
lean_dec(v_sz_2732_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_as_2731_, v_sz_boxed_2736_, v_i_boxed_2737_, v_b_2734_);
lean_dec_ref(v_as_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7(lean_object* v_t_2739_, lean_object* v_init_2740_){
_start:
{
lean_object* v_root_2742_; lean_object* v_tail_2743_; lean_object* v___x_2744_; 
v_root_2742_ = lean_ctor_get(v_t_2739_, 0);
v_tail_2743_ = lean_ctor_get(v_t_2739_, 1);
v___x_2744_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__10(v_init_2740_, v_root_2742_, v_init_2740_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2781_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2781_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2781_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
if (lean_obj_tag(v_a_2745_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; 
v_a_2749_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_a_2749_);
lean_dec_ref(v_a_2745_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v_a_2749_);
v___x_2751_ = v___x_2747_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; size_t v_sz_2756_; size_t v___x_2757_; lean_object* v___x_2758_; 
lean_del_object(v___x_2747_);
v_a_2753_ = lean_ctor_get(v_a_2745_, 0);
lean_inc(v_a_2753_);
lean_dec_ref(v_a_2745_);
v___x_2754_ = lean_box(0);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v_a_2753_);
v_sz_2756_ = lean_array_size(v_tail_2743_);
v___x_2757_ = ((size_t)0ULL);
v___x_2758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__7_spec__11(v_tail_2743_, v_sz_2756_, v___x_2757_, v___x_2755_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2772_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2772_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2772_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_fst_2763_; 
v_fst_2763_ = lean_ctor_get(v_a_2759_, 0);
if (lean_obj_tag(v_fst_2763_) == 0)
{
lean_object* v_snd_2764_; lean_object* v___x_2766_; 
v_snd_2764_ = lean_ctor_get(v_a_2759_, 1);
lean_inc(v_snd_2764_);
lean_dec(v_a_2759_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_snd_2764_);
v___x_2766_ = v___x_2761_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_snd_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
else
{
lean_object* v_val_2768_; lean_object* v___x_2770_; 
lean_inc_ref(v_fst_2763_);
lean_dec(v_a_2759_);
v_val_2768_ = lean_ctor_get(v_fst_2763_, 0);
lean_inc(v_val_2768_);
lean_dec_ref(v_fst_2763_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v_val_2768_);
v___x_2770_ = v___x_2761_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_val_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
v_a_2773_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2758_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2758_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2744_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2744_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00main_spec__7___boxed(lean_object* v_t_2790_, lean_object* v_init_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_t_2790_, v_init_2791_);
lean_dec_ref(v_t_2790_);
return v_res_2793_;
}
}
static lean_object* _init_l_main___closed__3(void){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(lean_box(0), lean_box(0), lean_box(0));
return v___x_2797_;
}
}
static lean_object* _init_l_main___closed__4(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2798_ = l_Lean_instInhabitedClassState_default;
v___x_2799_ = lean_box(0);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v___x_2798_);
return v___x_2800_;
}
}
static lean_object* _init_l_main___closed__5(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = l_Lean_Meta_Match_Extension_instInhabitedState;
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v___x_2801_);
return v___x_2803_;
}
}
static lean_object* _init_l_main___closed__6(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((lean_object*)(l_main___closed__2));
v___x_2805_ = ((lean_object*)(l_main___closed__1));
v___x_2806_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_2805_, v___x_2804_);
return v___x_2806_;
}
}
static lean_object* _init_l_main___closed__7(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2808_ = lean_box(0);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v___x_2807_);
return v___x_2809_;
}
}
static lean_object* _init_l_main___closed__8(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_obj_once(&l_main___closed__7, &l_main___closed__7_once, _init_l_main___closed__7);
v___x_2811_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2810_);
return v___x_2811_;
}
}
static lean_object* _init_l_main___closed__9(void){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Array_instInhabited(lean_box(0));
return v___x_2812_;
}
}
static lean_object* _init_l_main___closed__14(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = l_Lean_Options_empty;
v___x_2821_ = l_Lean_Core_getMaxHeartbeats(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l_main___closed__19(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2826_ = ((lean_object*)(l_main___closed__18));
v___x_2827_ = lean_unsigned_to_nat(27u);
v___x_2828_ = lean_unsigned_to_nat(144u);
v___x_2829_ = ((lean_object*)(l_main___closed__17));
v___x_2830_ = ((lean_object*)(l_main___closed__16));
v___x_2831_ = l_mkPanicMessageWithDecl(v___x_2830_, v___x_2829_, v___x_2828_, v___x_2827_, v___x_2826_);
return v___x_2831_;
}
}
static lean_object* _init_l_main___closed__21(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2833_ = ((lean_object*)(l_main___closed__18));
v___x_2834_ = lean_unsigned_to_nat(51u);
v___x_2835_ = lean_unsigned_to_nat(117u);
v___x_2836_ = ((lean_object*)(l_main___closed__17));
v___x_2837_ = ((lean_object*)(l_main___closed__16));
v___x_2838_ = l_mkPanicMessageWithDecl(v___x_2837_, v___x_2836_, v___x_2835_, v___x_2834_, v___x_2833_);
return v___x_2838_;
}
}
static lean_object* _init_l_main___closed__22(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = lean_unsigned_to_nat(1u);
v___x_2840_ = l_Lean_firstFrontendMacroScope;
v___x_2841_ = lean_nat_add(v___x_2840_, v___x_2839_);
return v___x_2841_;
}
}
static lean_object* _init_l_main___closed__26(void){
_start:
{
lean_object* v___x_2848_; uint64_t v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2849_ = 0ULL;
v___x_2850_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set_uint64(v___x_2850_, sizeof(void*)*1, v___x_2849_);
return v___x_2850_;
}
}
static lean_object* _init_l_main___closed__27(void){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2851_;
}
}
static lean_object* _init_l_main___closed__28(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_obj_once(&l_main___closed__27, &l_main___closed__27_once, _init_l_main___closed__27);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
static lean_object* _init_l_main___closed__29(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
return v___x_2855_;
}
}
static lean_object* _init_l_main___closed__30(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = l_Lean_NameSet_empty;
v___x_2857_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
lean_ctor_set(v___x_2858_, 2, v___x_2856_);
return v___x_2858_;
}
}
static lean_object* _init_l_main___closed__31(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; 
v___x_2859_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg___closed__1);
v___x_2860_ = lean_obj_once(&l_main___closed__28, &l_main___closed__28_once, _init_l_main___closed__28);
v___x_2861_ = 1;
v___x_2862_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2860_);
lean_ctor_set(v___x_2862_, 2, v___x_2859_);
lean_ctor_set_uint8(v___x_2862_, sizeof(void*)*3, v___x_2861_);
return v___x_2862_;
}
}
static uint8_t _init_l_main___closed__36(void){
_start:
{
uint8_t v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = 2;
v___x_2870_ = l_Lean_instOrdOLeanLevel_ord(v___x_2869_, v___x_2869_);
return v___x_2870_;
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = 1;
v___x_2872_ = lean_box_uint32(v___x_2871_);
return v___x_2872_;
}
}
static lean_object* _init_l_main___boxed__const__2(void){
_start:
{
uint32_t v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = 0;
v___x_2874_ = lean_box_uint32(v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2875_){
_start:
{
if (lean_obj_tag(v_args_2875_) == 1)
{
lean_object* v_tail_2900_; 
v_tail_2900_ = lean_ctor_get(v_args_2875_, 1);
lean_inc(v_tail_2900_);
if (lean_obj_tag(v_tail_2900_) == 1)
{
lean_object* v_tail_2901_; 
v_tail_2901_ = lean_ctor_get(v_tail_2900_, 1);
lean_inc(v_tail_2901_);
if (lean_obj_tag(v_tail_2901_) == 1)
{
lean_object* v_head_2902_; lean_object* v_head_2903_; lean_object* v_head_2904_; lean_object* v_tail_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_3528_; 
v_head_2902_ = lean_ctor_get(v_args_2875_, 0);
lean_inc(v_head_2902_);
lean_dec_ref(v_args_2875_);
v_head_2903_ = lean_ctor_get(v_tail_2900_, 0);
lean_inc(v_head_2903_);
lean_dec_ref(v_tail_2900_);
v_head_2904_ = lean_ctor_get(v_tail_2901_, 0);
v_tail_2905_ = lean_ctor_get(v_tail_2901_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_tail_2901_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_2907_ = v_tail_2901_;
v_isShared_2908_ = v_isSharedCheck_3528_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_tail_2905_);
lean_inc(v_head_2904_);
lean_dec(v_tail_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_3528_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_ModuleSetup_load(v_head_2902_);
lean_dec(v_head_2902_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v_name_2911_; lean_object* v_options_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref(v___x_2909_);
v_name_2911_ = lean_ctor_get(v_a_2910_, 0);
lean_inc(v_name_2911_);
v_options_2912_ = lean_ctor_get(v_a_2910_, 6);
lean_inc(v_options_2912_);
lean_dec(v_a_2910_);
v___x_2913_ = 0;
v___x_2914_ = l_Lean_LeanOptions_toOptions(v_options_2912_);
v___x_2915_ = lean_box(v___x_2913_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set_tag(v___x_2907_, 0);
lean_ctor_set(v___x_2907_, 1, v___x_2914_);
lean_ctor_set(v___x_2907_, 0, v___x_2915_);
v___x_2917_ = v___x_2907_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v___x_2914_);
v___x_2917_ = v_reuseFailAlloc_3519_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_tail_2905_, v___x_2917_);
lean_dec(v_tail_2905_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2920_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref(v___x_2918_);
v___x_2920_ = l_Lean_getBuildDir();
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
v___x_2922_ = lean_box(0);
v___x_2923_ = l_Lean_initSearchPath(v_a_2921_, v___x_2922_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_fst_2924_; lean_object* v_snd_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref(v___x_2923_);
v_fst_2924_ = lean_ctor_get(v_a_2919_, 0);
v_snd_2925_ = lean_ctor_get(v_a_2919_, 1);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_a_2919_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_2927_ = v_a_2919_;
v_isShared_2928_ = v_isSharedCheck_3494_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_snd_2925_);
lean_inc(v_fst_2924_);
lean_dec(v_a_2919_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_3494_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; uint8_t v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; uint8_t v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v_nextMacroScope_3091_; lean_object* v_ngen_3092_; lean_object* v_auxDeclNGen_3093_; lean_object* v_traceState_3094_; lean_object* v_messages_3095_; lean_object* v_infoState_3096_; lean_object* v_snapshotTasks_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; uint8_t v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; uint8_t v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; uint8_t v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3212_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; uint8_t v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; uint8_t v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; uint8_t v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; uint8_t v___y_3384_; lean_object* v___y_3385_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; uint8_t v___y_3399_; uint8_t v___x_3493_; 
v___x_2929_ = lean_obj_once(&l_main___closed__3, &l_main___closed__3_once, _init_l_main___closed__3);
v___x_2930_ = lean_obj_once(&l_main___closed__4, &l_main___closed__4_once, _init_l_main___closed__4);
v___x_2931_ = lean_obj_once(&l_main___closed__5, &l_main___closed__5_once, _init_l_main___closed__5);
v___x_2932_ = lean_obj_once(&l_main___closed__6, &l_main___closed__6_once, _init_l_main___closed__6);
v___x_2933_ = lean_obj_once(&l_main___closed__8, &l_main___closed__8_once, _init_l_main___closed__8);
v___x_2934_ = lean_obj_once(&l_main___closed__9, &l_main___closed__9_once, _init_l_main___closed__9);
v___x_2935_ = lean_box(1);
v___x_2936_ = ((lean_object*)(l_main___closed__10));
v___x_2937_ = l_Lean_Compiler_compiler_inLeanIR;
v___x_2938_ = 1;
v___x_2939_ = l_Lean_Option_set___at___00Lean_Environment_realizeConst_spec__0(v_snd_2925_, v___x_2937_, v___x_2938_);
v___x_2940_ = l_Lean_maxHeartbeats;
v___x_2941_ = lean_unsigned_to_nat(0u);
v___x_2942_ = l_Lean_Option_set___at___00main_spec__3(v___x_2939_, v___x_2940_, v___x_2941_);
v___x_3232_ = ((lean_object*)(l_main___closed__20));
lean_inc(v_name_2911_);
v___x_3233_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3233_, 0, v_name_2911_);
lean_ctor_set_uint8(v___x_3233_, sizeof(void*)*1, v___x_2938_);
lean_ctor_set_uint8(v___x_3233_, sizeof(void*)*1 + 1, v___x_2938_);
lean_ctor_set_uint8(v___x_3233_, sizeof(void*)*1 + 2, v___x_2938_);
v___x_3234_ = lean_unsigned_to_nat(1u);
v___x_3395_ = lean_mk_empty_array_with_capacity(v___x_3234_);
v___x_3396_ = lean_array_push(v___x_3395_, v___x_3233_);
v___x_3397_ = 2;
v___x_3493_ = lean_uint8_once(&l_main___closed__36, &l_main___closed__36_once, _init_l_main___closed__36);
if (v___x_3493_ == 0)
{
v___y_3399_ = v___x_2938_;
goto v___jp_3398_;
}
else
{
v___y_3399_ = v___x_2913_;
goto v___jp_3398_;
}
v___jp_2943_:
{
lean_object* v___x_2963_; lean_object* v_messages_2964_; lean_object* v_env_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3066_; 
v___x_2963_ = lean_st_ref_get(v___y_2958_);
lean_dec(v___y_2958_);
v_messages_2964_ = lean_ctor_get(v___x_2963_, 6);
v_env_2965_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; lean_object* v_unused_3068_; lean_object* v_unused_3069_; lean_object* v_unused_3070_; lean_object* v_unused_3071_; lean_object* v_unused_3072_; lean_object* v_unused_3073_; 
v_unused_3067_ = lean_ctor_get(v___x_2963_, 8);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v___x_2963_, 7);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v___x_2963_, 5);
lean_dec(v_unused_3069_);
v_unused_3070_ = lean_ctor_get(v___x_2963_, 4);
lean_dec(v_unused_3070_);
v_unused_3071_ = lean_ctor_get(v___x_2963_, 3);
lean_dec(v_unused_3071_);
v_unused_3072_ = lean_ctor_get(v___x_2963_, 2);
lean_dec(v_unused_3072_);
v_unused_3073_ = lean_ctor_get(v___x_2963_, 1);
lean_dec(v_unused_3073_);
v___x_2967_ = v___x_2963_;
v_isShared_2968_ = v_isSharedCheck_3066_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_messages_2964_);
lean_inc(v_env_2965_);
lean_dec(v___x_2963_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3066_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v_unreported_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v_unreported_2969_ = lean_ctor_get(v_messages_2964_, 1);
v___x_2970_ = lean_box(0);
v___x_2971_ = l_Lean_PersistentArray_forIn___at___00main_spec__7(v_unreported_2969_, v___x_2970_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3056_; 
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_2971_, 0);
lean_dec(v_unused_3057_);
v___x_2973_ = v___x_2971_;
v_isShared_2974_ = v_isSharedCheck_3056_;
goto v_resetjp_2972_;
}
else
{
lean_dec(v___x_2971_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3056_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
uint8_t v___x_2975_; 
v___x_2975_ = l_Lean_MessageLog_hasErrors(v_messages_2964_);
lean_dec_ref(v_messages_2964_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; 
lean_del_object(v___x_2973_);
lean_inc_ref(v_env_2965_);
v___x_2976_ = l___private_LeanIR_0__mkIRData(v_env_2965_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref(v___x_2976_);
v___x_2978_ = l_Lean_Environment_mainModule(v_env_2965_);
v___x_2979_ = ((lean_object*)(l_main___closed__12));
v___x_2980_ = l_Lean_Name_append(v___x_2978_, v___x_2979_);
lean_inc(v_head_2903_);
v___x_2981_ = l_Lean_saveModuleData(v_head_2903_, v___x_2980_, v_a_2977_);
lean_dec(v___x_2980_);
if (lean_obj_tag(v___x_2981_) == 0)
{
uint8_t v___x_2982_; lean_object* v___x_2983_; 
lean_dec_ref(v___x_2981_);
v___x_2982_ = 1;
v___x_2983_ = lean_io_prim_handle_mk(v_head_2904_, v___x_2982_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
lean_dec(v_head_2904_);
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref(v___x_2983_);
v___x_2985_ = ((lean_object*)(l_main___closed__13));
v___x_2986_ = l_Lean_Options_empty;
v___x_2987_ = lean_obj_once(&l_main___closed__14, &l_main___closed__14_once, _init_l_main___closed__14);
lean_inc_ref(v___y_2957_);
lean_inc_ref(v___y_2962_);
lean_inc_ref(v___y_2953_);
lean_inc_ref(v___y_2954_);
lean_inc_ref(v___y_2955_);
lean_inc_ref(v___y_2961_);
lean_inc(v___y_2956_);
lean_inc_ref(v_env_2965_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 8, v___y_2957_);
lean_ctor_set(v___x_2967_, 7, v___y_2962_);
lean_ctor_set(v___x_2967_, 6, v___y_2953_);
lean_ctor_set(v___x_2967_, 5, v___y_2954_);
lean_ctor_set(v___x_2967_, 4, v___y_2955_);
lean_ctor_set(v___x_2967_, 3, v___y_2960_);
lean_ctor_set(v___x_2967_, 2, v___y_2961_);
lean_ctor_set(v___x_2967_, 1, v___y_2956_);
v___x_2989_ = v___x_2967_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_env_2965_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___y_2956_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v___y_2961_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v___y_2960_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v___y_2955_);
lean_ctor_set(v_reuseFailAlloc_3013_, 5, v___y_2954_);
lean_ctor_set(v_reuseFailAlloc_3013_, 6, v___y_2953_);
lean_ctor_set(v_reuseFailAlloc_3013_, 7, v___y_2962_);
lean_ctor_set(v_reuseFailAlloc_3013_, 8, v___y_2957_);
v___x_2989_ = v_reuseFailAlloc_3013_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___f_2992_; lean_object* v___x_2993_; 
v___x_2990_ = lean_box(v___x_2913_);
v___x_2991_ = lean_box(v___y_2949_);
lean_inc(v___y_2944_);
lean_inc(v___y_2946_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2950_);
lean_inc_ref(v___y_2945_);
lean_inc(v___y_2951_);
v___f_2992_ = lean_alloc_closure((void*)(l_main___lam__1___boxed), 18, 17);
lean_closure_set(v___f_2992_, 0, v___x_2989_);
lean_closure_set(v___f_2992_, 1, v___y_2951_);
lean_closure_set(v___f_2992_, 2, v___x_2986_);
lean_closure_set(v___f_2992_, 3, v_name_2911_);
lean_closure_set(v___f_2992_, 4, v_a_2984_);
lean_closure_set(v___f_2992_, 5, v___y_2945_);
lean_closure_set(v___f_2992_, 6, v_head_2903_);
lean_closure_set(v___f_2992_, 7, v___y_2950_);
lean_closure_set(v___f_2992_, 8, v___x_2941_);
lean_closure_set(v___f_2992_, 9, v___y_2952_);
lean_closure_set(v___f_2992_, 10, v___y_2948_);
lean_closure_set(v___f_2992_, 11, v___y_2947_);
lean_closure_set(v___f_2992_, 12, v___x_2987_);
lean_closure_set(v___f_2992_, 13, v___y_2946_);
lean_closure_set(v___f_2992_, 14, v___y_2944_);
lean_closure_set(v___f_2992_, 15, v___x_2990_);
lean_closure_set(v___f_2992_, 16, v___x_2991_);
v___x_2993_ = l_Lean_profileitIOUnsafe___redArg(v___x_2985_, v___x_2942_, v___f_2992_, v___y_2959_);
lean_dec_ref(v___x_2942_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v___x_2994_; uint8_t v___x_2995_; 
lean_dec_ref(v___x_2993_);
v___x_2994_ = lean_display_cumulative_profiling_times();
v___x_2995_ = lean_unbox(v_fst_2924_);
lean_dec(v_fst_2924_);
if (v___x_2995_ == 0)
{
lean_dec_ref(v_env_2965_);
goto v___jp_2897_;
}
else
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Environment_displayStats(v_env_2965_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_dec_ref(v___x_2996_);
goto v___jp_2897_;
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v_env_2965_);
lean_dec(v_fst_2924_);
v_a_3005_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2993_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2993_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_dec_ref(v___x_2983_);
lean_del_object(v___x_2967_);
lean_dec_ref(v_env_2965_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2903_);
v___x_3014_ = ((lean_object*)(l_main___closed__15));
v___x_3015_ = lean_string_append(v___x_3014_, v_head_2904_);
lean_dec(v_head_2904_);
v___x_3016_ = ((lean_object*)(l___private_LeanIR_0__setConfigOption___closed__5));
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
v___x_3018_ = l_IO_eprintln___at___00main_spec__6(v___x_3017_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3026_; 
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v___x_3018_, 0);
lean_dec(v_unused_3027_);
v___x_3020_ = v___x_3018_;
v_isShared_3021_ = v_isSharedCheck_3026_;
goto v_resetjp_3019_;
}
else
{
lean_dec(v___x_3018_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3026_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3022_ = l_main___boxed__const__1;
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3022_);
v___x_3024_ = v___x_3020_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
v_a_3028_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3018_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3018_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_del_object(v___x_2967_);
lean_dec_ref(v_env_2965_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3036_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_2981_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_2981_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_del_object(v___x_2967_);
lean_dec_ref(v_env_2965_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3044_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2976_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_2976_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
lean_del_object(v___x_2967_);
lean_dec_ref(v_env_2965_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v___x_3052_ = l_main___boxed__const__1;
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_3052_);
v___x_3054_ = v___x_2973_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_del_object(v___x_2967_);
lean_dec_ref(v_env_2965_);
lean_dec_ref(v_messages_2964_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3058_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2971_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2971_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
v___jp_3074_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; size_t v_sz_3108_; size_t v___x_3109_; lean_object* v___x_3110_; 
lean_inc_ref(v___y_3098_);
v___x_3105_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3105_, 0, v___y_3104_);
lean_ctor_set(v___x_3105_, 1, v_nextMacroScope_3091_);
lean_ctor_set(v___x_3105_, 2, v_ngen_3092_);
lean_ctor_set(v___x_3105_, 3, v_auxDeclNGen_3093_);
lean_ctor_set(v___x_3105_, 4, v_traceState_3094_);
lean_ctor_set(v___x_3105_, 5, v___y_3098_);
lean_ctor_set(v___x_3105_, 6, v_messages_3095_);
lean_ctor_set(v___x_3105_, 7, v_infoState_3096_);
lean_ctor_set(v___x_3105_, 8, v_snapshotTasks_3097_);
v___x_3106_ = lean_st_ref_set(v___y_3087_, v___x_3105_);
v___x_3107_ = lean_box(0);
v_sz_3108_ = lean_array_size(v___y_3103_);
v___x_3109_ = ((size_t)0ULL);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00main_spec__13(v___y_3103_, v_sz_3108_, v___x_3109_, v___x_3107_, v___y_3099_, v___y_3087_);
lean_dec_ref(v___y_3103_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_dec_ref(v___x_3110_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3087_);
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3077_;
v___y_2947_ = v___y_3078_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3080_;
v___y_2950_ = v___y_3081_;
v___y_2951_ = v___y_3082_;
v___y_2952_ = v___y_3083_;
v___y_2953_ = v___y_3084_;
v___y_2954_ = v___y_3098_;
v___y_2955_ = v___y_3100_;
v___y_2956_ = v___y_3085_;
v___y_2957_ = v___y_3101_;
v___y_2958_ = v___y_3086_;
v___y_2959_ = v___y_3102_;
v___y_2960_ = v___y_3088_;
v___y_2961_ = v___y_3089_;
v___y_2962_ = v___y_3090_;
goto v___jp_2943_;
}
else
{
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_dec_ref(v___x_3110_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3087_);
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3077_;
v___y_2947_ = v___y_3078_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3080_;
v___y_2950_ = v___y_3081_;
v___y_2951_ = v___y_3082_;
v___y_2952_ = v___y_3083_;
v___y_2953_ = v___y_3084_;
v___y_2954_ = v___y_3098_;
v___y_2955_ = v___y_3100_;
v___y_2956_ = v___y_3085_;
v___y_2957_ = v___y_3101_;
v___y_2958_ = v___y_3086_;
v___y_2959_ = v___y_3102_;
v___y_2960_ = v___y_3088_;
v___y_2961_ = v___y_3089_;
v___y_2962_ = v___y_3090_;
goto v___jp_2943_;
}
else
{
lean_object* v_a_3111_; uint8_t v___x_3112_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref(v___x_3110_);
v___x_3112_ = l_Lean_Exception_isInterrupt(v_a_3111_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = l_Lean_Exception_toMessageData(v_a_3111_);
v___x_3114_ = l_Lean_logError___at___00main_spec__14(v___x_3113_, v___y_3099_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3099_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_dec_ref(v___x_3114_);
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3077_;
v___y_2947_ = v___y_3078_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3080_;
v___y_2950_ = v___y_3081_;
v___y_2951_ = v___y_3082_;
v___y_2952_ = v___y_3083_;
v___y_2953_ = v___y_3084_;
v___y_2954_ = v___y_3098_;
v___y_2955_ = v___y_3100_;
v___y_2956_ = v___y_3085_;
v___y_2957_ = v___y_3101_;
v___y_2958_ = v___y_3086_;
v___y_2959_ = v___y_3102_;
v___y_2960_ = v___y_3088_;
v___y_2961_ = v___y_3089_;
v___y_2962_ = v___y_3090_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec_ref(v___x_3114_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3086_);
lean_dec(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v___x_3115_ = lean_obj_once(&l_main___closed__19, &l_main___closed__19_once, _init_l_main___closed__19);
v___x_3116_ = l_panic___at___00main_spec__5(v___x_3115_);
return v___x_3116_;
}
}
else
{
lean_dec(v_a_3111_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3087_);
v___y_2944_ = v___y_3075_;
v___y_2945_ = v___y_3076_;
v___y_2946_ = v___y_3077_;
v___y_2947_ = v___y_3078_;
v___y_2948_ = v___y_3079_;
v___y_2949_ = v___y_3080_;
v___y_2950_ = v___y_3081_;
v___y_2951_ = v___y_3082_;
v___y_2952_ = v___y_3083_;
v___y_2953_ = v___y_3084_;
v___y_2954_ = v___y_3098_;
v___y_2955_ = v___y_3100_;
v___y_2956_ = v___y_3085_;
v___y_2957_ = v___y_3101_;
v___y_2958_ = v___y_3086_;
v___y_2959_ = v___y_3102_;
v___y_2960_ = v___y_3088_;
v___y_2961_ = v___y_3089_;
v___y_2962_ = v___y_3090_;
goto v___jp_2943_;
}
}
}
}
v___jp_3117_:
{
lean_object* v___x_3142_; lean_object* v_fileName_3143_; lean_object* v_fileMap_3144_; lean_object* v_currRecDepth_3145_; lean_object* v_ref_3146_; lean_object* v_currNamespace_3147_; lean_object* v_openDecls_3148_; lean_object* v_initHeartbeats_3149_; lean_object* v_maxHeartbeats_3150_; lean_object* v_quotContext_3151_; lean_object* v_currMacroScope_3152_; lean_object* v_cancelTk_x3f_3153_; uint8_t v_suppressElabErrors_3154_; lean_object* v_inheritedTraceOptions_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3185_; 
v___x_3142_ = lean_st_ref_take(v___y_3141_);
v_fileName_3143_ = lean_ctor_get(v___y_3140_, 0);
v_fileMap_3144_ = lean_ctor_get(v___y_3140_, 1);
v_currRecDepth_3145_ = lean_ctor_get(v___y_3140_, 3);
v_ref_3146_ = lean_ctor_get(v___y_3140_, 5);
v_currNamespace_3147_ = lean_ctor_get(v___y_3140_, 6);
v_openDecls_3148_ = lean_ctor_get(v___y_3140_, 7);
v_initHeartbeats_3149_ = lean_ctor_get(v___y_3140_, 8);
v_maxHeartbeats_3150_ = lean_ctor_get(v___y_3140_, 9);
v_quotContext_3151_ = lean_ctor_get(v___y_3140_, 10);
v_currMacroScope_3152_ = lean_ctor_get(v___y_3140_, 11);
v_cancelTk_x3f_3153_ = lean_ctor_get(v___y_3140_, 12);
v_suppressElabErrors_3154_ = lean_ctor_get_uint8(v___y_3140_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3155_ = lean_ctor_get(v___y_3140_, 13);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___y_3140_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; lean_object* v_unused_3187_; 
v_unused_3186_ = lean_ctor_get(v___y_3140_, 4);
lean_dec(v_unused_3186_);
v_unused_3187_ = lean_ctor_get(v___y_3140_, 2);
lean_dec(v_unused_3187_);
v___x_3157_ = v___y_3140_;
v_isShared_3158_ = v_isSharedCheck_3185_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_inheritedTraceOptions_3155_);
lean_inc(v_cancelTk_x3f_3153_);
lean_inc(v_currMacroScope_3152_);
lean_inc(v_quotContext_3151_);
lean_inc(v_maxHeartbeats_3150_);
lean_inc(v_initHeartbeats_3149_);
lean_inc(v_openDecls_3148_);
lean_inc(v_currNamespace_3147_);
lean_inc(v_ref_3146_);
lean_inc(v_currRecDepth_3145_);
lean_inc(v_fileMap_3144_);
lean_inc(v_fileName_3143_);
lean_dec(v___y_3140_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3185_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v_env_3159_; lean_object* v_nextMacroScope_3160_; lean_object* v_ngen_3161_; lean_object* v_auxDeclNGen_3162_; lean_object* v_traceState_3163_; lean_object* v_messages_3164_; lean_object* v_infoState_3165_; lean_object* v_snapshotTasks_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
v_env_3159_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_ref(v_env_3159_);
v_nextMacroScope_3160_ = lean_ctor_get(v___x_3142_, 1);
lean_inc(v_nextMacroScope_3160_);
v_ngen_3161_ = lean_ctor_get(v___x_3142_, 2);
lean_inc_ref(v_ngen_3161_);
v_auxDeclNGen_3162_ = lean_ctor_get(v___x_3142_, 3);
lean_inc_ref(v_auxDeclNGen_3162_);
v_traceState_3163_ = lean_ctor_get(v___x_3142_, 4);
lean_inc_ref(v_traceState_3163_);
v_messages_3164_ = lean_ctor_get(v___x_3142_, 6);
lean_inc_ref(v_messages_3164_);
v_infoState_3165_ = lean_ctor_get(v___x_3142_, 7);
lean_inc_ref(v_infoState_3165_);
v_snapshotTasks_3166_ = lean_ctor_get(v___x_3142_, 8);
lean_inc_ref(v_snapshotTasks_3166_);
lean_dec(v___x_3142_);
v___x_3167_ = l_Lean_maxRecDepth;
v___x_3168_ = l_Lean_Option_get___at___00main_spec__9(v___x_2942_, v___x_3167_);
lean_inc_ref(v___x_2942_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 4, v___x_3168_);
lean_ctor_set(v___x_3157_, 2, v___x_2942_);
v___x_3170_ = v___x_3157_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_fileName_3143_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_fileMap_3144_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_currRecDepth_3145_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3184_, 5, v_ref_3146_);
lean_ctor_set(v_reuseFailAlloc_3184_, 6, v_currNamespace_3147_);
lean_ctor_set(v_reuseFailAlloc_3184_, 7, v_openDecls_3148_);
lean_ctor_set(v_reuseFailAlloc_3184_, 8, v_initHeartbeats_3149_);
lean_ctor_set(v_reuseFailAlloc_3184_, 9, v_maxHeartbeats_3150_);
lean_ctor_set(v_reuseFailAlloc_3184_, 10, v_quotContext_3151_);
lean_ctor_set(v_reuseFailAlloc_3184_, 11, v_currMacroScope_3152_);
lean_ctor_set(v_reuseFailAlloc_3184_, 12, v_cancelTk_x3f_3153_);
lean_ctor_set(v_reuseFailAlloc_3184_, 13, v_inheritedTraceOptions_3155_);
lean_ctor_set_uint8(v_reuseFailAlloc_3184_, sizeof(void*)*14 + 1, v_suppressElabErrors_3154_);
v___x_3170_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; uint8_t v___x_3172_; 
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*14, v___y_3127_);
v___x_3171_ = lean_array_get_size(v___y_3138_);
v___x_3172_ = lean_nat_dec_lt(v___x_2941_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; 
lean_inc_ref(v___y_3139_);
v___x_3173_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3139_, v_env_3159_, v___x_2935_);
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3120_;
v___y_3078_ = v___y_3121_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3123_;
v___y_3081_ = v___y_3124_;
v___y_3082_ = v___y_3125_;
v___y_3083_ = v___y_3126_;
v___y_3084_ = v___y_3128_;
v___y_3085_ = v___y_3129_;
v___y_3086_ = v___y_3130_;
v___y_3087_ = v___y_3141_;
v___y_3088_ = v___y_3131_;
v___y_3089_ = v___y_3132_;
v___y_3090_ = v___y_3133_;
v_nextMacroScope_3091_ = v_nextMacroScope_3160_;
v_ngen_3092_ = v_ngen_3161_;
v_auxDeclNGen_3093_ = v_auxDeclNGen_3162_;
v_traceState_3094_ = v_traceState_3163_;
v_messages_3095_ = v_messages_3164_;
v_infoState_3096_ = v_infoState_3165_;
v_snapshotTasks_3097_ = v_snapshotTasks_3166_;
v___y_3098_ = v___y_3134_;
v___y_3099_ = v___x_3170_;
v___y_3100_ = v___y_3135_;
v___y_3101_ = v___y_3136_;
v___y_3102_ = v___y_3137_;
v___y_3103_ = v___y_3138_;
v___y_3104_ = v___x_3173_;
goto v___jp_3074_;
}
else
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_nat_dec_le(v___x_3171_, v___x_3171_);
if (v___x_3174_ == 0)
{
if (v___x_3172_ == 0)
{
lean_object* v___x_3175_; 
lean_inc_ref(v___y_3139_);
v___x_3175_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3139_, v_env_3159_, v___x_2935_);
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3120_;
v___y_3078_ = v___y_3121_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3123_;
v___y_3081_ = v___y_3124_;
v___y_3082_ = v___y_3125_;
v___y_3083_ = v___y_3126_;
v___y_3084_ = v___y_3128_;
v___y_3085_ = v___y_3129_;
v___y_3086_ = v___y_3130_;
v___y_3087_ = v___y_3141_;
v___y_3088_ = v___y_3131_;
v___y_3089_ = v___y_3132_;
v___y_3090_ = v___y_3133_;
v_nextMacroScope_3091_ = v_nextMacroScope_3160_;
v_ngen_3092_ = v_ngen_3161_;
v_auxDeclNGen_3093_ = v_auxDeclNGen_3162_;
v_traceState_3094_ = v_traceState_3163_;
v_messages_3095_ = v_messages_3164_;
v_infoState_3096_ = v_infoState_3165_;
v_snapshotTasks_3097_ = v_snapshotTasks_3166_;
v___y_3098_ = v___y_3134_;
v___y_3099_ = v___x_3170_;
v___y_3100_ = v___y_3135_;
v___y_3101_ = v___y_3136_;
v___y_3102_ = v___y_3137_;
v___y_3103_ = v___y_3138_;
v___y_3104_ = v___x_3175_;
goto v___jp_3074_;
}
else
{
size_t v___x_3176_; size_t v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3176_ = ((size_t)0ULL);
v___x_3177_ = lean_usize_of_nat(v___x_3171_);
v___x_3178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3138_, v___x_3176_, v___x_3177_, v___x_2935_);
lean_inc_ref(v___y_3139_);
v___x_3179_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3139_, v_env_3159_, v___x_3178_);
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3120_;
v___y_3078_ = v___y_3121_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3123_;
v___y_3081_ = v___y_3124_;
v___y_3082_ = v___y_3125_;
v___y_3083_ = v___y_3126_;
v___y_3084_ = v___y_3128_;
v___y_3085_ = v___y_3129_;
v___y_3086_ = v___y_3130_;
v___y_3087_ = v___y_3141_;
v___y_3088_ = v___y_3131_;
v___y_3089_ = v___y_3132_;
v___y_3090_ = v___y_3133_;
v_nextMacroScope_3091_ = v_nextMacroScope_3160_;
v_ngen_3092_ = v_ngen_3161_;
v_auxDeclNGen_3093_ = v_auxDeclNGen_3162_;
v_traceState_3094_ = v_traceState_3163_;
v_messages_3095_ = v_messages_3164_;
v_infoState_3096_ = v_infoState_3165_;
v_snapshotTasks_3097_ = v_snapshotTasks_3166_;
v___y_3098_ = v___y_3134_;
v___y_3099_ = v___x_3170_;
v___y_3100_ = v___y_3135_;
v___y_3101_ = v___y_3136_;
v___y_3102_ = v___y_3137_;
v___y_3103_ = v___y_3138_;
v___y_3104_ = v___x_3179_;
goto v___jp_3074_;
}
}
else
{
size_t v___x_3180_; size_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3180_ = ((size_t)0ULL);
v___x_3181_ = lean_usize_of_nat(v___x_3171_);
v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__15(v___y_3138_, v___x_3180_, v___x_3181_, v___x_2935_);
lean_inc_ref(v___y_3139_);
v___x_3183_ = l_Lean_SimplePersistentEnvExtension_setState___redArg(v___y_3139_, v_env_3159_, v___x_3182_);
v___y_3075_ = v___y_3118_;
v___y_3076_ = v___y_3119_;
v___y_3077_ = v___y_3120_;
v___y_3078_ = v___y_3121_;
v___y_3079_ = v___y_3122_;
v___y_3080_ = v___y_3123_;
v___y_3081_ = v___y_3124_;
v___y_3082_ = v___y_3125_;
v___y_3083_ = v___y_3126_;
v___y_3084_ = v___y_3128_;
v___y_3085_ = v___y_3129_;
v___y_3086_ = v___y_3130_;
v___y_3087_ = v___y_3141_;
v___y_3088_ = v___y_3131_;
v___y_3089_ = v___y_3132_;
v___y_3090_ = v___y_3133_;
v_nextMacroScope_3091_ = v_nextMacroScope_3160_;
v_ngen_3092_ = v_ngen_3161_;
v_auxDeclNGen_3093_ = v_auxDeclNGen_3162_;
v_traceState_3094_ = v_traceState_3163_;
v_messages_3095_ = v_messages_3164_;
v_infoState_3096_ = v_infoState_3165_;
v_snapshotTasks_3097_ = v_snapshotTasks_3166_;
v___y_3098_ = v___y_3134_;
v___y_3099_ = v___x_3170_;
v___y_3100_ = v___y_3135_;
v___y_3101_ = v___y_3136_;
v___y_3102_ = v___y_3137_;
v___y_3103_ = v___y_3138_;
v___y_3104_ = v___x_3183_;
goto v___jp_3074_;
}
}
}
}
}
v___jp_3188_:
{
if (v___y_3212_ == 0)
{
lean_object* v___x_3213_; lean_object* v_env_3214_; lean_object* v_nextMacroScope_3215_; lean_object* v_ngen_3216_; lean_object* v_auxDeclNGen_3217_; lean_object* v_traceState_3218_; lean_object* v_messages_3219_; lean_object* v_infoState_3220_; lean_object* v_snapshotTasks_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3230_; 
v___x_3213_ = lean_st_ref_take(v___y_3201_);
v_env_3214_ = lean_ctor_get(v___x_3213_, 0);
v_nextMacroScope_3215_ = lean_ctor_get(v___x_3213_, 1);
v_ngen_3216_ = lean_ctor_get(v___x_3213_, 2);
v_auxDeclNGen_3217_ = lean_ctor_get(v___x_3213_, 3);
v_traceState_3218_ = lean_ctor_get(v___x_3213_, 4);
v_messages_3219_ = lean_ctor_get(v___x_3213_, 6);
v_infoState_3220_ = lean_ctor_get(v___x_3213_, 7);
v_snapshotTasks_3221_ = lean_ctor_get(v___x_3213_, 8);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v___x_3213_, 5);
lean_dec(v_unused_3231_);
v___x_3223_ = v___x_3213_;
v_isShared_3224_ = v_isSharedCheck_3230_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_snapshotTasks_3221_);
lean_inc(v_infoState_3220_);
lean_inc(v_messages_3219_);
lean_inc(v_traceState_3218_);
lean_inc(v_auxDeclNGen_3217_);
lean_inc(v_ngen_3216_);
lean_inc(v_nextMacroScope_3215_);
lean_inc(v_env_3214_);
lean_dec(v___x_3213_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3230_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3225_ = l_Lean_Kernel_enableDiag(v_env_3214_, v___y_3198_);
lean_inc_ref(v___y_3206_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 5, v___y_3206_);
lean_ctor_set(v___x_3223_, 0, v___x_3225_);
v___x_3227_ = v___x_3223_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_nextMacroScope_3215_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_ngen_3216_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_auxDeclNGen_3217_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_traceState_3218_);
lean_ctor_set(v_reuseFailAlloc_3229_, 5, v___y_3206_);
lean_ctor_set(v_reuseFailAlloc_3229_, 6, v_messages_3219_);
lean_ctor_set(v_reuseFailAlloc_3229_, 7, v_infoState_3220_);
lean_ctor_set(v_reuseFailAlloc_3229_, 8, v_snapshotTasks_3221_);
v___x_3227_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_st_ref_set(v___y_3201_, v___x_3227_);
lean_inc(v___y_3201_);
v___y_3118_ = v___y_3189_;
v___y_3119_ = v___y_3190_;
v___y_3120_ = v___y_3191_;
v___y_3121_ = v___y_3192_;
v___y_3122_ = v___y_3193_;
v___y_3123_ = v___y_3194_;
v___y_3124_ = v___y_3195_;
v___y_3125_ = v___y_3196_;
v___y_3126_ = v___y_3197_;
v___y_3127_ = v___y_3198_;
v___y_3128_ = v___y_3199_;
v___y_3129_ = v___y_3200_;
v___y_3130_ = v___y_3201_;
v___y_3131_ = v___y_3202_;
v___y_3132_ = v___y_3204_;
v___y_3133_ = v___y_3205_;
v___y_3134_ = v___y_3206_;
v___y_3135_ = v___y_3207_;
v___y_3136_ = v___y_3208_;
v___y_3137_ = v___y_3209_;
v___y_3138_ = v___y_3211_;
v___y_3139_ = v___y_3210_;
v___y_3140_ = v___y_3203_;
v___y_3141_ = v___y_3201_;
goto v___jp_3117_;
}
}
}
else
{
lean_inc(v___y_3201_);
v___y_3118_ = v___y_3189_;
v___y_3119_ = v___y_3190_;
v___y_3120_ = v___y_3191_;
v___y_3121_ = v___y_3192_;
v___y_3122_ = v___y_3193_;
v___y_3123_ = v___y_3194_;
v___y_3124_ = v___y_3195_;
v___y_3125_ = v___y_3196_;
v___y_3126_ = v___y_3197_;
v___y_3127_ = v___y_3198_;
v___y_3128_ = v___y_3199_;
v___y_3129_ = v___y_3200_;
v___y_3130_ = v___y_3201_;
v___y_3131_ = v___y_3202_;
v___y_3132_ = v___y_3204_;
v___y_3133_ = v___y_3205_;
v___y_3134_ = v___y_3206_;
v___y_3135_ = v___y_3207_;
v___y_3136_ = v___y_3208_;
v___y_3137_ = v___y_3209_;
v___y_3138_ = v___y_3211_;
v___y_3139_ = v___y_3210_;
v___y_3140_ = v___y_3203_;
v___y_3141_ = v___y_3201_;
goto v___jp_3117_;
}
}
v___jp_3235_:
{
lean_object* v___x_3245_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 1, v___y_3243_);
lean_ctor_set(v___x_2927_, 0, v___y_3238_);
v___x_3245_ = v___x_2927_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___y_3238_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___y_3243_);
v___x_3245_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v_moduleData_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3246_ = lean_box(0);
lean_inc_ref(v___y_3241_);
v___x_3247_ = l_Lean_EnvExtension_setState___redArg(v___y_3241_, v___y_3237_, v___x_3245_, v___x_3246_);
v___x_3248_ = l_Lean_Environment_header(v___x_3247_);
v_moduleData_3249_ = lean_ctor_get(v___x_3248_, 6);
lean_inc_ref(v_moduleData_3249_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = lean_array_get_size(v_moduleData_3249_);
v___x_3251_ = lean_nat_dec_lt(v___y_3240_, v___x_3250_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec_ref(v_moduleData_3249_);
lean_dec_ref(v___x_3247_);
lean_dec(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec(v___y_3236_);
lean_dec_ref(v___x_2942_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v___x_3252_ = lean_obj_once(&l_main___closed__21, &l_main___closed__21_once, _init_l_main___closed__21);
v___x_3253_ = l_panic___at___00main_spec__5(v___x_3252_);
return v___x_3253_;
}
else
{
lean_object* v_base_3254_; lean_object* v_private_3255_; lean_object* v_header_3256_; lean_object* v_serverBaseExts_3257_; lean_object* v_checked_3258_; lean_object* v_asyncConstsMap_3259_; lean_object* v_asyncCtx_x3f_3260_; lean_object* v_importRealizationCtx_x3f_3261_; lean_object* v_localRealizationCtxMap_3262_; lean_object* v_allRealizations_3263_; uint8_t v_isExporting_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3338_; 
v_base_3254_ = lean_ctor_get(v___x_3247_, 0);
lean_inc_ref(v_base_3254_);
v_private_3255_ = lean_ctor_get(v_base_3254_, 0);
lean_inc(v_private_3255_);
v_header_3256_ = lean_ctor_get(v_private_3255_, 5);
lean_inc_ref(v_header_3256_);
v_serverBaseExts_3257_ = lean_ctor_get(v___x_3247_, 1);
v_checked_3258_ = lean_ctor_get(v___x_3247_, 2);
v_asyncConstsMap_3259_ = lean_ctor_get(v___x_3247_, 3);
v_asyncCtx_x3f_3260_ = lean_ctor_get(v___x_3247_, 4);
v_importRealizationCtx_x3f_3261_ = lean_ctor_get(v___x_3247_, 5);
v_localRealizationCtxMap_3262_ = lean_ctor_get(v___x_3247_, 6);
v_allRealizations_3263_ = lean_ctor_get(v___x_3247_, 7);
v_isExporting_3264_ = lean_ctor_get_uint8(v___x_3247_, sizeof(void*)*8);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v___x_3247_, 0);
lean_dec(v_unused_3339_);
v___x_3266_ = v___x_3247_;
v_isShared_3267_ = v_isSharedCheck_3338_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_allRealizations_3263_);
lean_inc(v_localRealizationCtxMap_3262_);
lean_inc(v_importRealizationCtx_x3f_3261_);
lean_inc(v_asyncCtx_x3f_3260_);
lean_inc(v_asyncConstsMap_3259_);
lean_inc(v_checked_3258_);
lean_inc(v_serverBaseExts_3257_);
lean_dec(v___x_3247_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3338_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v_public_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3336_; 
v_public_3268_ = lean_ctor_get(v_base_3254_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_base_3254_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v_base_3254_, 0);
lean_dec(v_unused_3337_);
v___x_3270_ = v_base_3254_;
v_isShared_3271_ = v_isSharedCheck_3336_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_public_3268_);
lean_dec(v_base_3254_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3336_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v_constants_3272_; uint8_t v_quotInit_3273_; lean_object* v_diagnostics_3274_; lean_object* v_const2ModIdx_3275_; lean_object* v_extensions_3276_; lean_object* v_irBaseExts_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3334_; 
v_constants_3272_ = lean_ctor_get(v_private_3255_, 0);
v_quotInit_3273_ = lean_ctor_get_uint8(v_private_3255_, sizeof(void*)*6);
v_diagnostics_3274_ = lean_ctor_get(v_private_3255_, 1);
v_const2ModIdx_3275_ = lean_ctor_get(v_private_3255_, 2);
v_extensions_3276_ = lean_ctor_get(v_private_3255_, 3);
v_irBaseExts_3277_ = lean_ctor_get(v_private_3255_, 4);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_private_3255_);
if (v_isSharedCheck_3334_ == 0)
{
lean_object* v_unused_3335_; 
v_unused_3335_ = lean_ctor_get(v_private_3255_, 5);
lean_dec(v_unused_3335_);
v___x_3279_ = v_private_3255_;
v_isShared_3280_ = v_isSharedCheck_3334_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_irBaseExts_3277_);
lean_inc(v_extensions_3276_);
lean_inc(v_const2ModIdx_3275_);
lean_inc(v_diagnostics_3274_);
lean_inc(v_constants_3272_);
lean_dec(v_private_3255_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3334_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
uint32_t v_trustLevel_3281_; lean_object* v_mainModule_3282_; uint8_t v_isModule_3283_; lean_object* v_regions_3284_; lean_object* v_modules_3285_; lean_object* v_moduleName2Idx_3286_; lean_object* v_importAllModules_3287_; lean_object* v_moduleData_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3332_; 
v_trustLevel_3281_ = lean_ctor_get_uint32(v_header_3256_, sizeof(void*)*7);
v_mainModule_3282_ = lean_ctor_get(v_header_3256_, 0);
v_isModule_3283_ = lean_ctor_get_uint8(v_header_3256_, sizeof(void*)*7 + 4);
v_regions_3284_ = lean_ctor_get(v_header_3256_, 2);
v_modules_3285_ = lean_ctor_get(v_header_3256_, 3);
v_moduleName2Idx_3286_ = lean_ctor_get(v_header_3256_, 4);
v_importAllModules_3287_ = lean_ctor_get(v_header_3256_, 5);
v_moduleData_3288_ = lean_ctor_get(v_header_3256_, 6);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_header_3256_);
if (v_isSharedCheck_3332_ == 0)
{
lean_object* v_unused_3333_; 
v_unused_3333_ = lean_ctor_get(v_header_3256_, 1);
lean_dec(v_unused_3333_);
v___x_3290_ = v_header_3256_;
v_isShared_3291_ = v_isSharedCheck_3332_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_moduleData_3288_);
lean_inc(v_importAllModules_3287_);
lean_inc(v_moduleName2Idx_3286_);
lean_inc(v_modules_3285_);
lean_inc(v_regions_3284_);
lean_inc(v_mainModule_3282_);
lean_dec(v_header_3256_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3332_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; lean_object* v_imports_3293_; lean_object* v___x_3295_; 
v___x_3292_ = lean_array_fget(v_moduleData_3249_, v___y_3240_);
lean_dec_ref(v_moduleData_3249_);
v_imports_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc_ref(v_imports_3293_);
lean_dec(v___x_3292_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 1, v_imports_3293_);
v___x_3295_ = v___x_3290_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 7, 5);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_mainModule_3282_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_imports_3293_);
lean_ctor_set(v_reuseFailAlloc_3331_, 2, v_regions_3284_);
lean_ctor_set(v_reuseFailAlloc_3331_, 3, v_modules_3285_);
lean_ctor_set(v_reuseFailAlloc_3331_, 4, v_moduleName2Idx_3286_);
lean_ctor_set(v_reuseFailAlloc_3331_, 5, v_importAllModules_3287_);
lean_ctor_set(v_reuseFailAlloc_3331_, 6, v_moduleData_3288_);
lean_ctor_set_uint32(v_reuseFailAlloc_3331_, sizeof(void*)*7, v_trustLevel_3281_);
lean_ctor_set_uint8(v_reuseFailAlloc_3331_, sizeof(void*)*7 + 4, v_isModule_3283_);
v___x_3295_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 5, v___x_3295_);
v___x_3297_ = v___x_3279_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_constants_3272_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_diagnostics_3274_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v_const2ModIdx_3275_);
lean_ctor_set(v_reuseFailAlloc_3330_, 3, v_extensions_3276_);
lean_ctor_set(v_reuseFailAlloc_3330_, 4, v_irBaseExts_3277_);
lean_ctor_set(v_reuseFailAlloc_3330_, 5, v___x_3295_);
lean_ctor_set_uint8(v_reuseFailAlloc_3330_, sizeof(void*)*6, v_quotInit_3273_);
v___x_3297_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3299_; 
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v___x_3297_);
v___x_3299_ = v___x_3270_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_public_3268_);
v___x_3299_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3301_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3299_);
v___x_3301_ = v___x_3266_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3328_, 1, v_serverBaseExts_3257_);
lean_ctor_set(v_reuseFailAlloc_3328_, 2, v_checked_3258_);
lean_ctor_set(v_reuseFailAlloc_3328_, 3, v_asyncConstsMap_3259_);
lean_ctor_set(v_reuseFailAlloc_3328_, 4, v_asyncCtx_x3f_3260_);
lean_ctor_set(v_reuseFailAlloc_3328_, 5, v_importRealizationCtx_x3f_3261_);
lean_ctor_set(v_reuseFailAlloc_3328_, 6, v_localRealizationCtxMap_3262_);
lean_ctor_set(v_reuseFailAlloc_3328_, 7, v_allRealizations_3263_);
lean_ctor_set_uint8(v_reuseFailAlloc_3328_, sizeof(void*)*8, v_isExporting_3264_);
v___x_3301_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v_env_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; uint8_t v___x_3327_; 
v___x_3302_ = l_Lean_Compiler_LCNF_postponedCompileDeclsExt;
v___x_3303_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2936_, v___x_3302_, v___x_3301_, v___y_3240_, v___y_3242_);
lean_dec(v___y_3240_);
v___x_3304_ = l_Lean_firstFrontendMacroScope;
v___x_3305_ = lean_obj_once(&l_main___closed__22, &l_main___closed__22_once, _init_l_main___closed__22);
v___x_3306_ = ((lean_object*)(l_main___closed__25));
lean_inc_n(v___y_3239_, 3);
v___x_3307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3307_, 0, v___y_3239_);
lean_ctor_set(v___x_3307_, 1, v___x_3234_);
lean_ctor_set(v___x_3307_, 2, v___x_2922_);
v___x_3308_ = lean_obj_once(&l_main___closed__26, &l_main___closed__26_once, _init_l_main___closed__26);
v___x_3309_ = lean_obj_once(&l_main___closed__29, &l_main___closed__29_once, _init_l_main___closed__29);
v___x_3310_ = lean_obj_once(&l_main___closed__30, &l_main___closed__30_once, _init_l_main___closed__30);
v___x_3311_ = lean_obj_once(&l_main___closed__31, &l_main___closed__31_once, _init_l_main___closed__31);
v___x_3312_ = ((lean_object*)(l_main___closed__32));
lean_inc_ref(v___x_3307_);
v___x_3313_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3301_);
lean_ctor_set(v___x_3313_, 1, v___x_3305_);
lean_ctor_set(v___x_3313_, 2, v___x_3306_);
lean_ctor_set(v___x_3313_, 3, v___x_3307_);
lean_ctor_set(v___x_3313_, 4, v___x_3308_);
lean_ctor_set(v___x_3313_, 5, v___x_3309_);
lean_ctor_set(v___x_3313_, 6, v___x_3310_);
lean_ctor_set(v___x_3313_, 7, v___x_3311_);
lean_ctor_set(v___x_3313_, 8, v___x_3312_);
v___x_3314_ = lean_st_mk_ref(v___x_3313_);
v___x_3315_ = l_Lean_inheritedTraceOptions;
v___x_3316_ = lean_st_ref_get(v___x_3315_);
v___x_3317_ = lean_st_ref_get(v___x_3314_);
v___x_3318_ = l_Lean_instInhabitedFileMap_default;
v___x_3319_ = lean_unsigned_to_nat(1000u);
v___x_3320_ = lean_box(0);
v___x_3321_ = l_Lean_Core_getMaxHeartbeats(v___x_2942_);
v___x_3322_ = lean_box(0);
lean_inc_ref(v___x_2942_);
lean_inc(v_head_2903_);
v___x_3323_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3323_, 0, v_head_2903_);
lean_ctor_set(v___x_3323_, 1, v___x_3318_);
lean_ctor_set(v___x_3323_, 2, v___x_2942_);
lean_ctor_set(v___x_3323_, 3, v___x_2941_);
lean_ctor_set(v___x_3323_, 4, v___x_3319_);
lean_ctor_set(v___x_3323_, 5, v___x_3320_);
lean_ctor_set(v___x_3323_, 6, v___y_3239_);
lean_ctor_set(v___x_3323_, 7, v___x_2922_);
lean_ctor_set(v___x_3323_, 8, v___x_2941_);
lean_ctor_set(v___x_3323_, 9, v___x_3321_);
lean_ctor_set(v___x_3323_, 10, v___y_3239_);
lean_ctor_set(v___x_3323_, 11, v___x_3304_);
lean_ctor_set(v___x_3323_, 12, v___x_3322_);
lean_ctor_set(v___x_3323_, 13, v___x_3316_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*14, v___x_2913_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*14 + 1, v___x_2913_);
v_env_3324_ = lean_ctor_get(v___x_3317_, 0);
lean_inc_ref(v_env_3324_);
lean_dec(v___x_3317_);
v___x_3325_ = l_Lean_diagnostics;
v___x_3326_ = l_Lean_Option_get___at___00main_spec__8(v___x_2942_, v___x_3325_);
v___x_3327_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3324_);
lean_dec_ref(v_env_3324_);
if (v___x_3327_ == 0)
{
if (v___x_3326_ == 0)
{
v___y_3189_ = v___x_3322_;
v___y_3190_ = v___x_3309_;
v___y_3191_ = v___x_3304_;
v___y_3192_ = v___x_2922_;
v___y_3193_ = v___y_3236_;
v___y_3194_ = v___x_3251_;
v___y_3195_ = v___x_3318_;
v___y_3196_ = v___x_3315_;
v___y_3197_ = v___x_3320_;
v___y_3198_ = v___x_3326_;
v___y_3199_ = v___x_3310_;
v___y_3200_ = v___x_3305_;
v___y_3201_ = v___x_3314_;
v___y_3202_ = v___x_3307_;
v___y_3203_ = v___x_3323_;
v___y_3204_ = v___x_3306_;
v___y_3205_ = v___x_3311_;
v___y_3206_ = v___x_3309_;
v___y_3207_ = v___x_3308_;
v___y_3208_ = v___x_3312_;
v___y_3209_ = v___y_3239_;
v___y_3210_ = v___x_3302_;
v___y_3211_ = v___x_3303_;
v___y_3212_ = v___x_3251_;
goto v___jp_3188_;
}
else
{
v___y_3189_ = v___x_3322_;
v___y_3190_ = v___x_3309_;
v___y_3191_ = v___x_3304_;
v___y_3192_ = v___x_2922_;
v___y_3193_ = v___y_3236_;
v___y_3194_ = v___x_3251_;
v___y_3195_ = v___x_3318_;
v___y_3196_ = v___x_3315_;
v___y_3197_ = v___x_3320_;
v___y_3198_ = v___x_3326_;
v___y_3199_ = v___x_3310_;
v___y_3200_ = v___x_3305_;
v___y_3201_ = v___x_3314_;
v___y_3202_ = v___x_3307_;
v___y_3203_ = v___x_3323_;
v___y_3204_ = v___x_3306_;
v___y_3205_ = v___x_3311_;
v___y_3206_ = v___x_3309_;
v___y_3207_ = v___x_3308_;
v___y_3208_ = v___x_3312_;
v___y_3209_ = v___y_3239_;
v___y_3210_ = v___x_3302_;
v___y_3211_ = v___x_3303_;
v___y_3212_ = v___x_3327_;
goto v___jp_3188_;
}
}
else
{
v___y_3189_ = v___x_3322_;
v___y_3190_ = v___x_3309_;
v___y_3191_ = v___x_3304_;
v___y_3192_ = v___x_2922_;
v___y_3193_ = v___y_3236_;
v___y_3194_ = v___x_3251_;
v___y_3195_ = v___x_3318_;
v___y_3196_ = v___x_3315_;
v___y_3197_ = v___x_3320_;
v___y_3198_ = v___x_3326_;
v___y_3199_ = v___x_3310_;
v___y_3200_ = v___x_3305_;
v___y_3201_ = v___x_3314_;
v___y_3202_ = v___x_3307_;
v___y_3203_ = v___x_3323_;
v___y_3204_ = v___x_3306_;
v___y_3205_ = v___x_3311_;
v___y_3206_ = v___x_3309_;
v___y_3207_ = v___x_3308_;
v___y_3208_ = v___x_3312_;
v___y_3209_ = v___y_3239_;
v___y_3210_ = v___x_3302_;
v___y_3211_ = v___x_3303_;
v___y_3212_ = v___x_3326_;
goto v___jp_3188_;
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
v___jp_3341_:
{
lean_object* v___x_3347_; lean_object* v_toEnvExtension_3348_; lean_object* v_asyncMode_3349_; lean_object* v___x_3350_; lean_object* v_importedEntries_3351_; lean_object* v_state_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3347_ = l_Lean_IR_declMapExt;
v_toEnvExtension_3348_ = lean_ctor_get(v___x_3347_, 0);
v_asyncMode_3349_ = lean_ctor_get(v_toEnvExtension_3348_, 2);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3346_);
v___x_3350_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2933_, v_toEnvExtension_3348_, v___y_3346_, v_asyncMode_3349_, v___y_3344_);
v_importedEntries_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc_ref(v_importedEntries_3351_);
v_state_3352_ = lean_ctor_get(v___x_3350_, 1);
lean_inc(v_state_3352_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_array_get_borrowed(v___x_2934_, v_importedEntries_3351_, v___y_3343_);
v___x_3354_ = lean_array_get_size(v___x_3353_);
v___x_3355_ = lean_nat_dec_lt(v___x_2941_, v___x_3354_);
if (v___x_3355_ == 0)
{
v___y_3236_ = v___y_3342_;
v___y_3237_ = v___y_3346_;
v___y_3238_ = v_importedEntries_3351_;
v___y_3239_ = v___y_3344_;
v___y_3240_ = v___y_3343_;
v___y_3241_ = v_toEnvExtension_3348_;
v___y_3242_ = v___y_3345_;
v___y_3243_ = v_state_3352_;
goto v___jp_3235_;
}
else
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_nat_dec_le(v___x_3354_, v___x_3354_);
if (v___x_3356_ == 0)
{
if (v___x_3355_ == 0)
{
v___y_3236_ = v___y_3342_;
v___y_3237_ = v___y_3346_;
v___y_3238_ = v_importedEntries_3351_;
v___y_3239_ = v___y_3344_;
v___y_3240_ = v___y_3343_;
v___y_3241_ = v_toEnvExtension_3348_;
v___y_3242_ = v___y_3345_;
v___y_3243_ = v_state_3352_;
goto v___jp_3235_;
}
else
{
size_t v___x_3357_; size_t v___x_3358_; lean_object* v___x_3359_; 
v___x_3357_ = ((size_t)0ULL);
v___x_3358_ = lean_usize_of_nat(v___x_3354_);
lean_inc_ref(v___y_3346_);
v___x_3359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3346_, v___x_3353_, v___x_3357_, v___x_3358_, v_state_3352_);
v___y_3236_ = v___y_3342_;
v___y_3237_ = v___y_3346_;
v___y_3238_ = v_importedEntries_3351_;
v___y_3239_ = v___y_3344_;
v___y_3240_ = v___y_3343_;
v___y_3241_ = v_toEnvExtension_3348_;
v___y_3242_ = v___y_3345_;
v___y_3243_ = v___x_3359_;
goto v___jp_3235_;
}
}
else
{
size_t v___x_3360_; size_t v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = ((size_t)0ULL);
v___x_3361_ = lean_usize_of_nat(v___x_3354_);
lean_inc_ref(v___y_3346_);
v___x_3362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__16(v___y_3346_, v___x_3353_, v___x_3360_, v___x_3361_, v_state_3352_);
v___y_3236_ = v___y_3342_;
v___y_3237_ = v___y_3346_;
v___y_3238_ = v_importedEntries_3351_;
v___y_3239_ = v___y_3344_;
v___y_3240_ = v___y_3343_;
v___y_3241_ = v_toEnvExtension_3348_;
v___y_3242_ = v___y_3345_;
v___y_3243_ = v___x_3362_;
goto v___jp_3235_;
}
}
}
v___jp_3363_:
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_nat_dec_lt(v___x_2941_, v___y_3366_);
if (v___x_3371_ == 0)
{
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3368_;
v___y_3344_ = v___y_3367_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___y_3370_;
goto v___jp_3341_;
}
else
{
uint8_t v___x_3372_; 
v___x_3372_ = lean_nat_dec_le(v___y_3366_, v___y_3366_);
if (v___x_3372_ == 0)
{
if (v___x_3371_ == 0)
{
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3368_;
v___y_3344_ = v___y_3367_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___y_3370_;
goto v___jp_3341_;
}
else
{
size_t v___x_3373_; size_t v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = ((size_t)0ULL);
v___x_3374_ = lean_usize_of_nat(v___y_3366_);
lean_dec(v___y_3366_);
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3365_, v___x_3373_, v___x_3374_, v___y_3370_);
lean_dec_ref(v___y_3365_);
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3368_;
v___y_3344_ = v___y_3367_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___x_3375_;
goto v___jp_3341_;
}
}
else
{
size_t v___x_3376_; size_t v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = ((size_t)0ULL);
v___x_3377_ = lean_usize_of_nat(v___y_3366_);
lean_dec(v___y_3366_);
v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__17(v___y_3365_, v___x_3376_, v___x_3377_, v___y_3370_);
lean_dec_ref(v___y_3365_);
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3368_;
v___y_3344_ = v___y_3367_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___x_3378_;
goto v___jp_3341_;
}
}
}
v___jp_3379_:
{
lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3386_ = lean_array_get_size(v___y_3385_);
v___x_3387_ = lean_nat_dec_lt(v___x_2941_, v___x_3386_);
if (v___x_3387_ == 0)
{
v___y_3364_ = v___y_3380_;
v___y_3365_ = v___y_3385_;
v___y_3366_ = v___x_3386_;
v___y_3367_ = v___y_3383_;
v___y_3368_ = v___y_3381_;
v___y_3369_ = v___y_3384_;
v___y_3370_ = v___y_3382_;
goto v___jp_3363_;
}
else
{
uint8_t v___x_3388_; 
v___x_3388_ = lean_nat_dec_le(v___x_3386_, v___x_3386_);
if (v___x_3388_ == 0)
{
if (v___x_3387_ == 0)
{
v___y_3364_ = v___y_3380_;
v___y_3365_ = v___y_3385_;
v___y_3366_ = v___x_3386_;
v___y_3367_ = v___y_3383_;
v___y_3368_ = v___y_3381_;
v___y_3369_ = v___y_3384_;
v___y_3370_ = v___y_3382_;
goto v___jp_3363_;
}
else
{
size_t v___x_3389_; size_t v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = ((size_t)0ULL);
v___x_3390_ = lean_usize_of_nat(v___x_3386_);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3385_, v___x_3389_, v___x_3390_, v___y_3382_);
v___y_3364_ = v___y_3380_;
v___y_3365_ = v___y_3385_;
v___y_3366_ = v___x_3386_;
v___y_3367_ = v___y_3383_;
v___y_3368_ = v___y_3381_;
v___y_3369_ = v___y_3384_;
v___y_3370_ = v___x_3391_;
goto v___jp_3363_;
}
}
else
{
size_t v___x_3392_; size_t v___x_3393_; lean_object* v___x_3394_; 
v___x_3392_ = ((size_t)0ULL);
v___x_3393_ = lean_usize_of_nat(v___x_3386_);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__18(v___y_3385_, v___x_3392_, v___x_3393_, v___y_3382_);
v___y_3364_ = v___y_3380_;
v___y_3365_ = v___y_3385_;
v___y_3366_ = v___x_3386_;
v___y_3367_ = v___y_3383_;
v___y_3368_ = v___y_3381_;
v___y_3369_ = v___y_3384_;
v___y_3370_ = v___x_3394_;
goto v___jp_3363_;
}
}
}
v___jp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___f_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3400_ = l_Lean_instInhabitedImportState_default;
v___x_3401_ = lean_box(v___x_3397_);
v___x_3402_ = lean_box(v___y_3399_);
v___x_3403_ = lean_box(v___x_2938_);
v___x_3404_ = lean_box(v___x_2913_);
lean_inc_ref(v___x_2942_);
lean_inc(v_name_2911_);
v___f_3405_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 10, 9);
lean_closure_set(v___f_3405_, 0, v___x_3400_);
lean_closure_set(v___f_3405_, 1, v___x_3396_);
lean_closure_set(v___f_3405_, 2, v___x_3401_);
lean_closure_set(v___f_3405_, 3, v___x_2935_);
lean_closure_set(v___f_3405_, 4, v___x_3402_);
lean_closure_set(v___f_3405_, 5, v_name_2911_);
lean_closure_set(v___f_3405_, 6, v___x_2942_);
lean_closure_set(v___f_3405_, 7, v___x_3403_);
lean_closure_set(v___f_3405_, 8, v___x_3404_);
v___x_3406_ = lean_alloc_closure((void*)(l_Lean_withImporting___boxed), 3, 2);
lean_closure_set(v___x_3406_, 0, lean_box(0));
lean_closure_set(v___x_3406_, 1, v___f_3405_);
v___x_3407_ = lean_box(0);
v___x_3408_ = l_Lean_profileitIOUnsafe___redArg(v___x_3232_, v___x_2942_, v___x_3406_, v___x_3407_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; lean_object* v_ext_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = l_Lean_Compiler_CSimp_ext;
v_ext_3411_ = lean_ctor_get(v___x_3410_, 1);
lean_inc(v_name_2911_);
v___x_3412_ = l_Lean_Environment_setMainModule(v_a_3409_, v_name_2911_);
lean_inc_ref(v_ext_3411_);
v___x_3413_ = l_main___elam__0___redArg(v___x_3407_, v___x_2929_, v_ext_3411_, v___x_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; lean_object* v_ext_3416_; lean_object* v___x_3417_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___x_3413_);
v___x_3415_ = l_Lean_Meta_instanceExtension;
v_ext_3416_ = lean_ctor_get(v___x_3415_, 1);
lean_inc_ref(v_ext_3416_);
v___x_3417_ = l_main___elam__0___redArg(v___x_3407_, v___x_2929_, v_ext_3416_, v_a_3414_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref(v___x_3417_);
v___x_3419_ = l_Lean_classExtension;
v___x_3420_ = l_main___elam__0___redArg(v___x_3407_, v___x_2930_, v___x_3419_, v_a_3418_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = l_Lean_Meta_Match_Extension_extension;
v___x_3423_ = l_main___elam__0___redArg(v___x_3407_, v___x_2931_, v___x_3422_, v_a_3421_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3452_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3452_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3452_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Environment_getModuleIdx_x3f(v_a_3424_, v_name_2911_);
if (lean_obj_tag(v___x_3428_) == 1)
{
lean_object* v_val_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
lean_del_object(v___x_3426_);
v_val_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_val_3429_);
lean_dec_ref(v___x_3428_);
v___x_3430_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_3431_ = 0;
v___x_3432_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2932_, v___x_3430_, v_a_3424_, v_val_3429_, v___x_3431_);
v___x_3433_ = lean_array_get_size(v___x_3432_);
v___x_3434_ = ((lean_object*)(l_main___closed__33));
v___x_3435_ = lean_nat_dec_lt(v___x_2941_, v___x_3433_);
if (v___x_3435_ == 0)
{
lean_dec_ref(v___x_3432_);
v___y_3380_ = v___x_3407_;
v___y_3381_ = v_val_3429_;
v___y_3382_ = v_a_3424_;
v___y_3383_ = v___x_3407_;
v___y_3384_ = v___x_3431_;
v___y_3385_ = v___x_3434_;
goto v___jp_3379_;
}
else
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_nat_dec_le(v___x_3433_, v___x_3433_);
if (v___x_3436_ == 0)
{
if (v___x_3435_ == 0)
{
lean_dec_ref(v___x_3432_);
v___y_3380_ = v___x_3407_;
v___y_3381_ = v_val_3429_;
v___y_3382_ = v_a_3424_;
v___y_3383_ = v___x_3407_;
v___y_3384_ = v___x_3431_;
v___y_3385_ = v___x_3434_;
goto v___jp_3379_;
}
else
{
size_t v___x_3437_; size_t v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = ((size_t)0ULL);
v___x_3438_ = lean_usize_of_nat(v___x_3433_);
lean_inc(v_a_3424_);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3424_, v___x_3432_, v___x_3437_, v___x_3438_, v___x_3434_);
lean_dec_ref(v___x_3432_);
v___y_3380_ = v___x_3407_;
v___y_3381_ = v_val_3429_;
v___y_3382_ = v_a_3424_;
v___y_3383_ = v___x_3407_;
v___y_3384_ = v___x_3431_;
v___y_3385_ = v___x_3439_;
goto v___jp_3379_;
}
}
else
{
size_t v___x_3440_; size_t v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = ((size_t)0ULL);
v___x_3441_ = lean_usize_of_nat(v___x_3433_);
lean_inc(v_a_3424_);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__19(v_a_3424_, v___x_3432_, v___x_3440_, v___x_3441_, v___x_3434_);
lean_dec_ref(v___x_3432_);
v___y_3380_ = v___x_3407_;
v___y_3381_ = v_val_3429_;
v___y_3382_ = v_a_3424_;
v___y_3383_ = v___x_3407_;
v___y_3384_ = v___x_3431_;
v___y_3385_ = v___x_3442_;
goto v___jp_3379_;
}
}
}
else
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_dec(v___x_3428_);
lean_dec(v_a_3424_);
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v___x_3443_ = ((lean_object*)(l_main___closed__34));
v___x_3444_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2911_, v___x_2938_);
v___x_3445_ = lean_string_append(v___x_3443_, v___x_3444_);
lean_dec_ref(v___x_3444_);
v___x_3446_ = ((lean_object*)(l_main___closed__35));
v___x_3447_ = lean_string_append(v___x_3445_, v___x_3446_);
v___x_3448_ = lean_mk_io_user_error(v___x_3447_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 1);
lean_ctor_set(v___x_3426_, 0, v___x_3448_);
v___x_3450_ = v___x_3426_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3453_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3423_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3423_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3461_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3420_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3420_);
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
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3469_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3417_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3417_);
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
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3477_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3413_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3413_);
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
lean_dec_ref(v___x_2942_);
lean_del_object(v___x_2927_);
lean_dec(v_fst_2924_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3485_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3408_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3408_);
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
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v_a_2919_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3495_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_2923_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_2923_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v_a_2919_);
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3503_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_2920_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_2920_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v_name_2911_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3511_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_2918_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_2918_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_del_object(v___x_2907_);
lean_dec(v_tail_2905_);
lean_dec(v_head_2904_);
lean_dec(v_head_2903_);
v_a_3520_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_2909_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_2909_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
else
{
lean_dec_ref(v_tail_2900_);
lean_dec(v_tail_2901_);
lean_dec_ref(v_args_2875_);
goto v___jp_2877_;
}
}
else
{
lean_dec(v_tail_2900_);
lean_dec_ref(v_args_2875_);
goto v___jp_2877_;
}
}
else
{
lean_dec(v_args_2875_);
goto v___jp_2877_;
}
v___jp_2877_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = ((lean_object*)(l_main___closed__0));
v___x_2879_ = l_IO_println___at___00Lean_Environment_displayStats_spec__1(v___x_2878_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2879_, 0);
lean_dec(v_unused_2888_);
v___x_2881_ = v___x_2879_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_dec(v___x_2879_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = l_main___boxed__const__1;
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2883_);
v___x_2885_ = v___x_2881_;
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
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_a_2889_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2879_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2879_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
v___jp_2897_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = l_main___boxed__const__2;
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3529_, lean_object* v_a_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = _lean_main(v_args_3529_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_as_3532_, lean_object* v_as_x27_3533_, lean_object* v_b_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_as_x27_3533_, v_b_3534_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_as_3538_, lean_object* v_as_x27_3539_, lean_object* v_b_3540_, lean_object* v_a_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_List_forIn_x27_loop___at___00main_spec__1(v_as_3538_, v_as_x27_3539_, v_b_3540_, v_a_3541_);
lean_dec(v_as_x27_3539_);
lean_dec(v_as_3538_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___redArg(v___y_3545_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16___boxed(lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__16(v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(lean_object* v_00_u03b2_3552_, lean_object* v_m_3553_, lean_object* v_a_3554_, lean_object* v_fallback_3555_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___redArg(v_m_3553_, v_a_3554_, v_fallback_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17___boxed(lean_object* v_00_u03b2_3557_, lean_object* v_m_3558_, lean_object* v_a_3559_, lean_object* v_fallback_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17(v_00_u03b2_3557_, v_m_3558_, v_a_3559_, v_fallback_3560_);
lean_dec(v_fallback_3560_);
lean_dec_ref(v_a_3559_);
lean_dec_ref(v_m_3558_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18(lean_object* v_00_u03b2_3562_, lean_object* v_m_3563_, lean_object* v_a_3564_, lean_object* v_b_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18___redArg(v_m_3563_, v_a_3564_, v_b_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(lean_object* v_n_3567_, lean_object* v_as_3568_, lean_object* v_lo_3569_, lean_object* v_hi_3570_, lean_object* v_w_3571_, lean_object* v_hlo_3572_, lean_object* v_hhi_3573_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___redArg(v_n_3567_, v_as_3568_, v_lo_3569_, v_hi_3570_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21___boxed(lean_object* v_n_3575_, lean_object* v_as_3576_, lean_object* v_lo_3577_, lean_object* v_hi_3578_, lean_object* v_w_3579_, lean_object* v_hlo_3580_, lean_object* v_hhi_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21(v_n_3575_, v_as_3576_, v_lo_3577_, v_hi_3578_, v_w_3579_, v_hlo_3580_, v_hhi_3581_);
lean_dec(v_hi_3578_);
lean_dec(v_n_3575_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(lean_object* v_00_u03b2_3583_, lean_object* v_a_3584_, lean_object* v_fallback_3585_, lean_object* v_x_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___redArg(v_a_3584_, v_fallback_3585_, v_x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21___boxed(lean_object* v_00_u03b2_3588_, lean_object* v_a_3589_, lean_object* v_fallback_3590_, lean_object* v_x_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__17_spec__21(v_00_u03b2_3588_, v_a_3589_, v_fallback_3590_, v_x_3591_);
lean_dec(v_x_3591_);
lean_dec(v_fallback_3590_);
lean_dec_ref(v_a_3589_);
return v_res_3592_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(lean_object* v_00_u03b2_3593_, lean_object* v_a_3594_, lean_object* v_x_3595_){
_start:
{
uint8_t v___x_3596_; 
v___x_3596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___redArg(v_a_3594_, v_x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23___boxed(lean_object* v_00_u03b2_3597_, lean_object* v_a_3598_, lean_object* v_x_3599_){
_start:
{
uint8_t v_res_3600_; lean_object* v_r_3601_; 
v_res_3600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__23(v_00_u03b2_3597_, v_a_3598_, v_x_3599_);
lean_dec(v_x_3599_);
lean_dec_ref(v_a_3598_);
v_r_3601_ = lean_box(v_res_3600_);
return v_r_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24(lean_object* v_00_u03b2_3602_, lean_object* v_data_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24___redArg(v_data_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25(lean_object* v_00_u03b2_3605_, lean_object* v_a_3606_, lean_object* v_b_3607_, lean_object* v_x_3608_){
_start:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__25___redArg(v_a_3606_, v_b_3607_, v_x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(lean_object* v_n_3610_, lean_object* v_lo_3611_, lean_object* v_hi_3612_, lean_object* v_hhi_3613_, lean_object* v_pivot_3614_, lean_object* v_as_3615_, lean_object* v_i_3616_, lean_object* v_k_3617_, lean_object* v_ilo_3618_, lean_object* v_ik_3619_, lean_object* v_w_3620_){
_start:
{
lean_object* v___x_3621_; 
v___x_3621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___redArg(v_hi_3612_, v_pivot_3614_, v_as_3615_, v_i_3616_, v_k_3617_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31___boxed(lean_object* v_n_3622_, lean_object* v_lo_3623_, lean_object* v_hi_3624_, lean_object* v_hhi_3625_, lean_object* v_pivot_3626_, lean_object* v_as_3627_, lean_object* v_i_3628_, lean_object* v_k_3629_, lean_object* v_ilo_3630_, lean_object* v_ik_3631_, lean_object* v_w_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__21_spec__31(v_n_3622_, v_lo_3623_, v_hi_3624_, v_hhi_3625_, v_pivot_3626_, v_as_3627_, v_i_3628_, v_k_3629_, v_ilo_3630_, v_ik_3631_, v_w_3632_);
lean_dec_ref(v_pivot_3626_);
lean_dec(v_hi_3624_);
lean_dec(v_lo_3623_);
lean_dec(v_n_3622_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(lean_object* v_as_3634_, size_t v_sz_3635_, size_t v_i_3636_, lean_object* v_b_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___redArg(v_as_3634_, v_sz_3635_, v_i_3636_, v_b_3637_, v___y_3638_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40___boxed(lean_object* v_as_3642_, lean_object* v_sz_3643_, lean_object* v_i_3644_, lean_object* v_b_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
size_t v_sz_boxed_3649_; size_t v_i_boxed_3650_; lean_object* v_res_3651_; 
v_sz_boxed_3649_ = lean_unbox_usize(v_sz_3643_);
lean_dec(v_sz_3643_);
v_i_boxed_3650_ = lean_unbox_usize(v_i_3644_);
lean_dec(v_i_3644_);
v_res_3651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__27_spec__40(v_as_3642_, v_sz_boxed_3649_, v_i_boxed_3650_, v_b_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec_ref(v_as_3642_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35(lean_object* v_00_u03b2_3652_, lean_object* v_i_3653_, lean_object* v_source_3654_, lean_object* v_target_3655_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35___redArg(v_i_3653_, v_source_3654_, v_target_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(uint8_t v___x_3657_, lean_object* v_as_3658_, size_t v_sz_3659_, size_t v_i_3660_, lean_object* v_b_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___redArg(v___x_3657_, v_as_3658_, v_sz_3659_, v_i_3660_, v_b_3661_, v___y_3662_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42___boxed(lean_object* v___x_3666_, lean_object* v_as_3667_, lean_object* v_sz_3668_, lean_object* v_i_3669_, lean_object* v_b_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v___x_41282__boxed_3674_; size_t v_sz_boxed_3675_; size_t v_i_boxed_3676_; lean_object* v_res_3677_; 
v___x_41282__boxed_3674_ = lean_unbox(v___x_3666_);
v_sz_boxed_3675_ = lean_unbox_usize(v_sz_3668_);
lean_dec(v_sz_3668_);
v_i_boxed_3676_ = lean_unbox_usize(v_i_3669_);
lean_dec(v_i_3669_);
v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__28_spec__42(v___x_41282__boxed_3674_, v_as_3667_, v_sz_boxed_3675_, v_i_boxed_3676_, v_b_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec_ref(v_as_3667_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(lean_object* v_as_3678_, size_t v_sz_3679_, size_t v_i_3680_, lean_object* v_b_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___redArg(v_as_3678_, v_sz_3679_, v_i_3680_, v_b_3681_, v___y_3682_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51___boxed(lean_object* v_as_3686_, lean_object* v_sz_3687_, lean_object* v_i_3688_, lean_object* v_b_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
size_t v_sz_boxed_3693_; size_t v_i_boxed_3694_; lean_object* v_res_3695_; 
v_sz_boxed_3693_ = lean_unbox_usize(v_sz_3687_);
lean_dec(v_sz_3687_);
v_i_boxed_3694_ = lean_unbox_usize(v_i_3688_);
lean_dec(v_i_3688_);
v_res_3695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00main_spec__12_spec__26_spec__38_spec__51(v_as_3686_, v_sz_boxed_3693_, v_i_boxed_3694_, v_b_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_as_3686_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44(lean_object* v_00_u03b2_3696_, lean_object* v_x_3697_, lean_object* v_x_3698_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__18_spec__24_spec__35_spec__44___redArg(v_x_3697_, v_x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(uint8_t v___x_3700_, lean_object* v_as_3701_, size_t v_sz_3702_, size_t v_i_3703_, lean_object* v_b_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___redArg(v___x_3700_, v_as_3701_, v_sz_3702_, v_i_3703_, v_b_3704_, v___y_3705_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49___boxed(lean_object* v___x_3709_, lean_object* v_as_3710_, lean_object* v_sz_3711_, lean_object* v_i_3712_, lean_object* v_b_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
uint8_t v___x_41313__boxed_3717_; size_t v_sz_boxed_3718_; size_t v_i_boxed_3719_; lean_object* v_res_3720_; 
v___x_41313__boxed_3717_ = lean_unbox(v___x_3709_);
v_sz_boxed_3718_ = lean_unbox_usize(v_sz_3711_);
lean_dec(v_sz_3711_);
v_i_boxed_3719_ = lean_unbox_usize(v_i_3712_);
lean_dec(v_i_3712_);
v_res_3720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_addTraceAsMessages___at___00main_spec__10_spec__19_spec__27_spec__40_spec__49(v___x_41313__boxed_3717_, v_as_3710_, v_sz_boxed_3718_, v_i_boxed_3719_, v_b_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec_ref(v_as_3710_);
return v_res_3720_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Main(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
l_main___boxed__const__2 = _init_l_main___boxed__const__2();
lean_mark_persistent(l_main___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_EmitC(uint8_t builtin);
lean_object* initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanIR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_EmitC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_LeanIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_LeanIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_LeanIR(builtin);
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize();
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    lean_object* in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    return _lean_main(in);
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  res = runtime_initialize_LeanIR(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = lean_unbox_uint32(lean_io_result_get_value(res));
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
