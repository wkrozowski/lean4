// Lean compiler output
// Module: Lean.Compiler.IR.CompilerM
// Imports: Lean.CoreM Lean.Environment Lean.Compiler.IR.Basic Lean.Compiler.IR.Format Lean.Compiler.MetaAttr Lean.Compiler.ExportAttr Lean.Compiler.LCNF.PhaseExt
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
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0;
static lean_object* l_Lean_IR_findEnvDecl___closed__0;
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___lam__3___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__0;
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_isDeclMeta___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_IR_log_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__1(lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_addDecl___redArg___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__9;
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435_(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt___lam__0___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declMetaExt;
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_isDeclMeta___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__2;
static lean_object* l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__8;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExportNameFor_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_IR_log___closed__1;
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_IR_log_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_435____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_instToFormat;
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_log___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getDecl___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_IR_LogEntry_fmt_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_log___closed__2;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__5;
static lean_object* l_Lean_IR_LogEntry_instToFormat___closed__0;
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_getDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_IR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_getDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_findEnvDecl_x27___closed__0;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__11;
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_log___closed__3;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__4____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__10;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_IR_isDeclMeta___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object*);
static lean_object* l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
static lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__0;
LEAN_EXPORT uint8_t l_Lean_IR_LogEntry_fmt___lam__0(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__1;
static lean_object* l_Lean_IR_addDecl___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_getDecl___closed__0;
LEAN_EXPORT uint8_t l_Lean_IR_isDeclMeta(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_tracePrefixOptionName;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getDecl___closed__1;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
static lean_object* l_Lean_IR_initFn___lam__3___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4(lean_object*, lean_object*, size_t, lean_object*);
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__12;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_435_(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__6;
static lean_object* l_Lean_IR_tracePrefixOptionName___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_getDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__4;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_setDeclMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_getDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__1;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__1(lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_setDeclMeta___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_IR_isDeclMeta___closed__2;
static size_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__0;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_LogEntry_fmt___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_IR_LogEntry_fmt_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_IR_formatDecl(x_6, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LogEntry_fmt___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_LogEntry_fmt___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_LogEntry_fmt___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt___lam__0___boxed), 1, 0);
x_6 = 1;
x_7 = l_Lean_Name_toString(x_3, x_6, x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_IR_LogEntry_fmt___closed__2;
x_10 = l_Lean_IR_LogEntry_fmt___closed__3;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_10);
x_11 = l_Lean_IR_LogEntry_fmt___closed__4;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = 0;
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_4);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec_ref(x_4);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_18, x_18);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec_ref(x_4);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__1(x_4, x_23, x_24, x_16);
lean_dec_ref(x_4);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt___lam__0___boxed), 1, 0);
x_30 = 1;
x_31 = l_Lean_Name_toString(x_27, x_30, x_29);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_IR_LogEntry_fmt___closed__2;
x_34 = l_Lean_IR_LogEntry_fmt___closed__3;
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
x_36 = l_Lean_IR_LogEntry_fmt___closed__4;
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = 0;
x_40 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_box(0);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_get_size(x_28);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec_ref(x_28);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec_ref(x_28);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_50 = l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__1(x_28, x_48, x_49, x_41);
lean_dec_ref(x_28);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_dec_ref(x_1);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_LogEntry_fmt_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_LogEntry_fmt___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_instToFormat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_LogEntry_instToFormat___closed__0;
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1;
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = l_Lean_IR_LogEntry_fmt(x_6);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Log_format(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_Log_format(x_1);
x_3 = lean_unsigned_to_nat(120u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_2, x_3, x_4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Log_toString(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__6;
x_2 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__4;
x_4 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__3;
x_5 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__2;
x_6 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__9;
x_4 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__10;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__11;
x_3 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 2);
x_10 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__7;
x_11 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__12;
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__7;
x_19 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__12;
lean_inc(x_17);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_17);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
static double _init_l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_IR_log_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 4);
lean_inc_ref(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 4);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; double x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__0;
x_21 = 0;
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_21);
x_24 = l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1;
x_25 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_25);
lean_ctor_set(x_10, 0, x_6);
x_26 = l_Lean_PersistentArray_push___redArg(x_19, x_10);
lean_ctor_set(x_12, 0, x_26);
x_27 = lean_st_ref_set(x_4, x_11, x_14);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint64_t x_34; lean_object* x_35; double x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__0;
x_37 = 0;
x_38 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
x_39 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_float(x_39, sizeof(void*)*2, x_36);
lean_ctor_set_float(x_39, sizeof(void*)*2 + 8, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 16, x_37);
x_40 = l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1;
x_41 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_8);
lean_ctor_set(x_41, 2, x_40);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_41);
lean_ctor_set(x_10, 0, x_6);
x_42 = l_Lean_PersistentArray_push___redArg(x_35, x_10);
x_43 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint64(x_43, sizeof(void*)*1, x_34);
lean_ctor_set(x_11, 4, x_43);
x_44 = lean_st_ref_set(x_4, x_11, x_14);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; double x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
x_51 = lean_ctor_get(x_11, 2);
x_52 = lean_ctor_get(x_11, 3);
x_53 = lean_ctor_get(x_11, 5);
x_54 = lean_ctor_get(x_11, 6);
x_55 = lean_ctor_get(x_11, 7);
x_56 = lean_ctor_get(x_11, 8);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_57 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_58 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_58);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_59 = x_12;
} else {
 lean_dec_ref(x_12);
 x_59 = lean_box(0);
}
x_60 = l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__0;
x_61 = 0;
x_62 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
x_63 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_float(x_63, sizeof(void*)*2, x_60);
lean_ctor_set_float(x_63, sizeof(void*)*2 + 8, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*2 + 16, x_61);
x_64 = l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1;
x_65 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_8);
lean_ctor_set(x_65, 2, x_64);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_65);
lean_ctor_set(x_10, 0, x_6);
x_66 = l_Lean_PersistentArray_push___redArg(x_58, x_10);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(0, 1, 8);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set_uint64(x_67, sizeof(void*)*1, x_57);
x_68 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_68, 0, x_49);
lean_ctor_set(x_68, 1, x_50);
lean_ctor_set(x_68, 2, x_51);
lean_ctor_set(x_68, 3, x_52);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_53);
lean_ctor_set(x_68, 6, x_54);
lean_ctor_set(x_68, 7, x_55);
lean_ctor_set(x_68, 8, x_56);
x_69 = lean_st_ref_set(x_4, x_68, x_14);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint64_t x_84; lean_object* x_85; lean_object* x_86; double x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_74 = lean_ctor_get(x_10, 1);
lean_inc(x_74);
lean_dec(x_10);
x_75 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_11, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_11, 3);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_11, 5);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_11, 6);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_11, 7);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_11, 8);
lean_inc_ref(x_82);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 lean_ctor_release(x_11, 7);
 lean_ctor_release(x_11, 8);
 x_83 = x_11;
} else {
 lean_dec_ref(x_11);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_85 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_85);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_86 = x_12;
} else {
 lean_dec_ref(x_12);
 x_86 = lean_box(0);
}
x_87 = l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__0;
x_88 = 0;
x_89 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
x_90 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_float(x_90, sizeof(void*)*2, x_87);
lean_ctor_set_float(x_90, sizeof(void*)*2 + 8, x_87);
lean_ctor_set_uint8(x_90, sizeof(void*)*2 + 16, x_88);
x_91 = l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1;
x_92 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_8);
lean_ctor_set(x_92, 2, x_91);
lean_inc(x_6);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_6);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_PersistentArray_push___redArg(x_85, x_93);
if (lean_is_scalar(x_86)) {
 x_95 = lean_alloc_ctor(0, 1, 8);
} else {
 x_95 = x_86;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set_uint64(x_95, sizeof(void*)*1, x_84);
if (lean_is_scalar(x_83)) {
 x_96 = lean_alloc_ctor(0, 9, 0);
} else {
 x_96 = x_83;
}
lean_ctor_set(x_96, 0, x_75);
lean_ctor_set(x_96, 1, x_76);
lean_ctor_set(x_96, 2, x_77);
lean_ctor_set(x_96, 3, x_78);
lean_ctor_set(x_96, 4, x_95);
lean_ctor_set(x_96, 5, x_79);
lean_ctor_set(x_96, 6, x_80);
lean_ctor_set(x_96, 7, x_81);
lean_ctor_set(x_96, 8, x_82);
x_97 = lean_st_ref_set(x_4, x_96, x_74);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
}
static lean_object* _init_l_Lean_IR_log___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_log___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_log___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_log___closed__1;
x_2 = l_Lean_IR_log___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_log___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_IR_log___closed__2;
x_6 = l_Lean_IR_log___closed__3;
x_7 = l_Lean_IR_LogEntry_fmt(x_1);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = l_Lean_addTrace___at___Lean_IR_log_spec__0(x_5, x_10, x_2, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_IR_log_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___Lean_IR_log_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_log(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ir", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_tracePrefixOptionName___closed__2;
x_2 = l_Lean_IR_tracePrefixOptionName___closed__1;
x_3 = l_Lean_IR_tracePrefixOptionName___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_tracePrefixOptionName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_tracePrefixOptionName___closed__3;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
goto block_6;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
lean_dec(x_8);
goto block_6;
}
}
block_6:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = 0;
x_5 = l_Lean_KVMap_getBool(x_1, x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
x_12 = l_Lean_IR_log(x_11, x_4, x_5, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_tracePrefixOptionName;
lean_inc(x_1);
x_7 = l_Lean_Name_append(x_6, x_1);
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_7, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_logDecls(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(x_7, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_apply_1(x_1, x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_IR_log(x_12, x_4, x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_IR_tracePrefixOptionName;
x_8 = l_Lean_Name_append(x_7, x_2);
x_9 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_IR_tracePrefixOptionName;
x_9 = l_Lean_Name_append(x_8, x_3);
x_10 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_2, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_logMessageIf___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_logMessageIf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_tracePrefixOptionName;
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_tracePrefixOptionName;
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(x_2, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_logMessage___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_logMessage(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
x_3 = x_7;
goto block_6;
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_5 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_13 = lean_nat_dec_le(x_3, x_7);
if (x_13 == 0)
{
lean_inc(x_7);
x_8 = x_7;
goto block_12;
}
else
{
x_8 = x_3;
goto block_12;
}
block_12:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Array_qsort_sort___redArg(x_5, x_1, x_8, x_8);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Array_qsort_sort___redArg(x_5, x_1, x_8, x_7);
lean_dec(x_7);
return x_11;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_dec_le(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
x_15 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0;
x_16 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1;
x_17 = l_Array_binSearchAux___redArg(x_15, x_16, x_1, x_14, x_3, x_8);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_List_elem___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__0(x_4, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
lean_inc(x_4);
lean_ctor_set(x_2, 1, x_6);
x_12 = l_Lean_NameSet_insert(x_7, x_4);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_2);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
lean_inc(x_4);
lean_ctor_set(x_2, 1, x_6);
x_14 = l_Lean_NameSet_insert(x_7, x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_1 = x_15;
x_2 = x_5;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_free_object(x_2);
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = l_List_elem___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__0(x_18, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_23 = x_1;
} else {
 lean_dec_ref(x_1);
 x_23 = lean_box(0);
}
lean_inc(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_20);
x_25 = l_Lean_NameSet_insert(x_21, x_18);
if (lean_is_scalar(x_23)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_23;
}
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_1 = x_26;
x_2 = x_19;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
x_2 = x_19;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_List_lengthTR___redArg(x_5);
x_8 = l_List_lengthTR___redArg(x_6);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_;
lean_inc(x_5);
x_11 = l_List_takeTR_go___redArg(x_5, x_5, x_9, x_10);
lean_dec(x_5);
x_12 = l_List_foldl___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__1(x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_435_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_435____boxed), 4, 0);
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_;
x_4 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_435_), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = 0;
x_7 = l_Lean_registerEnvExtension___redArg(x_4, x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435__spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_435____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_isDeclMeta___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declMetaExt;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_isDeclMeta___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_isDeclMeta___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_boxed", 6, 6);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_isDeclMeta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Environment_header(x_1);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*5 + 4);
lean_dec_ref(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec_ref(x_1);
x_13 = 1;
return x_13;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = l_Lean_IR_isDeclMeta___closed__2;
x_17 = lean_string_dec_eq(x_15, x_16);
if (x_17 == 0)
{
x_3 = x_2;
goto block_10;
}
else
{
x_3 = x_14;
goto block_10;
}
}
else
{
x_3 = x_2;
goto block_10;
}
}
block_10:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_IR_isDeclMeta___closed__0;
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_6 = l_Lean_IR_isDeclMeta___closed__1;
x_7 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_6, x_4, x_1, x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_3, x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_isDeclMeta___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_isDeclMeta(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_setDeclMeta___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_NameSet_insert(x_5, x_1);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_NameSet_insert(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_setDeclMeta(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc_ref(x_1);
x_3 = l_Lean_IR_isDeclMeta(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_IR_isDeclMeta___closed__0;
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_6 = lean_alloc_closure((void*)(l_Lean_IR_setDeclMeta___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_EnvExtension_modifyState___redArg(x_4, x_1, x_6, x_5);
return x_7;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_20; 
x_20 = lean_usize_dec_eq(x_3, x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_38; lean_object* x_43; 
x_21 = lean_array_uget(x_2, x_3);
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
x_38 = x_43;
goto block_42;
block_37:
{
uint8_t x_23; 
lean_inc_ref(x_1);
x_23 = l_Lean_Compiler_LCNF_isDeclPublic(x_1, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_21);
x_6 = x_5;
goto block_10;
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_21, 2);
lean_inc(x_26);
lean_dec_ref(x_21);
lean_inc(x_24);
lean_inc_ref(x_1);
x_27 = l_Lean_getExportNameFor_x3f(x_1, x_24);
if (lean_obj_tag(x_27) == 0)
{
x_11 = x_25;
x_12 = x_24;
x_13 = x_26;
goto block_19;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_28);
x_30 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__1;
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_array_push(x_5, x_34);
x_6 = x_35;
goto block_10;
}
else
{
lean_dec(x_28);
x_11 = x_25;
x_12 = x_24;
x_13 = x_26;
goto block_19;
}
}
}
else
{
lean_object* x_36; 
x_36 = lean_array_push(x_5, x_21);
x_6 = x_36;
goto block_10;
}
}
}
block_42:
{
uint8_t x_39; 
lean_inc_ref(x_1);
x_39 = l_Lean_IR_isDeclMeta(x_1, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
x_22 = x_40;
goto block_37;
}
else
{
lean_object* x_41; 
x_41 = lean_array_push(x_5, x_21);
x_6 = x_41;
goto block_10;
}
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_array_push(x_5, x_17);
x_6 = x_18;
goto block_10;
}
}
}
static lean_object* _init_l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___closed__0;
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_le(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_usize_of_nat(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0(x_1, x_2, x_9, x_10, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
x_3 = x_7;
goto block_6;
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___lam__0___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_name_eq(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___redArg(x_2, x_5, x_6);
return x_7;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_6, x_2);
x_13 = lean_name_eq(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget(x_19, x_2);
x_27 = lean_name_eq(x_3, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7_spec__7___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7_spec__7___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget(x_2, x_4);
x_9 = lean_array_fget(x_3, x_4);
x_10 = l_Lean_Name_hash___override(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_19 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_name_eq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_name_eq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___closed__0;
x_52 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__7___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___closed__0;
x_68 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_19; uint8_t x_20; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___closed__0;
x_14 = l_List_foldl___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__2(x_13, x_3);
x_19 = lean_array_get_size(x_14);
x_20 = lean_nat_dec_eq(x_19, x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_26; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_19, x_21);
lean_dec(x_19);
x_26 = lean_nat_dec_le(x_12, x_22);
if (x_26 == 0)
{
lean_inc(x_22);
x_23 = x_22;
goto block_25;
}
else
{
x_23 = x_12;
goto block_25;
}
block_25:
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_23, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_inc(x_23);
x_15 = x_23;
x_16 = x_23;
goto block_18;
}
else
{
x_15 = x_23;
x_16 = x_22;
goto block_18;
}
}
}
else
{
lean_dec(x_19);
x_5 = x_14;
goto block_11;
}
block_11:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Environment_header(x_1);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 4);
lean_dec_ref(x_6);
if (x_7 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_5);
x_10 = l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0(x_1, x_5, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_5);
return x_10;
}
}
block_18:
{
lean_object* x_17; 
x_17 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg(x_14, x_15, x_16);
lean_dec(x_16);
x_5 = x_17;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
x_3 = x_8;
goto block_7;
block_7:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___redArg(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__3___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__3___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_initFn___lam__3___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_initFn___lam__3___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__4____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7___redArg(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declMapExt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
x_2 = l_Lean_IR_log___closed__1;
x_3 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed), 4, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed), 1, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_IR_initFn___lam__4____x40_Lean_Compiler_IR_CompilerM___hyg_601_), 2, 0);
x_7 = l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = 0;
lean_inc_ref(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed), 7, 4);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_3);
lean_ctor_set(x_12, 4, x_8);
lean_ctor_set(x_12, 5, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*6, x_9);
x_13 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_12, x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7_spec__9(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lean_IR_initFn___lam__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_(x_1, x_2, x_3, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_initFn___lam__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_601____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_initFn___lam__3____x40_Lean_Compiler_IR_CompilerM___hyg_601_(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
x_12 = lean_nat_dec_le(x_3, x_6);
if (x_12 == 0)
{
lean_inc(x_6);
x_7 = x_6;
goto block_11;
}
else
{
x_7 = x_3;
goto block_11;
}
block_11:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_inc(x_7);
x_9 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg(x_1, x_7, x_7);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg(x_1, x_7, x_6);
lean_dec(x_6);
return x_10;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1;
x_2 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0;
x_3 = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declMapExt;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
x_3 = l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___closed__0;
x_4 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
x_5 = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(x_2, x_4, x_1);
x_6 = l_List_foldl___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__2(x_3, x_5);
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(x_6);
x_8 = l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__4;
x_11 = lean_array_push(x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_name_eq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_name_eq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_shiftr(x_5, x_6);
lean_dec(x_5);
x_8 = lean_array_fget(x_1, x_7);
x_9 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___lam__0(x_8, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = l_Array_qsort_sort___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__3___redArg___lam__0(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec_ref(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_15 = lean_nat_dec_lt(x_14, x_3);
if (x_15 == 0)
{
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
x_17 = lean_box(0);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = lean_box(0);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec_ref(x_8);
lean_dec(x_3);
x_19 = lean_nat_add(x_7, x_6);
lean_dec(x_7);
x_20 = lean_nat_dec_le(x_19, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_4);
x_21 = lean_box(0);
return x_21;
}
else
{
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
x_4 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec_ref(x_6);
x_8 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_3, x_5, x_1, x_7);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg(x_8, x_2);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = l_Lean_IR_findEnvDecl___closed__0;
x_12 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
x_28 = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), x_11, x_12, x_1, x_10);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_28);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec_ref(x_28);
x_32 = lean_box(0);
x_13 = x_32;
goto block_27;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_30, x_33);
lean_dec(x_30);
x_35 = lean_nat_dec_le(x_29, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
lean_dec_ref(x_28);
x_36 = lean_box(0);
x_13 = x_36;
goto block_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
x_38 = lean_box(0);
x_39 = lean_box(0);
lean_inc(x_2);
x_40 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___redArg(x_28, x_40, x_29, x_34);
lean_dec_ref(x_40);
lean_dec_ref(x_28);
if (lean_obj_tag(x_41) == 0)
{
x_13 = x_41;
goto block_27;
}
else
{
lean_dec(x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_41;
}
}
}
block_27:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = 0;
x_15 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_11, x_12, x_1, x_10, x_14);
lean_dec(x_10);
lean_dec_ref(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_17, x_19);
lean_dec(x_17);
x_21 = lean_nat_dec_le(x_16, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec_ref(x_15);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
x_22 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0;
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___redArg(x_15, x_25, x_16, x_20);
lean_dec_ref(x_25);
lean_dec_ref(x_15);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_IR_findEnvDecl_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_ir_find_env_decl(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_ir_find_env_decl(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_findDecl___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_findDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_findDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_findDecl___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = 0;
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec_ref(x_5);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_containsDecl___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_containsDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_containsDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_getDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_getDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_IR_getDecl_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_getDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_LogEntry_fmt___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown declaration '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = l_Lean_IR_findDecl___redArg(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Lean_IR_getDecl___closed__0;
x_9 = l_Lean_IR_getDecl___closed__1;
x_10 = 1;
x_11 = l_Lean_Name_toString(x_1, x_10, x_8);
x_12 = lean_string_append(x_9, x_11);
lean_dec_ref(x_11);
x_13 = l_Lean_IR_getDecl___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = l_Lean_throwError___at___Lean_IR_getDecl_spec__0___redArg(x_16, x_2, x_3, x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec_ref(x_6);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec_ref(x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_IR_getDecl_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_getDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_IR_getDecl_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_getDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
lean_dec_ref(x_9);
x_11 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
x_12 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_11, x_8, x_7, x_10);
x_13 = l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg(x_12, x_1);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
x_21 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_20, x_17, x_16, x_19);
x_22 = l_Lean_PersistentHashMap_find_x3f___at___Lean_IR_findEnvDecl_spec__0___redArg(x_21, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_findLocalDecl___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_findLocalDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_findLocalDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
x_4 = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_addDecl___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_addDecl___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
x_11 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_10, x_8, x_1);
x_12 = l_Lean_IR_addDecl___redArg___closed__2;
lean_ctor_set(x_5, 5, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = lean_st_ref_set(x_2, x_5, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 2);
x_23 = lean_ctor_get(x_5, 3);
x_24 = lean_ctor_get(x_5, 4);
x_25 = lean_ctor_get(x_5, 6);
x_26 = lean_ctor_get(x_5, 7);
x_27 = lean_ctor_get(x_5, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_28 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
x_29 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_28, x_20, x_1);
x_30 = l_Lean_IR_addDecl___redArg___closed__2;
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_25);
lean_ctor_set(x_31, 7, x_26);
lean_ctor_set(x_31, 8, x_27);
x_32 = lean_st_ref_set(x_2, x_31, x_6);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_addDecl___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_addDecl___redArg(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(x_1, x_12, x_13, x_7, x_3, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addDecls_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_addDecls(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_inc_ref(x_7);
return x_7;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_18; uint8_t x_19; 
x_9 = lean_array_uget(x_4, x_6);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_name_eq(x_18, x_3);
lean_dec(x_18);
x_10 = x_19;
goto block_17;
block_17:
{
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_6, x_11);
{
size_t _tmp_5 = x_12;
lean_object* _tmp_6 = x_1;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
return x_16;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_box(0);
x_5 = l_Lean_IR_findEnvDecl_x27___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0(x_5, x_4, x_2, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ir_find_env_decl(x_1, x_2);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ir_find_env_decl(x_1, x_2);
return x_12;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_findEnvDecl_x27_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_findEnvDecl_x27(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_IR_findEnvDecl_x27(x_8, x_1, x_2);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = l_Lean_IR_findEnvDecl_x27(x_12, x_1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_findDecl_x27___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_findDecl_x27___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_findDecl_x27(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = 1;
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_name_eq(x_13, x_1);
lean_dec(x_13);
x_7 = x_14;
goto block_11;
block_11:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = l_Lean_IR_containsDecl___redArg(x_1, x_3, x_4);
return x_8;
}
else
{
if (x_7 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Lean_IR_containsDecl___redArg(x_1, x_3, x_4);
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0(x_1, x_2, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_IR_containsDecl___redArg(x_1, x_3, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_box(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_containsDecl_x27___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_IR_containsDecl_x27_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_containsDecl_x27___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_containsDecl_x27(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lean_IR_findDecl_x27___redArg(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_IR_getDecl___closed__0;
x_10 = l_Lean_IR_getDecl___closed__1;
x_11 = 1;
x_12 = l_Lean_Name_toString(x_1, x_11, x_9);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_IR_getDecl___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = l_Lean_throwError___at___Lean_IR_getDecl_spec__0___redArg(x_17, x_3, x_4, x_8);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_6, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec_ref(x_7);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec_ref(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_getDecl_x27(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ir_find_env_decl(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_8 = x_14;
goto block_13;
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_19; uint8_t x_20; 
x_13 = lean_array_uget(x_3, x_4);
x_19 = 1;
lean_inc(x_13);
lean_inc_ref(x_1);
x_20 = l_Lean_Environment_contains(x_1, x_13, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = 2;
x_22 = l_Lean_instDecidableEqOLeanLevel(x_2, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_inc_ref(x_1);
x_23 = l_Lean_Compiler_LCNF_isDeclPublic(x_1, x_13);
x_14 = x_23;
goto block_18;
}
else
{
x_14 = x_22;
goto block_18;
}
}
else
{
lean_dec(x_13);
x_7 = x_6;
goto block_11;
}
block_18:
{
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_IR_isDeclMeta(x_1, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_16; 
x_16 = lean_array_push(x_6, x_13);
x_7 = x_16;
goto block_11;
}
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_6, x_13);
x_7 = x_17;
goto block_11;
}
}
}
else
{
lean_dec_ref(x_1);
return x_6;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
x_4 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3;
lean_inc_ref(x_1);
x_5 = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(x_3, x_4, x_1);
x_6 = lean_array_mk(x_5);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(x_7, x_8, x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_;
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
return x_12;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
return x_12;
}
else
{
size_t x_15; lean_object* x_16; 
x_15 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_16 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(x_1, x_2, x_9, x_8, x_15, x_12);
lean_dec_ref(x_9);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(x_1, x_7, x_3, x_8, x_9, x_6);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = lean_get_ir_extra_const_names(x_1, x_3);
return x_4;
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExportAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_LogEntry_fmt___closed__0 = _init_l_Lean_IR_LogEntry_fmt___closed__0();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__0);
l_Lean_IR_LogEntry_fmt___closed__1 = _init_l_Lean_IR_LogEntry_fmt___closed__1();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__1);
l_Lean_IR_LogEntry_fmt___closed__2 = _init_l_Lean_IR_LogEntry_fmt___closed__2();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__2);
l_Lean_IR_LogEntry_fmt___closed__3 = _init_l_Lean_IR_LogEntry_fmt___closed__3();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__3);
l_Lean_IR_LogEntry_fmt___closed__4 = _init_l_Lean_IR_LogEntry_fmt___closed__4();
lean_mark_persistent(l_Lean_IR_LogEntry_fmt___closed__4);
l_Lean_IR_LogEntry_instToFormat___closed__0 = _init_l_Lean_IR_LogEntry_instToFormat___closed__0();
lean_mark_persistent(l_Lean_IR_LogEntry_instToFormat___closed__0);
l_Lean_IR_LogEntry_instToFormat = _init_l_Lean_IR_LogEntry_instToFormat();
lean_mark_persistent(l_Lean_IR_LogEntry_instToFormat);
l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__0);
l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_IR_Log_format_spec__0___closed__1);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__0);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__1 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__1);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__2 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__2);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__3 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__3);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__4 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__4);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__5 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__5);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__6 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__6);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__7 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__7();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__7);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__8 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__8();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__8);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__9 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__9();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__9);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__10 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__10();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__10);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__11 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__11();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__11);
l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__12 = _init_l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__12();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_addTrace___at___Lean_IR_log_spec__0_spec__0___closed__12);
l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__0 = _init_l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__0();
l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1 = _init_l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_IR_log_spec__0___closed__1);
l_Lean_IR_log___closed__0 = _init_l_Lean_IR_log___closed__0();
lean_mark_persistent(l_Lean_IR_log___closed__0);
l_Lean_IR_log___closed__1 = _init_l_Lean_IR_log___closed__1();
lean_mark_persistent(l_Lean_IR_log___closed__1);
l_Lean_IR_log___closed__2 = _init_l_Lean_IR_log___closed__2();
lean_mark_persistent(l_Lean_IR_log___closed__2);
l_Lean_IR_log___closed__3 = _init_l_Lean_IR_log___closed__3();
lean_mark_persistent(l_Lean_IR_log___closed__3);
l_Lean_IR_tracePrefixOptionName___closed__0 = _init_l_Lean_IR_tracePrefixOptionName___closed__0();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__0);
l_Lean_IR_tracePrefixOptionName___closed__1 = _init_l_Lean_IR_tracePrefixOptionName___closed__1();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__1);
l_Lean_IR_tracePrefixOptionName___closed__2 = _init_l_Lean_IR_tracePrefixOptionName___closed__2();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__2);
l_Lean_IR_tracePrefixOptionName___closed__3 = _init_l_Lean_IR_tracePrefixOptionName___closed__3();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName___closed__3);
l_Lean_IR_tracePrefixOptionName = _init_l_Lean_IR_tracePrefixOptionName();
lean_mark_persistent(l_Lean_IR_tracePrefixOptionName);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_ = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___lam__0___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_ = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_435_);
if (builtin) {res = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_435_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declMetaExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declMetaExt);
lean_dec_ref(res);
}l_Lean_IR_isDeclMeta___closed__0 = _init_l_Lean_IR_isDeclMeta___closed__0();
lean_mark_persistent(l_Lean_IR_isDeclMeta___closed__0);
l_Lean_IR_isDeclMeta___closed__1 = _init_l_Lean_IR_isDeclMeta___closed__1();
lean_mark_persistent(l_Lean_IR_isDeclMeta___closed__1);
l_Lean_IR_isDeclMeta___closed__2 = _init_l_Lean_IR_isDeclMeta___closed__2();
lean_mark_persistent(l_Lean_IR_isDeclMeta___closed__2);
l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__0);
l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0_spec__0___closed__1);
l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___closed__0 = _init_l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___closed__0();
lean_mark_persistent(l_Array_filterMapM___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__0___closed__0);
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__4_spec__4___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601__spec__7_spec__7___redArg___closed__0);
l_Lean_IR_initFn___lam__3___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_ = _init_l_Lean_IR_initFn___lam__3___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_();
lean_mark_persistent(l_Lean_IR_initFn___lam__3___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_);
l_Lean_IR_initFn___lam__3___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_ = _init_l_Lean_IR_initFn___lam__3___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_();
lean_mark_persistent(l_Lean_IR_initFn___lam__3___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_);
l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_ = _init_l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_();
lean_mark_persistent(l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR_CompilerM___hyg_601_);
l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_ = _init_l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_();
lean_mark_persistent(l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR_CompilerM___hyg_601_);
l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_ = _init_l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_();
lean_mark_persistent(l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR_CompilerM___hyg_601_);
if (builtin) {res = l_Lean_IR_initFn____x40_Lean_Compiler_IR_CompilerM___hyg_601_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_declMapExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_declMapExt);
lean_dec_ref(res);
}l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3);
l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__4 = _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__4);
l_Lean_IR_findEnvDecl___closed__0 = _init_l_Lean_IR_findEnvDecl___closed__0();
lean_mark_persistent(l_Lean_IR_findEnvDecl___closed__0);
l_Lean_IR_getDecl___closed__0 = _init_l_Lean_IR_getDecl___closed__0();
lean_mark_persistent(l_Lean_IR_getDecl___closed__0);
l_Lean_IR_getDecl___closed__1 = _init_l_Lean_IR_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_getDecl___closed__1);
l_Lean_IR_getDecl___closed__2 = _init_l_Lean_IR_getDecl___closed__2();
lean_mark_persistent(l_Lean_IR_getDecl___closed__2);
l_Lean_IR_addDecl___redArg___closed__0 = _init_l_Lean_IR_addDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_addDecl___redArg___closed__0);
l_Lean_IR_addDecl___redArg___closed__1 = _init_l_Lean_IR_addDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_addDecl___redArg___closed__1);
l_Lean_IR_addDecl___redArg___closed__2 = _init_l_Lean_IR_addDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_addDecl___redArg___closed__2);
l_Lean_IR_findEnvDecl_x27___closed__0 = _init_l_Lean_IR_findEnvDecl_x27___closed__0();
lean_mark_persistent(l_Lean_IR_findEnvDecl_x27___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
