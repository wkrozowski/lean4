// Lean compiler output
// Module: Lean.Compiler.IR.CompilerM
// Imports: public import Lean.Compiler.IR.Format public import Lean.Compiler.ExportAttr public import Lean.Compiler.LCNF.PublicDeclsExt import Lean.Compiler.InitAttr import all Lean.Compiler.ModPkgExt import Init.Data.Format.Macro import Lean.Compiler.LCNF.Basic
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
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_get_export_name_for(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isBoxedName(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExternAttrData_default;
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_regularInitAttr;
extern lean_object* l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_IR_LogEntry_fmt_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_LogEntry_fmt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_IR_LogEntry_fmt___closed__0 = (const lean_object*)&l_Lean_IR_LogEntry_fmt___closed__0_value;
static const lean_string_object l_Lean_IR_LogEntry_fmt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_IR_LogEntry_fmt___closed__1 = (const lean_object*)&l_Lean_IR_LogEntry_fmt___closed__1_value;
static lean_once_cell_t l_Lean_IR_LogEntry_fmt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__2;
static lean_once_cell_t l_Lean_IR_LogEntry_fmt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_LogEntry_fmt___closed__3;
static const lean_ctor_object l_Lean_IR_LogEntry_fmt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_LogEntry_fmt___closed__0_value)}};
static const lean_object* l_Lean_IR_LogEntry_fmt___closed__4 = (const lean_object*)&l_Lean_IR_LogEntry_fmt___closed__4_value;
static const lean_ctor_object l_Lean_IR_LogEntry_fmt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IR_LogEntry_fmt___closed__1_value)}};
static const lean_object* l_Lean_IR_LogEntry_fmt___closed__5 = (const lean_object*)&l_Lean_IR_LogEntry_fmt___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object*);
static const lean_closure_object l_Lean_IR_LogEntry_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_LogEntry_fmt, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_LogEntry_instToFormat___closed__0 = (const lean_object*)&l_Lean_IR_LogEntry_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_IR_LogEntry_instToFormat = (const lean_object*)&l_Lean_IR_LogEntry_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_log___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_IR_log___closed__0 = (const lean_object*)&l_Lean_IR_log___closed__0_value;
static const lean_string_object l_Lean_IR_log___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IR"};
static const lean_object* l_Lean_IR_log___closed__1 = (const lean_object*)&l_Lean_IR_log___closed__1_value;
static const lean_ctor_object l_Lean_IR_log___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_log___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_IR_log___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_log___closed__2_value_aux_0),((lean_object*)&l_Lean_IR_log___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 183, 71, 31, 86, 224, 207, 192)}};
static const lean_object* l_Lean_IR_log___closed__2 = (const lean_object*)&l_Lean_IR_log___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_tracePrefixOptionName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_IR_tracePrefixOptionName___closed__0 = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__0_value;
static const lean_string_object l_Lean_IR_tracePrefixOptionName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l_Lean_IR_tracePrefixOptionName___closed__1 = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__1_value;
static const lean_string_object l_Lean_IR_tracePrefixOptionName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Lean_IR_tracePrefixOptionName___closed__2 = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__2_value;
static const lean_ctor_object l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_0),((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 121, 176, 5, 201, 231, 94, 72)}};
static const lean_ctor_object l_Lean_IR_tracePrefixOptionName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__3_value_aux_1),((lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 180, 88, 7, 84, 16, 192, 27)}};
static const lean_object* l_Lean_IR_tracePrefixOptionName___closed__3 = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_IR_tracePrefixOptionName = (const lean_object*)&l_Lean_IR_tracePrefixOptionName___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object*);
static const lean_array_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(135, 186, 94, 176, 136, 38, 52, 11)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "declMapExt"};
static const lean_object* l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_IR_log___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 220, 115, 150, 240, 139, 111, 12)}};
static const lean_ctor_object l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 236, 150, 45, 29, 146, 124, 106)}};
static const lean_object* l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed, .m_arity = 7, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value),((lean_object*)&l_Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_declMapExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0_value;
static const lean_closure_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2;
static const lean_ctor_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3_value;
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_findEnvDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_findEnvDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IR_getDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown declaration `"};
static const lean_object* l_Lean_IR_getDecl___closed__0 = (const lean_object*)&l_Lean_IR_getDecl___closed__0_value;
static const lean_string_object l_Lean_IR_getDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_IR_getDecl___closed__1 = (const lean_object*)&l_Lean_IR_getDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object*);
static lean_once_cell_t l_Lean_IR_addDecl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addDecl___redArg___closed__0;
static lean_once_cell_t l_Lean_IR_addDecl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addDecl___redArg___closed__1;
static lean_once_cell_t l_Lean_IR_addDecl___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0_value;
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_IR_LogEntry_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_cls_8_; lean_object* v_decls_9_; lean_object* v___x_10_; 
v_cls_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_cls_8_);
v_decls_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc_ref(v_decls_9_);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_cls_8_, v_decls_9_);
return v___x_10_;
}
else
{
lean_object* v_msg_11_; lean_object* v___x_12_; 
v_msg_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_msg_11_);
lean_dec_ref(v_t_6_);
v___x_12_ = lean_apply_1(v_k_7_, v_msg_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_IR_LogEntry_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim___redArg(lean_object* v_t_25_, lean_object* v_step_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_25_, v_step_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_step_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_step_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_29_, v_step_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim___redArg(lean_object* v_t_33_, lean_object* v_message_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_33_, v_message_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_message_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_message_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_IR_LogEntry_ctorElim___redArg(v_t_37_, v_message_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_IR_LogEntry_fmt_spec__0(lean_object* v_a_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_nat_to_int(v_a_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(lean_object* v_as_43_, size_t v_i_44_, size_t v_stop_45_, lean_object* v_b_46_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = lean_usize_dec_eq(v_i_44_, v_stop_45_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; size_t v___x_54_; size_t v___x_55_; 
v___x_48_ = lean_array_uget_borrowed(v_as_43_, v_i_44_);
v___x_49_ = lean_box(1);
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v_b_46_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_48_);
v___x_52_ = l_Lean_IR_formatDecl(v___x_48_, v___x_51_);
v___x_53_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_add(v_i_44_, v___x_54_);
v_i_44_ = v___x_55_;
v_b_46_ = v___x_53_;
goto _start;
}
else
{
return v_b_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1___boxed(lean_object* v_as_57_, lean_object* v_i_58_, lean_object* v_stop_59_, lean_object* v_b_60_){
_start:
{
size_t v_i_boxed_61_; size_t v_stop_boxed_62_; lean_object* v_res_63_; 
v_i_boxed_61_ = lean_unbox_usize(v_i_58_);
lean_dec(v_i_58_);
v_stop_boxed_62_ = lean_unbox_usize(v_stop_59_);
lean_dec(v_stop_59_);
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_as_57_, v_i_boxed_61_, v_stop_boxed_62_, v_b_60_);
lean_dec_ref(v_as_57_);
return v_res_63_;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__2(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__0));
v___x_67_ = lean_string_length(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_IR_LogEntry_fmt___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&l_Lean_IR_LogEntry_fmt___closed__2, &l_Lean_IR_LogEntry_fmt___closed__2_once, _init_l_Lean_IR_LogEntry_fmt___closed__2);
v___x_69_ = lean_nat_to_int(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LogEntry_fmt(lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v_cls_75_; lean_object* v_decls_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_108_; 
v_cls_75_ = lean_ctor_get(v_x_74_, 0);
v_decls_76_ = lean_ctor_get(v_x_74_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_108_ == 0)
{
v___x_78_ = v_x_74_;
v_isShared_79_ = v_isSharedCheck_108_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_decls_76_);
lean_inc(v_cls_75_);
lean_dec(v_x_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_108_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_80_ = 1;
v___x_81_ = l_Lean_Name_toString(v_cls_75_, v___x_80_);
v___x_82_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
v___x_83_ = lean_obj_once(&l_Lean_IR_LogEntry_fmt___closed__3, &l_Lean_IR_LogEntry_fmt___closed__3_once, _init_l_Lean_IR_LogEntry_fmt___closed__3);
v___x_84_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__4));
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 5);
lean_ctor_set(v___x_78_, 1, v___x_82_);
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_86_ = v___x_78_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_82_);
v___x_86_ = v_reuseFailAlloc_107_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_87_ = ((lean_object*)(l_Lean_IR_LogEntry_fmt___closed__5));
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_83_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = lean_box(0);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_array_get_size(v_decls_76_);
v___x_95_ = lean_nat_dec_lt(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec_ref(v_decls_76_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_92_);
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = lean_nat_dec_le(v___x_94_, v___x_94_);
if (v___x_97_ == 0)
{
if (v___x_95_ == 0)
{
lean_object* v___x_98_; 
lean_dec_ref(v_decls_76_);
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_91_);
lean_ctor_set(v___x_98_, 1, v___x_92_);
return v___x_98_;
}
else
{
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = ((size_t)0ULL);
v___x_100_ = lean_usize_of_nat(v___x_94_);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_76_, v___x_99_, v___x_100_, v___x_92_);
lean_dec_ref(v_decls_76_);
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_91_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
return v___x_102_;
}
}
else
{
size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_103_ = ((size_t)0ULL);
v___x_104_ = lean_usize_of_nat(v___x_94_);
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LogEntry_fmt_spec__1(v_decls_76_, v___x_103_, v___x_104_, v___x_92_);
lean_dec_ref(v_decls_76_);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_91_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
return v___x_106_;
}
}
}
}
}
else
{
lean_object* v_msg_109_; 
v_msg_109_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_msg_109_);
lean_dec_ref(v_x_74_);
return v_msg_109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_, lean_object* v_b_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_usize_dec_eq(v_i_113_, v_stop_114_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; size_t v___x_122_; size_t v___x_123_; 
v___x_117_ = lean_array_uget_borrowed(v_as_112_, v_i_113_);
v___x_118_ = lean_box(1);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v_b_115_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
lean_inc(v___x_117_);
v___x_120_ = l_Lean_IR_LogEntry_fmt(v___x_117_);
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = ((size_t)1ULL);
v___x_123_ = lean_usize_add(v_i_113_, v___x_122_);
v_i_113_ = v___x_123_;
v_b_115_ = v___x_121_;
goto _start;
}
else
{
return v_b_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0___boxed(lean_object* v_as_125_, lean_object* v_i_126_, lean_object* v_stop_127_, lean_object* v_b_128_){
_start:
{
size_t v_i_boxed_129_; size_t v_stop_boxed_130_; lean_object* v_res_131_; 
v_i_boxed_129_ = lean_unbox_usize(v_i_126_);
lean_dec(v_i_126_);
v_stop_boxed_130_ = lean_unbox_usize(v_stop_127_);
lean_dec(v_stop_127_);
v_res_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_as_125_, v_i_boxed_129_, v_stop_boxed_130_, v_b_128_);
lean_dec_ref(v_as_125_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format(lean_object* v_log_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_133_ = lean_box(0);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_array_get_size(v_log_132_);
v___x_136_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
return v___x_133_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = lean_nat_dec_le(v___x_135_, v___x_135_);
if (v___x_137_ == 0)
{
if (v___x_136_ == 0)
{
return v___x_133_;
}
else
{
size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((size_t)0ULL);
v___x_139_ = lean_usize_of_nat(v___x_135_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_132_, v___x_138_, v___x_139_, v___x_133_);
return v___x_140_;
}
}
else
{
size_t v___x_141_; size_t v___x_142_; lean_object* v___x_143_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_135_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Log_format_spec__0(v_log_132_, v___x_141_, v___x_142_, v___x_133_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_format___boxed(lean_object* v_log_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_IR_Log_format(v_log_144_);
lean_dec_ref(v_log_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString(lean_object* v_log_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = l_Lean_IR_Log_format(v_log_146_);
v___x_148_ = l_Std_Format_defWidth;
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l_Std_Format_pretty(v___x_147_, v___x_148_, v___x_149_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Log_toString___boxed(lean_object* v_log_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_IR_Log_toString(v_log_151_);
lean_dec_ref(v_log_151_);
return v_res_152_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__0);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
lean_ctor_set(v___x_158_, 3, v___x_156_);
lean_ctor_set(v___x_158_, 4, v___x_156_);
lean_ctor_set(v___x_158_, 5, v___x_156_);
lean_ctor_set(v___x_158_, 6, v___x_156_);
lean_ctor_set(v___x_158_, 7, v___x_156_);
lean_ctor_set(v___x_158_, 8, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_unsigned_to_nat(32u);
v___x_160_ = lean_mk_empty_array_with_capacity(v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_162_ = ((size_t)5ULL);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_unsigned_to_nat(32u);
v___x_165_ = lean_mk_empty_array_with_capacity(v___x_164_);
v___x_166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__3);
v___x_167_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
lean_ctor_set(v___x_167_, 2, v___x_163_);
lean_ctor_set(v___x_167_, 3, v___x_163_);
lean_ctor_set_usize(v___x_167_, 4, v___x_162_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_box(1);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__4);
v___x_170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__1);
v___x_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(lean_object* v_msgData_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; lean_object* v_env_177_; lean_object* v_options_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_176_ = lean_st_ref_get(v___y_174_);
v_env_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_env_177_);
lean_dec(v___x_176_);
v_options_178_ = lean_ctor_get(v___y_173_, 2);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__2);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_178_);
v___x_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_181_, 0, v_env_177_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
lean_ctor_set(v___x_181_, 3, v_options_178_);
v___x_182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_msgData_172_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0___boxed(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msgData_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_188_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0(void){
_start:
{
lean_object* v___x_189_; double v___x_190_; 
v___x_189_ = lean_unsigned_to_nat(0u);
v___x_190_ = lean_float_of_nat(v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0(lean_object* v_cls_194_, lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_245_; 
v_ref_199_ = lean_ctor_get(v___y_196_, 5);
v___x_200_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_195_, v___y_196_, v___y_197_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_245_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_245_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_245_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v_traceState_206_; lean_object* v_env_207_; lean_object* v_nextMacroScope_208_; lean_object* v_ngen_209_; lean_object* v_auxDeclNGen_210_; lean_object* v_cache_211_; lean_object* v_messages_212_; lean_object* v_infoState_213_; lean_object* v_snapshotTasks_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_244_; 
v___x_205_ = lean_st_ref_take(v___y_197_);
v_traceState_206_ = lean_ctor_get(v___x_205_, 4);
v_env_207_ = lean_ctor_get(v___x_205_, 0);
v_nextMacroScope_208_ = lean_ctor_get(v___x_205_, 1);
v_ngen_209_ = lean_ctor_get(v___x_205_, 2);
v_auxDeclNGen_210_ = lean_ctor_get(v___x_205_, 3);
v_cache_211_ = lean_ctor_get(v___x_205_, 5);
v_messages_212_ = lean_ctor_get(v___x_205_, 6);
v_infoState_213_ = lean_ctor_get(v___x_205_, 7);
v_snapshotTasks_214_ = lean_ctor_get(v___x_205_, 8);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_244_ == 0)
{
v___x_216_ = v___x_205_;
v_isShared_217_ = v_isSharedCheck_244_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_snapshotTasks_214_);
lean_inc(v_infoState_213_);
lean_inc(v_messages_212_);
lean_inc(v_cache_211_);
lean_inc(v_traceState_206_);
lean_inc(v_auxDeclNGen_210_);
lean_inc(v_ngen_209_);
lean_inc(v_nextMacroScope_208_);
lean_inc(v_env_207_);
lean_dec(v___x_205_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_244_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
uint64_t v_tid_218_; lean_object* v_traces_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_243_; 
v_tid_218_ = lean_ctor_get_uint64(v_traceState_206_, sizeof(void*)*1);
v_traces_219_ = lean_ctor_get(v_traceState_206_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v_traceState_206_);
if (v_isSharedCheck_243_ == 0)
{
v___x_221_ = v_traceState_206_;
v_isShared_222_ = v_isSharedCheck_243_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_traces_219_);
lean_dec(v_traceState_206_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_243_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; double v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_223_ = lean_box(0);
v___x_224_ = lean_float_once(&l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__0);
v___x_225_ = 0;
v___x_226_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__1));
v___x_227_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_227_, 0, v_cls_194_);
lean_ctor_set(v___x_227_, 1, v___x_223_);
lean_ctor_set(v___x_227_, 2, v___x_226_);
lean_ctor_set_float(v___x_227_, sizeof(void*)*3, v___x_224_);
lean_ctor_set_float(v___x_227_, sizeof(void*)*3 + 8, v___x_224_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*3 + 16, v___x_225_);
v___x_228_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_IR_log_spec__0___closed__2));
v___x_229_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v_a_201_);
lean_ctor_set(v___x_229_, 2, v___x_228_);
lean_inc(v_ref_199_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v_ref_199_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_PersistentArray_push___redArg(v_traces_219_, v___x_230_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_231_);
v___x_233_ = v___x_221_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_231_);
lean_ctor_set_uint64(v_reuseFailAlloc_242_, sizeof(void*)*1, v_tid_218_);
v___x_233_ = v_reuseFailAlloc_242_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_235_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 4, v___x_233_);
v___x_235_ = v___x_216_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_env_207_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_nextMacroScope_208_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_ngen_209_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_auxDeclNGen_210_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_cache_211_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_messages_212_);
lean_ctor_set(v_reuseFailAlloc_241_, 7, v_infoState_213_);
lean_ctor_set(v_reuseFailAlloc_241_, 8, v_snapshotTasks_214_);
v___x_235_ = v_reuseFailAlloc_241_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_236_ = lean_st_ref_set(v___y_197_, v___x_235_);
v___x_237_ = lean_box(0);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_237_);
v___x_239_ = v___x_203_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_IR_log_spec__0___boxed(lean_object* v_cls_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v_cls_246_, v_msg_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log(lean_object* v_entry_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = ((lean_object*)(l_Lean_IR_log___closed__2));
v___x_262_ = l_Lean_IR_LogEntry_fmt(v_entry_257_);
v___x_263_ = l_Lean_MessageData_ofFormat(v___x_262_);
v___x_264_ = l_Lean_addTrace___at___00Lean_IR_log_spec__0(v___x_261_, v___x_263_, v_a_258_, v_a_259_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_log___boxed(lean_object* v_entry_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_IR_log(v_entry_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_269_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(lean_object* v_opts_278_, lean_object* v_optName_279_){
_start:
{
lean_object* v_map_280_; lean_object* v___x_287_; 
v_map_280_ = lean_ctor_get(v_opts_278_, 0);
v___x_287_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_280_, v_optName_279_);
if (lean_obj_tag(v___x_287_) == 1)
{
lean_object* v_val_288_; 
v_val_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_val_288_);
lean_dec_ref(v___x_287_);
if (lean_obj_tag(v_val_288_) == 1)
{
uint8_t v_v_289_; 
v_v_289_ = lean_ctor_get_uint8(v_val_288_, 0);
lean_dec_ref(v_val_288_);
return v_v_289_;
}
else
{
lean_dec(v_val_288_);
goto v___jp_281_;
}
}
else
{
lean_dec(v___x_287_);
goto v___jp_281_;
}
v___jp_281_:
{
lean_object* v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_283_ = 0;
v___x_284_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_280_, v___x_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
return v___x_283_;
}
else
{
lean_object* v_val_285_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref(v___x_284_);
if (lean_obj_tag(v_val_285_) == 1)
{
uint8_t v_v_286_; 
v_v_286_ = lean_ctor_get_uint8(v_val_285_, 0);
lean_dec_ref(v_val_285_);
return v_v_286_;
}
else
{
lean_dec(v_val_285_);
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor___boxed(lean_object* v_opts_290_, lean_object* v_optName_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_opts_290_, v_optName_291_);
lean_dec(v_optName_291_);
lean_dec_ref(v_opts_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object* v_optName_294_, lean_object* v_cls_295_, lean_object* v_decls_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_options_300_; uint8_t v___x_301_; 
v_options_300_ = lean_ctor_get(v_a_297_, 2);
v___x_301_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_options_300_, v_optName_294_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_decls_296_);
lean_dec(v_cls_295_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_cls_295_);
lean_ctor_set(v___x_304_, 1, v_decls_296_);
v___x_305_ = l_Lean_IR_log(v___x_304_, v_a_297_, v_a_298_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux___boxed(lean_object* v_optName_306_, lean_object* v_cls_307_, lean_object* v_decls_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v_optName_306_, v_cls_307_, v_decls_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_optName_306_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls(lean_object* v_cls_313_, lean_object* v_decl_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
lean_inc(v_cls_313_);
v___x_319_ = l_Lean_Name_append(v___x_318_, v_cls_313_);
v___x_320_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_319_, v_cls_313_, v_decl_314_, v_a_315_, v_a_316_);
lean_dec(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logDecls___boxed(lean_object* v_cls_321_, lean_object* v_decl_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_IR_logDecls(v_cls_321_, v_decl_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(lean_object* v_inst_327_, lean_object* v_optName_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_options_333_; uint8_t v___x_334_; 
v_options_333_ = lean_ctor_get(v_a_330_, 2);
v___x_334_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_isLogEnabledFor(v_options_333_, v_optName_328_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_a_329_);
lean_dec_ref(v_inst_327_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_apply_1(v_inst_327_, v_a_329_);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
v___x_339_ = l_Lean_IR_log(v___x_338_, v_a_330_, v_a_331_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg___boxed(lean_object* v_inst_340_, lean_object* v_optName_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_340_, v_optName_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_optName_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(lean_object* v_00_u03b1_347_, lean_object* v_inst_348_, lean_object* v_optName_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_348_, v_optName_349_, v_a_350_, v_a_351_, v_a_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___boxed(lean_object* v_00_u03b1_355_, lean_object* v_inst_356_, lean_object* v_optName_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux(v_00_u03b1_355_, v_inst_356_, v_optName_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_optName_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg(lean_object* v_inst_363_, lean_object* v_cls_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_370_ = l_Lean_Name_append(v___x_369_, v_cls_364_);
v___x_371_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_363_, v___x_370_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___redArg___boxed(lean_object* v_inst_372_, lean_object* v_cls_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_IR_logMessageIf___redArg(v_inst_372_, v_cls_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf(lean_object* v_00_u03b1_379_, lean_object* v_inst_380_, lean_object* v_cls_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_387_ = l_Lean_Name_append(v___x_386_, v_cls_381_);
v___x_388_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_380_, v___x_387_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessageIf___boxed(lean_object* v_00_u03b1_389_, lean_object* v_inst_390_, lean_object* v_cls_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_IR_logMessageIf(v_00_u03b1_389_, v_inst_390_, v_cls_391_, v_a_392_, v_a_393_, v_a_394_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg(lean_object* v_inst_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_403_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_397_, v___x_402_, v_a_398_, v_a_399_, v_a_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___redArg___boxed(lean_object* v_inst_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_IR_logMessage___redArg(v_inst_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage(lean_object* v_00_u03b1_410_, lean_object* v_inst_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_IR_tracePrefixOptionName));
v___x_417_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logMessageIfAux___redArg(v_inst_411_, v___x_416_, v_a_412_, v_a_413_, v_a_414_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_logMessage___boxed(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_IR_logMessage(v_00_u03b1_418_, v_inst_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_424_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(lean_object* v_a_425_, lean_object* v_b_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_427_ = l_Lean_IR_Decl_name(v_a_425_);
v___x_428_ = l_Lean_IR_Decl_name(v_b_426_);
v___x_429_ = l_Lean_Name_quickLt(v___x_427_, v___x_428_);
lean_dec(v___x_428_);
lean_dec(v___x_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt___boxed(lean_object* v_a_430_, lean_object* v_b_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_declLt(v_a_430_, v_b_431_);
lean_dec_ref(v_b_431_);
lean_dec_ref(v_a_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls(lean_object* v_decls_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = lean_array_get_size(v_decls_435_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_nat_dec_eq(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___y_443_; uint8_t v___x_447_; 
v___x_439_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_sub(v___x_436_, v___x_440_);
v___x_447_ = lean_nat_dec_le(v___x_437_, v___x_441_);
if (v___x_447_ == 0)
{
lean_inc(v___x_441_);
v___y_443_ = v___x_441_;
goto v___jp_442_;
}
else
{
v___y_443_ = v___x_437_;
goto v___jp_442_;
}
v___jp_442_:
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_le(v___y_443_, v___x_441_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v___x_441_);
lean_inc(v___y_443_);
v___x_445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_439_, v___x_436_, v_decls_435_, v___y_443_, v___y_443_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_443_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___x_439_, v___x_436_, v_decls_435_, v___y_443_, v___x_441_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___x_441_);
return v___x_446_;
}
}
}
else
{
return v_decls_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(lean_object* v_decls_451_, lean_object* v_declName_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_array_get_size(v_decls_451_);
v___x_455_ = lean_nat_dec_lt(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_dec(v_declName_452_);
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_sub(v___x_454_, v___x_457_);
v___x_459_ = lean_nat_dec_le(v___x_453_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v___x_458_);
lean_dec(v_declName_452_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_tmpDecl_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_462_ = lean_box(0);
v___x_463_ = l_Lean_instInhabitedExternAttrData_default;
v_tmpDecl_464_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_464_, 0, v_declName_452_);
lean_ctor_set(v_tmpDecl_464_, 1, v___x_461_);
lean_ctor_set(v_tmpDecl_464_, 2, v___x_462_);
lean_ctor_set(v_tmpDecl_464_, 3, v___x_463_);
v___x_465_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_sortDecls___closed__0));
v___x_466_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__1));
v___x_467_ = l_Array_binSearchAux___redArg(v___x_465_, v___x_466_, v_decls_451_, v_tmpDecl_464_, v___x_453_, v___x_458_);
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___boxed(lean_object* v_decls_468_, lean_object* v_declName_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f(v_decls_468_, v_declName_469_);
lean_dec_ref(v_decls_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__1(lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
return v_x_471_;
}
else
{
lean_object* v_head_473_; lean_object* v_tail_474_; lean_object* v___x_475_; 
v_head_473_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_head_473_);
v_tail_474_ = lean_ctor_get(v_x_472_, 1);
lean_inc(v_tail_474_);
lean_dec_ref(v_x_472_);
v___x_475_ = lean_array_push(v_x_471_, v_head_473_);
v_x_471_ = v___x_475_;
v_x_472_ = v_tail_474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_env_483_, lean_object* v_as_484_, size_t v_i_485_, size_t v_stop_486_, lean_object* v_b_487_){
_start:
{
lean_object* v___y_489_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; uint8_t v___x_500_; 
v___x_500_ = lean_usize_dec_eq(v_i_485_, v_stop_486_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; uint8_t v___y_503_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_501_ = lean_array_uget_borrowed(v_as_484_, v_i_485_);
v___x_518_ = l_Lean_IR_Decl_name(v___x_501_);
lean_inc_ref(v_env_483_);
v___x_519_ = l_Lean_isDeclMeta(v_env_483_, v___x_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; 
lean_inc_ref(v_env_483_);
v___x_520_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_483_, v___x_518_);
if (v___x_520_ == 0)
{
lean_dec(v___x_518_);
v___y_489_ = v_b_487_;
goto v___jp_488_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = l_Lean_Compiler_LCNF_isBoxedName(v___x_518_);
if (v___x_521_ == 0)
{
lean_dec(v___x_518_);
v___y_503_ = v___x_521_;
goto v___jp_502_;
}
else
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = l_Lean_Name_getPrefix(v___x_518_);
lean_dec(v___x_518_);
lean_inc_ref(v_env_483_);
v___x_523_ = l_Lean_isExtern(v_env_483_, v___x_522_);
v___y_503_ = v___x_523_;
goto v___jp_502_;
}
}
}
else
{
lean_object* v___x_524_; 
lean_dec(v___x_518_);
lean_inc(v___x_501_);
v___x_524_ = lean_array_push(v_b_487_, v___x_501_);
v___y_489_ = v___x_524_;
goto v___jp_488_;
}
v___jp_502_:
{
if (v___y_503_ == 0)
{
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_f_504_; lean_object* v_xs_505_; lean_object* v_type_506_; lean_object* v___x_507_; 
v_f_504_ = lean_ctor_get(v___x_501_, 0);
v_xs_505_ = lean_ctor_get(v___x_501_, 1);
v_type_506_ = lean_ctor_get(v___x_501_, 2);
lean_inc(v_f_504_);
lean_inc_ref(v_env_483_);
v___x_507_ = lean_get_export_name_for(v_env_483_, v_f_504_);
if (lean_obj_tag(v___x_507_) == 1)
{
lean_object* v_val_508_; 
v_val_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_val_508_);
lean_dec_ref(v___x_507_);
if (lean_obj_tag(v_val_508_) == 1)
{
lean_object* v_str_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_str_509_ = lean_ctor_get(v_val_508_, 1);
lean_inc_ref(v_str_509_);
lean_dec_ref(v_val_508_);
v___x_510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__2));
v___x_511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v_str_509_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
lean_inc(v_type_506_);
lean_inc_ref(v_xs_505_);
lean_inc(v_f_504_);
v___x_514_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_514_, 0, v_f_504_);
lean_ctor_set(v___x_514_, 1, v_xs_505_);
lean_ctor_set(v___x_514_, 2, v_type_506_);
lean_ctor_set(v___x_514_, 3, v___x_513_);
v___x_515_ = lean_array_push(v_b_487_, v___x_514_);
v___y_489_ = v___x_515_;
goto v___jp_488_;
}
else
{
lean_dec(v_val_508_);
lean_inc_ref(v_xs_505_);
lean_inc(v_f_504_);
lean_inc(v_type_506_);
v___y_494_ = v_type_506_;
v___y_495_ = v_f_504_;
v___y_496_ = v_xs_505_;
goto v___jp_493_;
}
}
else
{
lean_dec(v___x_507_);
lean_inc_ref(v_xs_505_);
lean_inc(v_f_504_);
lean_inc(v_type_506_);
v___y_494_ = v_type_506_;
v___y_495_ = v_f_504_;
v___y_496_ = v_xs_505_;
goto v___jp_493_;
}
}
else
{
lean_object* v___x_516_; 
lean_inc(v___x_501_);
v___x_516_ = lean_array_push(v_b_487_, v___x_501_);
v___y_489_ = v___x_516_;
goto v___jp_488_;
}
}
else
{
lean_object* v___x_517_; 
lean_inc(v___x_501_);
v___x_517_ = lean_array_push(v_b_487_, v___x_501_);
v___y_489_ = v___x_517_;
goto v___jp_488_;
}
}
}
else
{
lean_dec_ref(v_env_483_);
return v_b_487_;
}
v___jp_488_:
{
size_t v___x_490_; size_t v___x_491_; 
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_485_, v___x_490_);
v_i_485_ = v___x_491_;
v_b_487_ = v___y_489_;
goto _start;
}
v___jp_493_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___closed__0));
v___x_498_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_498_, 0, v___y_495_);
lean_ctor_set(v___x_498_, 1, v___y_496_);
lean_ctor_set(v___x_498_, 2, v___y_494_);
lean_ctor_set(v___x_498_, 3, v___x_497_);
v___x_499_ = lean_array_push(v_b_487_, v___x_498_);
v___y_489_ = v___x_499_;
goto v___jp_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_env_525_, lean_object* v_as_526_, lean_object* v_i_527_, lean_object* v_stop_528_, lean_object* v_b_529_){
_start:
{
size_t v_i_boxed_530_; size_t v_stop_boxed_531_; lean_object* v_res_532_; 
v_i_boxed_530_ = lean_unbox_usize(v_i_527_);
lean_dec(v_i_527_);
v_stop_boxed_531_ = lean_unbox_usize(v_stop_528_);
lean_dec(v_stop_528_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0(v_env_525_, v_as_526_, v_i_boxed_530_, v_stop_boxed_531_, v_b_529_);
lean_dec_ref(v_as_526_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0(lean_object* v_env_535_, lean_object* v_as_536_, lean_object* v_start_537_, lean_object* v_stop_538_){
_start:
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0___closed__0));
v___x_540_ = lean_nat_dec_lt(v_start_537_, v_stop_538_);
if (v___x_540_ == 0)
{
lean_dec_ref(v_env_535_);
return v___x_539_;
}
else
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_array_get_size(v_as_536_);
v___x_542_ = lean_nat_dec_le(v_stop_538_, v___x_541_);
if (v___x_542_ == 0)
{
uint8_t v___x_543_; 
v___x_543_ = lean_nat_dec_lt(v_start_537_, v___x_541_);
if (v___x_543_ == 0)
{
lean_dec_ref(v_env_535_);
return v___x_539_;
}
else
{
size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_usize_of_nat(v_start_537_);
v___x_545_ = lean_usize_of_nat(v___x_541_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0(v_env_535_, v_as_536_, v___x_544_, v___x_545_, v___x_539_);
return v___x_546_;
}
}
else
{
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_usize_of_nat(v_start_537_);
v___x_548_ = lean_usize_of_nat(v_stop_538_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0_spec__0(v_env_535_, v_as_536_, v___x_547_, v___x_548_, v___x_539_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_550_, lean_object* v_as_551_, lean_object* v_start_552_, lean_object* v_stop_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0(v_env_550_, v_as_551_, v_start_552_, v_stop_553_);
lean_dec(v_stop_553_);
lean_dec(v_start_552_);
lean_dec_ref(v_as_551_);
return v_res_554_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___lam__0(lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = l_Lean_IR_Decl_name(v___y_555_);
v___x_558_ = l_Lean_IR_Decl_name(v___y_556_);
v___x_559_ = l_Lean_Name_quickLt(v___x_557_, v___x_558_);
lean_dec(v___x_558_);
lean_dec(v___x_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___lam__0___boxed(lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___lam__0(v___y_560_, v___y_561_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v___y_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_565_, lean_object* v_lo_566_, lean_object* v_hi_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_nat_dec_lt(v_lo_566_, v_hi_567_);
if (v___x_568_ == 0)
{
lean_dec(v_lo_566_);
return v_as_565_;
}
else
{
lean_object* v___f_569_; lean_object* v___x_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; uint8_t v___x_573_; 
v___f_569_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_566_);
v___x_570_ = l_Array_qpartition___redArg(v_as_565_, v___f_569_, v_lo_566_, v_hi_567_);
v_fst_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_fst_571_);
v_snd_572_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_snd_572_);
lean_dec_ref(v___x_570_);
v___x_573_ = lean_nat_dec_le(v_hi_567_, v_fst_571_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg(v_snd_572_, v_lo_566_, v_fst_571_);
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_fst_571_, v___x_575_);
lean_dec(v_fst_571_);
v_as_565_ = v___x_574_;
v_lo_566_ = v___x_576_;
goto _start;
}
else
{
lean_dec(v_fst_571_);
lean_dec(v_lo_566_);
return v_snd_572_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_578_, lean_object* v_lo_579_, lean_object* v_hi_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg(v_as_578_, v_lo_579_, v_hi_580_);
lean_dec(v_hi_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object* v_env_582_, lean_object* v_s_583_, lean_object* v_entries_584_, uint8_t v_x_585_){
_start:
{
lean_object* v___y_587_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_decls_595_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0___closed__0));
v_decls_595_ = l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__1(v___x_594_, v_entries_584_);
v___x_600_ = lean_array_get_size(v_decls_595_);
v___x_601_ = lean_nat_dec_eq(v___x_600_, v___x_593_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___y_605_; uint8_t v___x_607_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_sub(v___x_600_, v___x_602_);
v___x_607_ = lean_nat_dec_le(v___x_593_, v___x_603_);
if (v___x_607_ == 0)
{
lean_inc(v___x_603_);
v___y_605_ = v___x_603_;
goto v___jp_604_;
}
else
{
v___y_605_ = v___x_593_;
goto v___jp_604_;
}
v___jp_604_:
{
uint8_t v___x_606_; 
v___x_606_ = lean_nat_dec_le(v___y_605_, v___x_603_);
if (v___x_606_ == 0)
{
lean_dec(v___x_603_);
lean_inc(v___y_605_);
v___y_597_ = v___y_605_;
v___y_598_ = v___y_605_;
goto v___jp_596_;
}
else
{
v___y_597_ = v___y_605_;
v___y_598_ = v___x_603_;
goto v___jp_596_;
}
}
}
else
{
v___y_587_ = v_decls_595_;
goto v___jp_586_;
}
v___jp_586_:
{
lean_object* v___x_588_; uint8_t v_isModule_589_; 
v___x_588_ = l_Lean_Environment_header(v_env_582_);
v_isModule_589_ = lean_ctor_get_uint8(v___x_588_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_588_);
if (v_isModule_589_ == 0)
{
lean_dec_ref(v_env_582_);
return v___y_587_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_array_get_size(v___y_587_);
v___x_592_ = l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0(v_env_582_, v___y_587_, v___x_590_, v___x_591_);
lean_dec_ref(v___y_587_);
return v___x_592_;
}
}
v___jp_596_:
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg(v_decls_595_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
v___y_587_ = v___x_599_;
goto v___jp_586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed(lean_object* v_env_608_, lean_object* v_s_609_, lean_object* v_entries_610_, lean_object* v_x_611_){
_start:
{
uint8_t v_x_2376__boxed_612_; lean_object* v_res_613_; 
v_x_2376__boxed_612_ = lean_unbox(v_x_611_);
v_res_613_ = l_Lean_IR_initFn___lam__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(v_env_608_, v_s_609_, v_entries_610_, v_x_2376__boxed_612_);
lean_dec_ref(v_s_609_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object* v_es_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_mk(v_es_614_);
return v___x_615_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(lean_object* v_keys_616_, lean_object* v_i_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_array_get_size(v_keys_616_);
v___x_620_ = lean_nat_dec_lt(v_i_617_, v___x_619_);
if (v___x_620_ == 0)
{
lean_dec(v_i_617_);
return v___x_620_;
}
else
{
lean_object* v_k_x27_621_; uint8_t v___x_622_; 
v_k_x27_621_ = lean_array_fget_borrowed(v_keys_616_, v_i_617_);
v___x_622_ = lean_name_eq(v_k_618_, v_k_x27_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v_i_617_, v___x_623_);
lean_dec(v_i_617_);
v_i_617_ = v___x_624_;
goto _start;
}
else
{
lean_dec(v_i_617_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_keys_626_, lean_object* v_i_627_, lean_object* v_k_628_){
_start:
{
uint8_t v_res_629_; lean_object* v_r_630_; 
v_res_629_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_keys_626_, v_i_627_, v_k_628_);
lean_dec(v_k_628_);
lean_dec_ref(v_keys_626_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; 
v___x_631_ = ((size_t)5ULL);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_shift_left(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_634_; size_t v___x_635_; size_t v___x_636_; 
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0);
v___x_636_ = lean_usize_sub(v___x_635_, v___x_634_);
return v___x_636_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object* v_x_637_, size_t v_x_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v_es_640_; lean_object* v___x_641_; size_t v___x_642_; size_t v___x_643_; size_t v___x_644_; lean_object* v_j_645_; lean_object* v___x_646_; 
v_es_640_ = lean_ctor_get(v_x_637_, 0);
v___x_641_ = lean_box(2);
v___x_642_ = ((size_t)5ULL);
v___x_643_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_644_ = lean_usize_land(v_x_638_, v___x_643_);
v_j_645_ = lean_usize_to_nat(v___x_644_);
v___x_646_ = lean_array_get_borrowed(v___x_641_, v_es_640_, v_j_645_);
lean_dec(v_j_645_);
switch(lean_obj_tag(v___x_646_))
{
case 0:
{
lean_object* v_key_647_; uint8_t v___x_648_; 
v_key_647_ = lean_ctor_get(v___x_646_, 0);
v___x_648_ = lean_name_eq(v_x_639_, v_key_647_);
return v___x_648_;
}
case 1:
{
lean_object* v_node_649_; size_t v___x_650_; 
v_node_649_ = lean_ctor_get(v___x_646_, 0);
v___x_650_ = lean_usize_shift_right(v_x_638_, v___x_642_);
v_x_637_ = v_node_649_;
v_x_638_ = v___x_650_;
goto _start;
}
default: 
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
}
}
else
{
lean_object* v_ks_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_ks_653_ = lean_ctor_get(v_x_637_, 0);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_ks_653_, v___x_654_, v_x_639_);
return v___x_655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
size_t v_x_2446__boxed_659_; uint8_t v_res_660_; lean_object* v_r_661_; 
v_x_2446__boxed_659_ = lean_unbox_usize(v_x_657_);
lean_dec(v_x_657_);
v_res_660_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_656_, v_x_2446__boxed_659_, v_x_658_);
lean_dec(v_x_658_);
lean_dec_ref(v_x_656_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_662_; uint64_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(1723u);
v___x_663_ = lean_uint64_of_nat(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
uint64_t v___y_667_; 
if (lean_obj_tag(v_x_665_) == 0)
{
uint64_t v___x_670_; 
v___x_670_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_667_ = v___x_670_;
goto v___jp_666_;
}
else
{
uint64_t v_hash_671_; 
v_hash_671_ = lean_ctor_get_uint64(v_x_665_, sizeof(void*)*2);
v___y_667_ = v_hash_671_;
goto v___jp_666_;
}
v___jp_666_:
{
size_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_uint64_to_usize(v___y_667_);
v___x_669_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_664_, v___x_668_, v_x_665_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg(v_x_672_, v_x_673_);
lean_dec(v_x_673_);
lean_dec_ref(v_x_672_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object* v_x1_676_, lean_object* v_x2_677_){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = l_Lean_IR_Decl_name(v_x2_677_);
v___x_679_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg(v_x1_676_, v___x_678_);
lean_dec(v___x_678_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; 
v___x_680_ = 1;
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = 0;
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed(lean_object* v_x1_682_, lean_object* v_x2_683_){
_start:
{
uint8_t v_res_684_; lean_object* v_r_685_; 
v_res_684_ = l_Lean_IR_initFn___lam__2_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(v_x1_682_, v_x2_683_);
lean_dec_ref(v_x2_683_);
lean_dec_ref(v_x1_682_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_686_;
}
}
static lean_object* _init_l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_, &l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__once, _init_l_Lean_IR_initFn___lam__3___closed__0_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_, &l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__once, _init_l_Lean_IR_initFn___lam__3___closed__1_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed(lean_object* v_x_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_IR_initFn___lam__3_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(v_x_691_);
lean_dec_ref(v_x_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v_ks_697_; lean_object* v_vs_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_722_; 
v_ks_697_ = lean_ctor_get(v_x_693_, 0);
v_vs_698_ = lean_ctor_get(v_x_693_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_693_);
if (v_isSharedCheck_722_ == 0)
{
v___x_700_ = v_x_693_;
v_isShared_701_ = v_isSharedCheck_722_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_vs_698_);
lean_inc(v_ks_697_);
lean_dec(v_x_693_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_722_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_array_get_size(v_ks_697_);
v___x_703_ = lean_nat_dec_lt(v_x_694_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec(v_x_694_);
v___x_704_ = lean_array_push(v_ks_697_, v_x_695_);
v___x_705_ = lean_array_push(v_vs_698_, v_x_696_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_705_);
lean_ctor_set(v___x_700_, 0, v___x_704_);
v___x_707_ = v___x_700_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
else
{
lean_object* v_k_x27_709_; uint8_t v___x_710_; 
v_k_x27_709_ = lean_array_fget_borrowed(v_ks_697_, v_x_694_);
v___x_710_ = lean_name_eq(v_x_695_, v_k_x27_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_712_; 
if (v_isShared_701_ == 0)
{
v___x_712_ = v___x_700_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_ks_697_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_vs_698_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = lean_nat_add(v_x_694_, v___x_713_);
lean_dec(v_x_694_);
v_x_693_ = v___x_712_;
v_x_694_ = v___x_714_;
goto _start;
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_717_ = lean_array_fset(v_ks_697_, v_x_694_, v_x_695_);
v___x_718_ = lean_array_fset(v_vs_698_, v_x_694_, v_x_696_);
lean_dec(v_x_694_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_718_);
lean_ctor_set(v___x_700_, 0, v___x_717_);
v___x_720_ = v___x_700_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(lean_object* v_n_723_, lean_object* v_k_724_, lean_object* v_v_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(v_n_723_, v___x_726_, v_k_724_, v_v_725_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg(lean_object* v_x_729_, size_t v_x_730_, size_t v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_729_) == 0)
{
lean_object* v_es_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; size_t v___x_738_; lean_object* v_j_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_es_734_ = lean_ctor_get(v_x_729_, 0);
v___x_735_ = ((size_t)5ULL);
v___x_736_ = ((size_t)1ULL);
v___x_737_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_738_ = lean_usize_land(v_x_730_, v___x_737_);
v_j_739_ = lean_usize_to_nat(v___x_738_);
v___x_740_ = lean_array_get_size(v_es_734_);
v___x_741_ = lean_nat_dec_lt(v_j_739_, v___x_740_);
if (v___x_741_ == 0)
{
lean_dec(v_j_739_);
lean_dec(v_x_733_);
lean_dec(v_x_732_);
return v_x_729_;
}
else
{
lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_778_; 
lean_inc_ref(v_es_734_);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_729_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_x_729_, 0);
lean_dec(v_unused_779_);
v___x_743_ = v_x_729_;
v_isShared_744_ = v_isSharedCheck_778_;
goto v_resetjp_742_;
}
else
{
lean_dec(v_x_729_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_778_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_v_745_; lean_object* v___x_746_; lean_object* v_xs_x27_747_; lean_object* v___y_749_; 
v_v_745_ = lean_array_fget(v_es_734_, v_j_739_);
v___x_746_ = lean_box(0);
v_xs_x27_747_ = lean_array_fset(v_es_734_, v_j_739_, v___x_746_);
switch(lean_obj_tag(v_v_745_))
{
case 0:
{
lean_object* v_key_754_; lean_object* v_val_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_765_; 
v_key_754_ = lean_ctor_get(v_v_745_, 0);
v_val_755_ = lean_ctor_get(v_v_745_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_v_745_);
if (v_isSharedCheck_765_ == 0)
{
v___x_757_ = v_v_745_;
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_val_755_);
lean_inc(v_key_754_);
lean_dec(v_v_745_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_765_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
uint8_t v___x_759_; 
v___x_759_ = lean_name_eq(v_x_732_, v_key_754_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_del_object(v___x_757_);
v___x_760_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_754_, v_val_755_, v_x_732_, v_x_733_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v___y_749_ = v___x_761_;
goto v___jp_748_;
}
else
{
lean_object* v___x_763_; 
lean_dec(v_val_755_);
lean_dec(v_key_754_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v_x_733_);
lean_ctor_set(v___x_757_, 0, v_x_732_);
v___x_763_ = v___x_757_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_x_732_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_x_733_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
v___y_749_ = v___x_763_;
goto v___jp_748_;
}
}
}
}
case 1:
{
lean_object* v_node_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_776_; 
v_node_766_ = lean_ctor_get(v_v_745_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v_v_745_);
if (v_isSharedCheck_776_ == 0)
{
v___x_768_ = v_v_745_;
v_isShared_769_ = v_isSharedCheck_776_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_node_766_);
lean_dec(v_v_745_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_776_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_770_ = lean_usize_shift_right(v_x_730_, v___x_735_);
v___x_771_ = lean_usize_add(v_x_731_, v___x_736_);
v___x_772_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg(v_node_766_, v___x_770_, v___x_771_, v_x_732_, v_x_733_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_772_);
v___x_774_ = v___x_768_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
v___y_749_ = v___x_774_;
goto v___jp_748_;
}
}
}
default: 
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_x_732_);
lean_ctor_set(v___x_777_, 1, v_x_733_);
v___y_749_ = v___x_777_;
goto v___jp_748_;
}
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_array_fset(v_xs_x27_747_, v_j_739_, v___y_749_);
lean_dec(v_j_739_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_750_);
v___x_752_ = v___x_743_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
else
{
lean_object* v_ks_780_; lean_object* v_vs_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_801_; 
v_ks_780_ = lean_ctor_get(v_x_729_, 0);
v_vs_781_ = lean_ctor_get(v_x_729_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_729_);
if (v_isSharedCheck_801_ == 0)
{
v___x_783_ = v_x_729_;
v_isShared_784_ = v_isSharedCheck_801_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_vs_781_);
lean_inc(v_ks_780_);
lean_dec(v_x_729_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_801_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_ks_780_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_vs_781_);
v___x_786_ = v_reuseFailAlloc_800_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v_newNode_787_; uint8_t v___y_789_; size_t v___x_795_; uint8_t v___x_796_; 
v_newNode_787_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v___x_786_, v_x_732_, v_x_733_);
v___x_795_ = ((size_t)7ULL);
v___x_796_ = lean_usize_dec_le(v___x_795_, v_x_731_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_787_);
v___x_798_ = lean_unsigned_to_nat(4u);
v___x_799_ = lean_nat_dec_lt(v___x_797_, v___x_798_);
lean_dec(v___x_797_);
v___y_789_ = v___x_799_;
goto v___jp_788_;
}
else
{
v___y_789_ = v___x_796_;
goto v___jp_788_;
}
v___jp_788_:
{
if (v___y_789_ == 0)
{
lean_object* v_ks_790_; lean_object* v_vs_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_ks_790_ = lean_ctor_get(v_newNode_787_, 0);
lean_inc_ref(v_ks_790_);
v_vs_791_ = lean_ctor_get(v_newNode_787_, 1);
lean_inc_ref(v_vs_791_);
lean_dec_ref(v_newNode_787_);
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg___closed__0);
v___x_794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_x_731_, v_ks_790_, v_vs_791_, v___x_792_, v___x_793_);
lean_dec_ref(v_vs_791_);
lean_dec_ref(v_ks_790_);
return v___x_794_;
}
else
{
return v_newNode_787_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(size_t v_depth_802_, lean_object* v_keys_803_, lean_object* v_vals_804_, lean_object* v_i_805_, lean_object* v_entries_806_){
_start:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_array_get_size(v_keys_803_);
v___x_808_ = lean_nat_dec_lt(v_i_805_, v___x_807_);
if (v___x_808_ == 0)
{
lean_dec(v_i_805_);
return v_entries_806_;
}
else
{
lean_object* v_k_809_; lean_object* v_v_810_; uint64_t v___y_812_; 
v_k_809_ = lean_array_fget_borrowed(v_keys_803_, v_i_805_);
v_v_810_ = lean_array_fget_borrowed(v_vals_804_, v_i_805_);
if (lean_obj_tag(v_k_809_) == 0)
{
uint64_t v___x_823_; 
v___x_823_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_812_ = v___x_823_;
goto v___jp_811_;
}
else
{
uint64_t v_hash_824_; 
v_hash_824_ = lean_ctor_get_uint64(v_k_809_, sizeof(void*)*2);
v___y_812_ = v_hash_824_;
goto v___jp_811_;
}
v___jp_811_:
{
size_t v_h_813_; size_t v___x_814_; lean_object* v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v_h_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_h_813_ = lean_uint64_to_usize(v___y_812_);
v___x_814_ = ((size_t)5ULL);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_sub(v_depth_802_, v___x_816_);
v___x_818_ = lean_usize_mul(v___x_814_, v___x_817_);
v_h_819_ = lean_usize_shift_right(v_h_813_, v___x_818_);
v___x_820_ = lean_nat_add(v_i_805_, v___x_815_);
lean_dec(v_i_805_);
lean_inc(v_v_810_);
lean_inc(v_k_809_);
v___x_821_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg(v_entries_806_, v_h_819_, v_depth_802_, v_k_809_, v_v_810_);
v_i_805_ = v___x_820_;
v_entries_806_ = v___x_821_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_depth_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_i_828_, lean_object* v_entries_829_){
_start:
{
size_t v_depth_boxed_830_; lean_object* v_res_831_; 
v_depth_boxed_830_ = lean_unbox_usize(v_depth_825_);
lean_dec(v_depth_825_);
v_res_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_depth_boxed_830_, v_keys_826_, v_vals_827_, v_i_828_, v_entries_829_);
lean_dec_ref(v_vals_827_);
lean_dec_ref(v_keys_826_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg___boxed(lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
size_t v_x_2630__boxed_837_; size_t v_x_2631__boxed_838_; lean_object* v_res_839_; 
v_x_2630__boxed_837_ = lean_unbox_usize(v_x_833_);
lean_dec(v_x_833_);
v_x_2631__boxed_838_ = lean_unbox_usize(v_x_834_);
lean_dec(v_x_834_);
v_res_839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_832_, v_x_2630__boxed_837_, v_x_2631__boxed_838_, v_x_835_, v_x_836_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4___redArg(lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
uint64_t v___y_844_; 
if (lean_obj_tag(v_x_841_) == 0)
{
uint64_t v___x_848_; 
v___x_848_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_844_ = v___x_848_;
goto v___jp_843_;
}
else
{
uint64_t v_hash_849_; 
v_hash_849_ = lean_ctor_get_uint64(v_x_841_, sizeof(void*)*2);
v___y_844_ = v_hash_849_;
goto v___jp_843_;
}
v___jp_843_:
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_uint64_to_usize(v___y_844_);
v___x_846_ = ((size_t)1ULL);
v___x_847_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_840_, v___x_845_, v___x_846_, v_x_841_, v_x_842_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn___lam__4_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(lean_object* v_s_850_, lean_object* v_d_851_){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = l_Lean_IR_Decl_name(v_d_851_);
v___x_853_ = l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4___redArg(v_s_850_, v___x_852_, v_d_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_));
v___x_882_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2____boxed(lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_();
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2(lean_object* v_n_885_, lean_object* v_as_886_, lean_object* v_lo_887_, lean_object* v_hi_888_, lean_object* v_w_889_, lean_object* v_hlo_890_, lean_object* v_hhi_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg(v_as_886_, v_lo_887_, v_hi_888_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_893_, lean_object* v_as_894_, lean_object* v_lo_895_, lean_object* v_hi_896_, lean_object* v_w_897_, lean_object* v_hlo_898_, lean_object* v_hhi_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2(v_n_893_, v_as_894_, v_lo_895_, v_hi_896_, v_w_897_, v_hlo_898_, v_hhi_899_);
lean_dec(v_hi_896_);
lean_dec(v_n_893_);
return v_res_900_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg(v_x_902_, v_x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___boxed(lean_object* v_00_u03b2_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3(v_00_u03b2_905_, v_x_906_, v_x_907_);
lean_dec(v_x_907_);
lean_dec_ref(v_x_906_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b2_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4___redArg(v_x_911_, v_x_912_, v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_00_u03b2_915_, lean_object* v_x_916_, size_t v_x_917_, lean_object* v_x_918_){
_start:
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_916_, v_x_917_, v_x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_00_u03b2_920_, lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
size_t v_x_2917__boxed_924_; uint8_t v_res_925_; lean_object* v_r_926_; 
v_x_2917__boxed_924_ = lean_unbox_usize(v_x_922_);
lean_dec(v_x_922_);
v_res_925_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b2_920_, v_x_921_, v_x_2917__boxed_924_, v_x_923_);
lean_dec(v_x_923_);
lean_dec_ref(v_x_921_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6(lean_object* v_00_u03b2_927_, lean_object* v_x_928_, size_t v_x_929_, size_t v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___redArg(v_x_928_, v_x_929_, v_x_930_, v_x_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6___boxed(lean_object* v_00_u03b2_934_, lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
size_t v_x_2928__boxed_940_; size_t v_x_2929__boxed_941_; lean_object* v_res_942_; 
v_x_2928__boxed_940_ = lean_unbox_usize(v_x_936_);
lean_dec(v_x_936_);
v_x_2929__boxed_941_ = lean_unbox_usize(v_x_937_);
lean_dec(v_x_937_);
v_res_942_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6(v_00_u03b2_934_, v_x_935_, v_x_2928__boxed_940_, v_x_2929__boxed_941_, v_x_938_, v_x_939_);
return v_res_942_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5(lean_object* v_00_u03b2_943_, lean_object* v_keys_944_, lean_object* v_vals_945_, lean_object* v_heq_946_, lean_object* v_i_947_, lean_object* v_k_948_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___redArg(v_keys_944_, v_i_947_, v_k_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_950_, lean_object* v_keys_951_, lean_object* v_vals_952_, lean_object* v_heq_953_, lean_object* v_i_954_, lean_object* v_k_955_){
_start:
{
uint8_t v_res_956_; lean_object* v_r_957_; 
v_res_956_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4_spec__5(v_00_u03b2_950_, v_keys_951_, v_vals_952_, v_heq_953_, v_i_954_, v_k_955_);
lean_dec(v_k_955_);
lean_dec_ref(v_vals_952_);
lean_dec_ref(v_keys_951_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8(lean_object* v_00_u03b2_958_, lean_object* v_n_959_, lean_object* v_k_960_, lean_object* v_v_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8___redArg(v_n_959_, v_k_960_, v_v_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9(lean_object* v_00_u03b2_963_, size_t v_depth_964_, lean_object* v_keys_965_, lean_object* v_vals_966_, lean_object* v_heq_967_, lean_object* v_i_968_, lean_object* v_entries_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___redArg(v_depth_964_, v_keys_965_, v_vals_966_, v_i_968_, v_entries_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9___boxed(lean_object* v_00_u03b2_971_, lean_object* v_depth_972_, lean_object* v_keys_973_, lean_object* v_vals_974_, lean_object* v_heq_975_, lean_object* v_i_976_, lean_object* v_entries_977_){
_start:
{
size_t v_depth_boxed_978_; lean_object* v_res_979_; 
v_depth_boxed_978_ = lean_unbox_usize(v_depth_972_);
lean_dec(v_depth_972_);
v_res_979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__9(v_00_u03b2_971_, v_depth_boxed_978_, v_keys_973_, v_vals_974_, v_heq_975_, v_i_976_, v_entries_977_);
lean_dec_ref(v_vals_974_);
lean_dec_ref(v_keys_973_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__4_spec__6_spec__8_spec__9___redArg(v_x_981_, v_x_982_, v_x_983_, v_x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(lean_object* v_irDecls_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_987_ = lean_array_get_size(v_irDecls_986_);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_nat_dec_eq(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___y_993_; uint8_t v___x_997_; 
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_sub(v___x_987_, v___x_990_);
v___x_997_ = lean_nat_dec_le(v___x_988_, v___x_991_);
if (v___x_997_ == 0)
{
lean_inc(v___x_991_);
v___y_993_ = v___x_991_;
goto v___jp_992_;
}
else
{
v___y_993_ = v___x_988_;
goto v___jp_992_;
}
v___jp_992_:
{
uint8_t v___x_994_; 
v___x_994_ = lean_nat_dec_le(v___y_993_, v___x_991_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; 
lean_dec(v___x_991_);
lean_inc(v___y_993_);
v___x_995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg(v_irDecls_986_, v___y_993_, v___y_993_);
lean_dec(v___y_993_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg(v_irDecls_986_, v___y_993_, v___x_991_);
lean_dec(v___x_991_);
return v___x_996_;
}
}
}
else
{
return v_irDecls_986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(lean_object* v_initDecls_998_){
_start:
{
lean_inc_ref(v_initDecls_998_);
return v_initDecls_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4___boxed(lean_object* v_initDecls_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__4(v_initDecls_999_);
lean_dec_ref(v_initDecls_999_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(lean_object* v_modPkg_1001_){
_start:
{
lean_inc_ref(v_modPkg_1001_);
return v_modPkg_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7___boxed(lean_object* v_modPkg_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__7(v_modPkg_1002_);
lean_dec_ref(v_modPkg_1002_);
return v_res_1003_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__1));
v___x_1007_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__0));
v___x_1008_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1007_, v___x_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* lean_ir_export_entries(lean_object* v_env_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v_toEnvExtension_1014_; lean_object* v_name_1015_; lean_object* v_asyncMode_1016_; lean_object* v___x_1017_; lean_object* v_ext_1018_; lean_object* v_toEnvExtension_1019_; lean_object* v_name_1020_; lean_object* v_exportEntriesFn_1021_; lean_object* v_asyncMode_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_toEnvExtension_1026_; lean_object* v_name_1027_; lean_object* v_exportEntriesFn_1028_; lean_object* v_asyncMode_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_irDecls_1035_; lean_object* v_irEntries_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v_initDecls_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_modPkg_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1013_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_toEnvExtension_1014_);
v_name_1015_ = lean_ctor_get(v___x_1013_, 1);
lean_inc(v_name_1015_);
v_asyncMode_1016_ = lean_ctor_get(v_toEnvExtension_1014_, 2);
lean_inc(v_asyncMode_1016_);
lean_dec_ref(v_toEnvExtension_1014_);
v___x_1017_ = l_Lean_regularInitAttr;
v_ext_1018_ = lean_ctor_get(v___x_1017_, 1);
lean_inc_ref(v_ext_1018_);
v_toEnvExtension_1019_ = lean_ctor_get(v_ext_1018_, 0);
v_name_1020_ = lean_ctor_get(v_ext_1018_, 1);
lean_inc(v_name_1020_);
v_exportEntriesFn_1021_ = lean_ctor_get(v_ext_1018_, 4);
lean_inc_ref(v_exportEntriesFn_1021_);
v_asyncMode_1022_ = lean_ctor_get(v_toEnvExtension_1019_, 2);
lean_inc(v_asyncMode_1022_);
v___x_1023_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc_ref(v_env_1012_);
v___x_1024_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1023_, v___x_1013_, v_env_1012_, v_asyncMode_1016_);
lean_dec(v_asyncMode_1016_);
v___x_1025_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
v_toEnvExtension_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc_ref(v_toEnvExtension_1026_);
v_name_1027_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_name_1027_);
v_exportEntriesFn_1028_ = lean_ctor_get(v___x_1025_, 4);
lean_inc_ref(v_exportEntriesFn_1028_);
v_asyncMode_1029_ = lean_ctor_get(v_toEnvExtension_1026_, 2);
lean_inc(v_asyncMode_1029_);
lean_dec_ref(v_toEnvExtension_1026_);
v___x_1030_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__3));
v___x_1031_ = lean_box(0);
lean_inc_ref(v_env_1012_);
v___x_1032_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1030_, v_ext_1018_, v_env_1012_, v_asyncMode_1022_, v___x_1031_);
lean_dec(v_asyncMode_1022_);
lean_dec_ref(v_ext_1018_);
v___x_1033_ = lean_box(0);
v___x_1034_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__0___closed__0));
v_irDecls_1035_ = l_List_foldl___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__1(v___x_1034_, v___x_1024_);
v_irEntries_1036_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries_unsafe__1(v_irDecls_1035_);
v___x_1037_ = 2;
v___x_1038_ = lean_box(v___x_1037_);
lean_inc_ref(v_env_1012_);
v_initDecls_1039_ = lean_apply_3(v_exportEntriesFn_1021_, v_env_1012_, v___x_1032_, v___x_1038_);
lean_inc_ref(v_env_1012_);
v___x_1040_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1033_, v___x_1025_, v_env_1012_, v_asyncMode_1029_, v___x_1031_);
lean_dec(v_asyncMode_1029_);
v___x_1041_ = lean_box(v___x_1037_);
v_modPkg_1042_ = lean_apply_3(v_exportEntriesFn_1028_, v_env_1012_, v___x_1040_, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_name_1015_);
lean_ctor_set(v___x_1043_, 1, v_irEntries_1036_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_name_1020_);
lean_ctor_set(v___x_1044_, 1, v_initDecls_1039_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_name_1027_);
lean_ctor_set(v___x_1045_, 1, v_modPkg_1042_);
v___x_1046_ = lean_unsigned_to_nat(3u);
v___x_1047_ = lean_mk_empty_array_with_capacity(v___x_1046_);
v___x_1048_ = lean_array_push(v___x_1047_, v___x_1043_);
v___x_1049_ = lean_array_push(v___x_1048_, v___x_1044_);
v___x_1050_ = lean_array_push(v___x_1049_, v___x_1045_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(lean_object* v_as_1051_, lean_object* v_k_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v_m_1057_; lean_object* v_a_1058_; uint8_t v___x_1059_; 
v___x_1055_ = lean_nat_add(v_x_1053_, v_x_1054_);
v___x_1056_ = lean_unsigned_to_nat(1u);
v_m_1057_ = lean_nat_shiftr(v___x_1055_, v___x_1056_);
lean_dec(v___x_1055_);
v_a_1058_ = lean_array_fget_borrowed(v_as_1051_, v_m_1057_);
v___x_1059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___lam__0(v_a_1058_, v_k_1052_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; 
lean_dec(v_x_1054_);
v___x_1060_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__2___redArg___lam__0(v_k_1052_, v_a_1058_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec(v_m_1057_);
lean_dec(v_x_1053_);
lean_inc(v_a_1058_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_a_1058_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_nat_dec_eq(v_m_1057_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_nat_sub(v_m_1057_, v___x_1056_);
lean_dec(v_m_1057_);
v___x_1065_ = lean_nat_dec_lt(v___x_1064_, v_x_1053_);
if (v___x_1065_ == 0)
{
v_x_1054_ = v___x_1064_;
goto _start;
}
else
{
lean_object* v___x_1067_; 
lean_dec(v___x_1064_);
lean_dec(v_x_1053_);
v___x_1067_ = lean_box(0);
return v___x_1067_;
}
}
else
{
lean_object* v___x_1068_; 
lean_dec(v_m_1057_);
lean_dec(v_x_1053_);
v___x_1068_ = lean_box(0);
return v___x_1068_;
}
}
}
else
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
lean_dec(v_x_1053_);
v___x_1069_ = lean_nat_add(v_m_1057_, v___x_1056_);
lean_dec(v_m_1057_);
v___x_1070_ = lean_nat_dec_le(v___x_1069_, v_x_1054_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec(v___x_1069_);
lean_dec(v_x_1054_);
v___x_1071_ = lean_box(0);
return v___x_1071_;
}
else
{
v_x_1053_ = v___x_1069_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg___boxed(lean_object* v_as_1073_, lean_object* v_k_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1073_, v_k_1074_, v_x_1075_, v_x_1076_);
lean_dec_ref(v_k_1074_);
lean_dec_ref(v_as_1073_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1078_, lean_object* v_vals_1079_, lean_object* v_i_1080_, lean_object* v_k_1081_){
_start:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_array_get_size(v_keys_1078_);
v___x_1083_ = lean_nat_dec_lt(v_i_1080_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec(v_i_1080_);
v___x_1084_ = lean_box(0);
return v___x_1084_;
}
else
{
lean_object* v_k_x27_1085_; uint8_t v___x_1086_; 
v_k_x27_1085_ = lean_array_fget_borrowed(v_keys_1078_, v_i_1080_);
v___x_1086_ = lean_name_eq(v_k_1081_, v_k_x27_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(1u);
v___x_1088_ = lean_nat_add(v_i_1080_, v___x_1087_);
lean_dec(v_i_1080_);
v_i_1080_ = v___x_1088_;
goto _start;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_array_fget_borrowed(v_vals_1079_, v_i_1080_);
lean_dec(v_i_1080_);
lean_inc(v___x_1090_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1092_, lean_object* v_vals_1093_, lean_object* v_i_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1092_, v_vals_1093_, v_i_1094_, v_k_1095_);
lean_dec(v_k_1095_);
lean_dec_ref(v_vals_1093_);
lean_dec_ref(v_keys_1092_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(lean_object* v_x_1097_, size_t v_x_1098_, lean_object* v_x_1099_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v_es_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1121_; 
v_es_1100_ = lean_ctor_get(v_x_1097_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1102_ = v_x_1097_;
v_isShared_1103_ = v_isSharedCheck_1121_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_es_1100_);
lean_dec(v_x_1097_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1121_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; lean_object* v_j_1108_; lean_object* v___x_1109_; 
v___x_1104_ = lean_box(2);
v___x_1105_ = ((size_t)5ULL);
v___x_1106_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_1107_ = lean_usize_land(v_x_1098_, v___x_1106_);
v_j_1108_ = lean_usize_to_nat(v___x_1107_);
v___x_1109_ = lean_array_get(v___x_1104_, v_es_1100_, v_j_1108_);
lean_dec(v_j_1108_);
lean_dec_ref(v_es_1100_);
switch(lean_obj_tag(v___x_1109_))
{
case 0:
{
lean_object* v_key_1110_; lean_object* v_val_1111_; uint8_t v___x_1112_; 
v_key_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_key_1110_);
v_val_1111_ = lean_ctor_get(v___x_1109_, 1);
lean_inc(v_val_1111_);
lean_dec_ref(v___x_1109_);
v___x_1112_ = lean_name_eq(v_x_1099_, v_key_1110_);
lean_dec(v_key_1110_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec(v_val_1111_);
lean_del_object(v___x_1102_);
v___x_1113_ = lean_box(0);
return v___x_1113_;
}
else
{
lean_object* v___x_1115_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 1);
lean_ctor_set(v___x_1102_, 0, v_val_1111_);
v___x_1115_ = v___x_1102_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_val_1111_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
case 1:
{
lean_object* v_node_1117_; size_t v___x_1118_; 
lean_del_object(v___x_1102_);
v_node_1117_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_node_1117_);
lean_dec_ref(v___x_1109_);
v___x_1118_ = lean_usize_shift_right(v_x_1098_, v___x_1105_);
v_x_1097_ = v_node_1117_;
v_x_1098_ = v___x_1118_;
goto _start;
}
default: 
{
lean_object* v___x_1120_; 
lean_del_object(v___x_1102_);
v___x_1120_ = lean_box(0);
return v___x_1120_;
}
}
}
}
else
{
lean_object* v_ks_1122_; lean_object* v_vs_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_ks_1122_ = lean_ctor_get(v_x_1097_, 0);
lean_inc_ref(v_ks_1122_);
v_vs_1123_ = lean_ctor_get(v_x_1097_, 1);
lean_inc_ref(v_vs_1123_);
lean_dec_ref(v_x_1097_);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_ks_1122_, v_vs_1123_, v___x_1124_, v_x_1099_);
lean_dec_ref(v_vs_1123_);
lean_dec_ref(v_ks_1122_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
size_t v_x_414__boxed_1129_; lean_object* v_res_1130_; 
v_x_414__boxed_1129_ = lean_unbox_usize(v_x_1127_);
lean_dec(v_x_1127_);
v_res_1130_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1126_, v_x_414__boxed_1129_, v_x_1128_);
lean_dec(v_x_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
uint64_t v___y_1134_; 
if (lean_obj_tag(v_x_1132_) == 0)
{
uint64_t v___x_1137_; 
v___x_1137_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg___closed__0);
v___y_1134_ = v___x_1137_;
goto v___jp_1133_;
}
else
{
uint64_t v_hash_1138_; 
v_hash_1138_ = lean_ctor_get_uint64(v_x_1132_, sizeof(void*)*2);
v___y_1134_ = v_hash_1138_;
goto v___jp_1133_;
}
v___jp_1133_:
{
size_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = lean_uint64_to_usize(v___y_1134_);
v___x_1136_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1131_, v___x_1135_, v_x_1132_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg___boxed(lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1139_, v_x_1140_);
lean_dec(v_x_1140_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_IR_findEnvDecl___closed__0(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v___x_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl(lean_object* v_env_1145_, lean_object* v_declName_1146_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1156_; 
v___x_1147_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1148_ = l_Lean_IR_declMapExt;
v___x_1156_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1145_, v_declName_1146_);
if (lean_obj_tag(v___x_1156_) == 0)
{
goto v___jp_1149_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_val_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_val_1157_);
lean_dec_ref(v___x_1156_);
v___x_1172_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1147_, v___x_1148_, v_env_1145_, v_val_1157_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_array_get_size(v___x_1172_);
v___x_1175_ = lean_nat_dec_lt(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_dec_ref(v___x_1172_);
goto v___jp_1158_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = lean_unsigned_to_nat(1u);
v___x_1177_ = lean_nat_sub(v___x_1174_, v___x_1176_);
v___x_1178_ = lean_nat_dec_le(v___x_1173_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v___x_1177_);
lean_dec_ref(v___x_1172_);
goto v___jp_1158_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_tmpDecl_1182_; lean_object* v___x_1183_; 
v___x_1179_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1180_ = lean_box(0);
v___x_1181_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_declName_1146_);
v_tmpDecl_1182_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1182_, 0, v_declName_1146_);
lean_ctor_set(v_tmpDecl_1182_, 1, v___x_1179_);
lean_ctor_set(v_tmpDecl_1182_, 2, v___x_1180_);
lean_ctor_set(v_tmpDecl_1182_, 3, v___x_1181_);
v___x_1183_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1172_, v_tmpDecl_1182_, v___x_1173_, v___x_1177_);
lean_dec_ref(v_tmpDecl_1182_);
lean_dec_ref(v___x_1172_);
if (lean_obj_tag(v___x_1183_) == 0)
{
goto v___jp_1158_;
}
else
{
lean_dec(v_val_1157_);
lean_dec(v_declName_1146_);
lean_dec_ref(v_env_1145_);
return v___x_1183_;
}
}
}
v___jp_1158_:
{
uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1159_ = 0;
v___x_1160_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1147_, v___x_1148_, v_env_1145_, v_val_1157_, v___x_1159_);
lean_dec(v_val_1157_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_array_get_size(v___x_1160_);
v___x_1163_ = lean_nat_dec_lt(v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_dec_ref(v___x_1160_);
goto v___jp_1149_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_sub(v___x_1162_, v___x_1164_);
v___x_1166_ = lean_nat_dec_le(v___x_1161_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_dec(v___x_1165_);
lean_dec_ref(v___x_1160_);
goto v___jp_1149_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_tmpDecl_1170_; lean_object* v___x_1171_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1168_ = lean_box(0);
v___x_1169_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_declName_1146_);
v_tmpDecl_1170_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1170_, 0, v_declName_1146_);
lean_ctor_set(v_tmpDecl_1170_, 1, v___x_1167_);
lean_ctor_set(v_tmpDecl_1170_, 2, v___x_1168_);
lean_ctor_set(v_tmpDecl_1170_, 3, v___x_1169_);
v___x_1171_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1160_, v_tmpDecl_1170_, v___x_1161_, v___x_1165_);
lean_dec_ref(v_tmpDecl_1170_);
lean_dec_ref(v___x_1160_);
if (lean_obj_tag(v___x_1171_) == 0)
{
goto v___jp_1149_;
}
else
{
lean_dec(v_declName_1146_);
lean_dec_ref(v_env_1145_);
return v___x_1171_;
}
}
}
}
}
v___jp_1149_:
{
lean_object* v_toEnvExtension_1150_; lean_object* v_asyncMode_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_snd_1154_; lean_object* v___x_1155_; 
v_toEnvExtension_1150_ = lean_ctor_get(v___x_1148_, 0);
lean_inc_ref(v_toEnvExtension_1150_);
v_asyncMode_1151_ = lean_ctor_get(v_toEnvExtension_1150_, 2);
lean_inc(v_asyncMode_1151_);
lean_dec_ref(v_toEnvExtension_1150_);
v___x_1152_ = lean_box(0);
v___x_1153_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1147_, v___x_1148_, v_env_1145_, v_asyncMode_1151_, v___x_1152_);
lean_dec(v_asyncMode_1151_);
v_snd_1154_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_snd_1154_);
lean_dec(v___x_1153_);
v___x_1155_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_snd_1154_, v_declName_1146_);
lean_dec(v_declName_1146_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(lean_object* v_00_u03b2_1184_, lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v_x_1185_, v_x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___boxed(lean_object* v_00_u03b2_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0(v_00_u03b2_1188_, v_x_1189_, v_x_1190_);
lean_dec(v_x_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(lean_object* v_as_1192_, lean_object* v_k_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v_as_1192_, v_k_1193_, v_x_1194_, v_x_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___boxed(lean_object* v_as_1198_, lean_object* v_k_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1(v_as_1198_, v_k_1199_, v_x_1200_, v_x_1201_, v_x_1202_);
lean_dec_ref(v_k_1199_);
lean_dec_ref(v_as_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(lean_object* v_00_u03b2_1204_, lean_object* v_x_1205_, size_t v_x_1206_, lean_object* v_x_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___redArg(v_x_1205_, v_x_1206_, v_x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_){
_start:
{
size_t v_x_597__boxed_1213_; lean_object* v_res_1214_; 
v_x_597__boxed_1213_ = lean_unbox_usize(v_x_1211_);
lean_dec(v_x_1211_);
v_res_1214_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0(v_00_u03b2_1209_, v_x_1210_, v_x_597__boxed_1213_, v_x_1212_);
lean_dec(v_x_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1215_, lean_object* v_keys_1216_, lean_object* v_vals_1217_, lean_object* v_heq_1218_, lean_object* v_i_1219_, lean_object* v_k_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___redArg(v_keys_1216_, v_vals_1217_, v_i_1219_, v_k_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1222_, lean_object* v_keys_1223_, lean_object* v_vals_1224_, lean_object* v_heq_1225_, lean_object* v_i_1226_, lean_object* v_k_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0_spec__0_spec__1(v_00_u03b2_1222_, v_keys_1223_, v_vals_1224_, v_heq_1225_, v_i_1226_, v_k_1227_);
lean_dec(v_k_1227_);
lean_dec_ref(v_vals_1224_);
lean_dec_ref(v_keys_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl(lean_object* v_env_1229_, lean_object* v_declName_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1232_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1229_, v_declName_1230_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; lean_object* v_toEnvExtension_1234_; lean_object* v_asyncMode_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1233_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc_ref(v_toEnvExtension_1234_);
v_asyncMode_1235_ = lean_ctor_get(v_toEnvExtension_1234_, 2);
lean_inc(v_asyncMode_1235_);
lean_dec_ref(v_toEnvExtension_1234_);
v___x_1236_ = lean_box(0);
v___x_1237_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1231_, v___x_1233_, v_env_1229_, v_asyncMode_1235_, v___x_1236_);
lean_dec(v_asyncMode_1235_);
v___x_1238_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1237_, v_declName_1230_);
lean_dec(v_declName_1230_);
return v___x_1238_;
}
else
{
lean_object* v_val_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___y_1243_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_val_1239_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_val_1239_);
lean_dec_ref(v___x_1232_);
v___x_1240_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1241_ = l_Lean_IR_declMapExt;
v___x_1257_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1240_, v___x_1241_, v_env_1229_, v_val_1239_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_array_get_size(v___x_1257_);
v___x_1260_ = lean_nat_dec_lt(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref(v___x_1257_);
v___x_1261_ = lean_box(0);
v___y_1243_ = v___x_1261_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_sub(v___x_1259_, v___x_1262_);
v___x_1264_ = lean_nat_dec_le(v___x_1258_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec(v___x_1263_);
lean_dec_ref(v___x_1257_);
v___x_1265_ = lean_box(0);
v___y_1243_ = v___x_1265_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_tmpDecl_1269_; lean_object* v___x_1270_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1267_ = lean_box(0);
v___x_1268_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_declName_1230_);
v_tmpDecl_1269_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1269_, 0, v_declName_1230_);
lean_ctor_set(v_tmpDecl_1269_, 1, v___x_1266_);
lean_ctor_set(v_tmpDecl_1269_, 2, v___x_1267_);
lean_ctor_set(v_tmpDecl_1269_, 3, v___x_1268_);
v___x_1270_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1257_, v_tmpDecl_1269_, v___x_1258_, v___x_1263_);
lean_dec_ref(v_tmpDecl_1269_);
lean_dec_ref(v___x_1257_);
if (lean_obj_tag(v___x_1270_) == 0)
{
v___y_1243_ = v___x_1270_;
goto v___jp_1242_;
}
else
{
lean_dec(v_val_1239_);
lean_dec(v_declName_1230_);
lean_dec_ref(v_env_1229_);
return v___x_1270_;
}
}
}
v___jp_1242_:
{
uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1244_ = 0;
v___x_1245_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1240_, v___x_1241_, v_env_1229_, v_val_1239_, v___x_1244_);
lean_dec(v_val_1239_);
lean_dec_ref(v_env_1229_);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_array_get_size(v___x_1245_);
v___x_1248_ = lean_nat_dec_lt(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec_ref(v___x_1245_);
lean_dec(v_declName_1230_);
return v___y_1243_;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_nat_sub(v___x_1247_, v___x_1249_);
v___x_1251_ = lean_nat_dec_le(v___x_1246_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v___x_1250_);
lean_dec_ref(v___x_1245_);
lean_dec(v_declName_1230_);
return v___y_1243_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_tmpDecl_1255_; lean_object* v___x_1256_; 
lean_dec(v___y_1243_);
v___x_1252_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Lean_instInhabitedExternAttrData_default;
v_tmpDecl_1255_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1255_, 0, v_declName_1230_);
lean_ctor_set(v_tmpDecl_1255_, 1, v___x_1252_);
lean_ctor_set(v_tmpDecl_1255_, 2, v___x_1253_);
lean_ctor_set(v_tmpDecl_1255_, 3, v___x_1254_);
v___x_1256_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1245_, v_tmpDecl_1255_, v___x_1246_, v___x_1250_);
lean_dec_ref(v_tmpDecl_1255_);
lean_dec_ref(v___x_1245_);
return v___x_1256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_find_env_decl_boxed(lean_object* v_env_1271_, lean_object* v_declName_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v_boxed_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc(v_declName_1272_);
v_boxed_1274_ = l_Lean_Compiler_LCNF_mkBoxedName(v_declName_1272_);
v___x_1275_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1271_, v_declName_1272_);
lean_dec(v_declName_1272_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; lean_object* v_toEnvExtension_1277_; lean_object* v_asyncMode_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1276_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc_ref(v_toEnvExtension_1277_);
v_asyncMode_1278_ = lean_ctor_get(v_toEnvExtension_1277_, 2);
lean_inc(v_asyncMode_1278_);
lean_dec_ref(v_toEnvExtension_1277_);
v___x_1279_ = lean_box(0);
v___x_1280_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1273_, v___x_1276_, v_env_1271_, v_asyncMode_1278_, v___x_1279_);
lean_dec(v_asyncMode_1278_);
v___x_1281_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1280_, v_boxed_1274_);
lean_dec(v_boxed_1274_);
return v___x_1281_;
}
else
{
lean_object* v_val_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___y_1286_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_val_1282_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_val_1282_);
lean_dec_ref(v___x_1275_);
v___x_1283_ = lean_obj_once(&l_Lean_IR_findEnvDecl___closed__0, &l_Lean_IR_findEnvDecl___closed__0_once, _init_l_Lean_IR_findEnvDecl___closed__0);
v___x_1284_ = l_Lean_IR_declMapExt;
v___x_1300_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1283_, v___x_1284_, v_env_1271_, v_val_1282_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_array_get_size(v___x_1300_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; 
lean_dec_ref(v___x_1300_);
v___x_1304_ = lean_box(0);
v___y_1286_ = v___x_1304_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = lean_nat_sub(v___x_1302_, v___x_1305_);
v___x_1307_ = lean_nat_dec_le(v___x_1301_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_dec(v___x_1306_);
lean_dec_ref(v___x_1300_);
v___x_1308_ = lean_box(0);
v___y_1286_ = v___x_1308_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_tmpDecl_1312_; lean_object* v___x_1313_; 
v___x_1309_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1310_ = lean_box(0);
v___x_1311_ = l_Lean_instInhabitedExternAttrData_default;
lean_inc(v_boxed_1274_);
v_tmpDecl_1312_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1312_, 0, v_boxed_1274_);
lean_ctor_set(v_tmpDecl_1312_, 1, v___x_1309_);
lean_ctor_set(v_tmpDecl_1312_, 2, v___x_1310_);
lean_ctor_set(v_tmpDecl_1312_, 3, v___x_1311_);
v___x_1313_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1300_, v_tmpDecl_1312_, v___x_1301_, v___x_1306_);
lean_dec_ref(v_tmpDecl_1312_);
lean_dec_ref(v___x_1300_);
if (lean_obj_tag(v___x_1313_) == 0)
{
v___y_1286_ = v___x_1313_;
goto v___jp_1285_;
}
else
{
lean_dec(v_val_1282_);
lean_dec(v_boxed_1274_);
lean_dec_ref(v_env_1271_);
return v___x_1313_;
}
}
}
v___jp_1285_:
{
uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1287_ = 0;
v___x_1288_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1283_, v___x_1284_, v_env_1271_, v_val_1282_, v___x_1287_);
lean_dec(v_val_1282_);
lean_dec_ref(v_env_1271_);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_array_get_size(v___x_1288_);
v___x_1291_ = lean_nat_dec_lt(v___x_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v___x_1288_);
lean_dec(v_boxed_1274_);
return v___y_1286_;
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_nat_sub(v___x_1290_, v___x_1292_);
v___x_1294_ = lean_nat_dec_le(v___x_1289_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_dec(v___x_1293_);
lean_dec_ref(v___x_1288_);
lean_dec(v_boxed_1274_);
return v___y_1286_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_tmpDecl_1298_; lean_object* v___x_1299_; 
lean_dec(v___y_1286_);
v___x_1295_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_findAtSorted_x3f___closed__0));
v___x_1296_ = lean_box(0);
v___x_1297_ = l_Lean_instInhabitedExternAttrData_default;
v_tmpDecl_1298_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_tmpDecl_1298_, 0, v_boxed_1274_);
lean_ctor_set(v_tmpDecl_1298_, 1, v___x_1295_);
lean_ctor_set(v_tmpDecl_1298_, 2, v___x_1296_);
lean_ctor_set(v_tmpDecl_1298_, 3, v___x_1297_);
v___x_1299_ = l_Array_binSearchAux___at___00Lean_IR_findEnvDecl_spec__1___redArg(v___x_1288_, v_tmpDecl_1298_, v___x_1289_, v___x_1293_);
lean_dec_ref(v_tmpDecl_1298_);
lean_dec_ref(v___x_1288_);
return v___x_1299_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t lean_has_compile_error(lean_object* v_env_1314_, lean_object* v_constName_1315_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1314_, v_constName_1315_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1317_; lean_object* v_toEnvExtension_1318_; lean_object* v_asyncMode_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1317_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref(v_toEnvExtension_1318_);
v_asyncMode_1319_ = lean_ctor_get(v_toEnvExtension_1318_, 2);
lean_inc(v_asyncMode_1319_);
lean_dec_ref(v_toEnvExtension_1318_);
v___x_1320_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1321_ = lean_box(0);
v___x_1322_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1320_, v___x_1317_, v_env_1314_, v_asyncMode_1319_, v___x_1321_);
lean_dec(v_asyncMode_1319_);
v___x_1323_ = l_Lean_PersistentHashMap_contains___at___00Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2__spec__3___redArg(v___x_1322_, v_constName_1315_);
lean_dec(v_constName_1315_);
lean_dec(v___x_1322_);
if (v___x_1323_ == 0)
{
uint8_t v___x_1324_; 
v___x_1324_ = 1;
return v___x_1324_;
}
else
{
uint8_t v___x_1325_; 
v___x_1325_ = 0;
return v___x_1325_;
}
}
else
{
uint8_t v___x_1326_; 
lean_dec_ref(v___x_1316_);
lean_dec(v_constName_1315_);
lean_dec_ref(v_env_1314_);
v___x_1326_ = 0;
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_hasCompileError___boxed(lean_object* v_env_1327_, lean_object* v_constName_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = lean_has_compile_error(v_env_1327_, v_constName_1328_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg(lean_object* v_n_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v___x_1334_; lean_object* v_env_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1334_ = lean_st_ref_get(v_a_1332_);
v_env_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc_ref(v_env_1335_);
lean_dec(v___x_1334_);
v___x_1336_ = l_Lean_IR_findEnvDecl(v_env_1335_, v_n_1331_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___redArg___boxed(lean_object* v_n_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_IR_findDecl___redArg(v_n_1338_, v_a_1339_);
lean_dec(v_a_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl(lean_object* v_n_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_IR_findDecl___redArg(v_n_1342_, v_a_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl___boxed(lean_object* v_n_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_IR_findDecl(v_n_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg(lean_object* v_n_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1355_; lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1370_; 
v___x_1355_ = l_Lean_IR_findDecl___redArg(v_n_1352_, v_a_1353_);
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1370_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1370_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
if (lean_obj_tag(v_a_1356_) == 0)
{
uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1360_ = 0;
v___x_1361_ = lean_box(v___x_1360_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1361_);
v___x_1363_ = v___x_1358_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
else
{
uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec_ref(v_a_1356_);
v___x_1365_ = 1;
v___x_1366_ = lean_box(v___x_1365_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1366_);
v___x_1368_ = v___x_1358_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___redArg___boxed(lean_object* v_n_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_IR_containsDecl___redArg(v_n_1371_, v_a_1372_);
lean_dec(v_a_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl(lean_object* v_n_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_IR_containsDecl___redArg(v_n_1375_, v_a_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl___boxed(lean_object* v_n_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_IR_containsDecl(v_n_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(lean_object* v_msg_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_ref_1389_; lean_object* v___x_1390_; lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1399_; 
v_ref_1389_ = lean_ctor_get(v___y_1386_, 5);
v___x_1390_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_IR_log_spec__0_spec__0(v_msg_1385_, v___y_1386_, v___y_1387_);
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
lean_inc(v_ref_1389_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_ref_1389_);
lean_ctor_set(v___x_1395_, 1, v_a_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 1);
lean_ctor_set(v___x_1393_, 0, v___x_1395_);
v___x_1397_ = v___x_1393_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg___boxed(lean_object* v_msg_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl(lean_object* v_n_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1429_; 
lean_inc(v_n_1407_);
v___x_1411_ = l_Lean_IR_findDecl___redArg(v_n_1407_, v_a_1409_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1429_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1429_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
if (lean_obj_tag(v_a_1412_) == 1)
{
lean_object* v_val_1416_; lean_object* v___x_1418_; 
lean_dec(v_n_1407_);
v_val_1416_ = lean_ctor_get(v_a_1412_, 0);
lean_inc(v_val_1416_);
lean_dec_ref(v_a_1412_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v_val_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_val_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
else
{
lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_del_object(v___x_1414_);
lean_dec(v_a_1412_);
v___x_1420_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1421_ = 1;
v___x_1422_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1407_, v___x_1421_);
v___x_1423_ = lean_string_append(v___x_1420_, v___x_1422_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1425_ = lean_string_append(v___x_1423_, v___x_1424_);
v___x_1426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
v___x_1427_ = l_Lean_MessageData_ofFormat(v___x_1426_);
v___x_1428_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1427_, v_a_1408_, v_a_1409_);
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl___boxed(lean_object* v_n_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_IR_getDecl(v_n_1430_, v_a_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(lean_object* v_00_u03b1_1435_, lean_object* v_msg_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v_msg_1436_, v___y_1437_, v___y_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___boxed(lean_object* v_00_u03b1_1441_, lean_object* v_msg_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0(v_00_u03b1_1441_, v_msg_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object* v_n_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___x_1450_; lean_object* v_env_1451_; lean_object* v___x_1452_; lean_object* v_toEnvExtension_1453_; lean_object* v_asyncMode_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1450_ = lean_st_ref_get(v_a_1448_);
v_env_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_env_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_toEnvExtension_1453_);
v_asyncMode_1454_ = lean_ctor_get(v_toEnvExtension_1453_, 2);
lean_inc(v_asyncMode_1454_);
lean_dec_ref(v_toEnvExtension_1453_);
v___x_1455_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1455_, v___x_1452_, v_env_1451_, v_asyncMode_1454_, v___x_1456_);
lean_dec(v_asyncMode_1454_);
v___x_1458_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_IR_findEnvDecl_spec__0___redArg(v___x_1457_, v_n_1447_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___redArg___boxed(lean_object* v_n_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_IR_findLocalDecl___redArg(v_n_1460_, v_a_1461_);
lean_dec(v_a_1461_);
lean_dec(v_n_1460_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl(lean_object* v_n_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_IR_findLocalDecl___redArg(v_n_1464_, v_a_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findLocalDecl___boxed(lean_object* v_n_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_IR_findLocalDecl(v_n_1469_, v_a_1470_, v_a_1471_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_n_1469_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecls(lean_object* v_env_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v_toEnvExtension_1476_; lean_object* v_asyncMode_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1475_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc_ref(v_toEnvExtension_1476_);
v_asyncMode_1477_ = lean_ctor_get(v_toEnvExtension_1476_, 2);
lean_inc(v_asyncMode_1477_);
lean_dec_ref(v_toEnvExtension_1476_);
v___x_1478_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
v___x_1479_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1478_, v___x_1475_, v_env_1474_, v_asyncMode_1477_);
lean_dec(v_asyncMode_1477_);
return v___x_1479_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__0(void){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__1(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__0, &l_Lean_IR_addDecl___redArg___closed__0_once, _init_l_Lean_IR_addDecl___redArg___closed__0);
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_IR_addDecl___redArg___closed__2(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__1, &l_Lean_IR_addDecl___redArg___closed__1_once, _init_l_Lean_IR_addDecl___redArg___closed__1);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg(lean_object* v_decl_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v___x_1488_; lean_object* v_env_1489_; lean_object* v_nextMacroScope_1490_; lean_object* v_ngen_1491_; lean_object* v_auxDeclNGen_1492_; lean_object* v_traceState_1493_; lean_object* v_messages_1494_; lean_object* v_infoState_1495_; lean_object* v_snapshotTasks_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1512_; 
v___x_1488_ = lean_st_ref_take(v_a_1486_);
v_env_1489_ = lean_ctor_get(v___x_1488_, 0);
v_nextMacroScope_1490_ = lean_ctor_get(v___x_1488_, 1);
v_ngen_1491_ = lean_ctor_get(v___x_1488_, 2);
v_auxDeclNGen_1492_ = lean_ctor_get(v___x_1488_, 3);
v_traceState_1493_ = lean_ctor_get(v___x_1488_, 4);
v_messages_1494_ = lean_ctor_get(v___x_1488_, 6);
v_infoState_1495_ = lean_ctor_get(v___x_1488_, 7);
v_snapshotTasks_1496_ = lean_ctor_get(v___x_1488_, 8);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v___x_1488_, 5);
lean_dec(v_unused_1513_);
v___x_1498_ = v___x_1488_;
v_isShared_1499_ = v_isSharedCheck_1512_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snapshotTasks_1496_);
lean_inc(v_infoState_1495_);
lean_inc(v_messages_1494_);
lean_inc(v_traceState_1493_);
lean_inc(v_auxDeclNGen_1492_);
lean_inc(v_ngen_1491_);
lean_inc(v_nextMacroScope_1490_);
lean_inc(v_env_1489_);
lean_dec(v___x_1488_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1512_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v_toEnvExtension_1501_; lean_object* v_asyncMode_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1500_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_ref(v_toEnvExtension_1501_);
v_asyncMode_1502_ = lean_ctor_get(v_toEnvExtension_1501_, 2);
lean_inc(v_asyncMode_1502_);
lean_dec_ref(v_toEnvExtension_1501_);
v___x_1503_ = lean_box(0);
v___x_1504_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1500_, v_env_1489_, v_decl_1485_, v_asyncMode_1502_, v___x_1503_);
lean_dec(v_asyncMode_1502_);
v___x_1505_ = lean_obj_once(&l_Lean_IR_addDecl___redArg___closed__2, &l_Lean_IR_addDecl___redArg___closed__2_once, _init_l_Lean_IR_addDecl___redArg___closed__2);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 5, v___x_1505_);
lean_ctor_set(v___x_1498_, 0, v___x_1504_);
v___x_1507_ = v___x_1498_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_nextMacroScope_1490_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_ngen_1491_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_auxDeclNGen_1492_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_traceState_1493_);
lean_ctor_set(v_reuseFailAlloc_1511_, 5, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1511_, 6, v_messages_1494_);
lean_ctor_set(v_reuseFailAlloc_1511_, 7, v_infoState_1495_);
lean_ctor_set(v_reuseFailAlloc_1511_, 8, v_snapshotTasks_1496_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_st_ref_set(v_a_1486_, v___x_1507_);
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___redArg___boxed(lean_object* v_decl_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_IR_addDecl___redArg(v_decl_1514_, v_a_1515_);
lean_dec(v_a_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl(lean_object* v_decl_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_IR_addDecl___redArg(v_decl_1518_, v_a_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecl___boxed(lean_object* v_decl_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_IR_addDecl(v_decl_1523_, v_a_1524_, v_a_1525_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(lean_object* v_as_1528_, size_t v_i_1529_, size_t v_stop_1530_, lean_object* v_b_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_usize_dec_eq(v_i_1529_, v_stop_1530_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_array_uget_borrowed(v_as_1528_, v_i_1529_);
lean_inc(v___x_1535_);
v___x_1536_ = l_Lean_IR_addDecl___redArg(v___x_1535_, v___y_1532_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; size_t v___x_1538_; size_t v___x_1539_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1536_);
v___x_1538_ = ((size_t)1ULL);
v___x_1539_ = lean_usize_add(v_i_1529_, v___x_1538_);
v_i_1529_ = v___x_1539_;
v_b_1531_ = v_a_1537_;
goto _start;
}
else
{
return v___x_1536_;
}
}
else
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_b_1531_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg___boxed(lean_object* v_as_1542_, lean_object* v_i_1543_, lean_object* v_stop_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
size_t v_i_boxed_1548_; size_t v_stop_boxed_1549_; lean_object* v_res_1550_; 
v_i_boxed_1548_ = lean_unbox_usize(v_i_1543_);
lean_dec(v_i_1543_);
v_stop_boxed_1549_ = lean_unbox_usize(v_stop_1544_);
lean_dec(v_stop_1544_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1542_, v_i_boxed_1548_, v_stop_boxed_1549_, v_b_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v_as_1542_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls(lean_object* v_decls_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_array_get_size(v_decls_1551_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_nat_dec_lt(v___x_1555_, v___x_1556_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
return v___x_1559_;
}
else
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_nat_dec_le(v___x_1556_, v___x_1556_);
if (v___x_1560_ == 0)
{
if (v___x_1558_ == 0)
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1557_);
return v___x_1561_;
}
else
{
size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = lean_usize_of_nat(v___x_1556_);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1551_, v___x_1562_, v___x_1563_, v___x_1557_, v_a_1553_);
return v___x_1564_;
}
}
else
{
size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = ((size_t)0ULL);
v___x_1566_ = lean_usize_of_nat(v___x_1556_);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_decls_1551_, v___x_1565_, v___x_1566_, v___x_1557_, v_a_1553_);
return v___x_1567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addDecls___boxed(lean_object* v_decls_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_IR_addDecls(v_decls_1568_, v_a_1569_, v_a_1570_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec_ref(v_decls_1568_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(lean_object* v_as_1573_, size_t v_i_1574_, size_t v_stop_1575_, lean_object* v_b_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___redArg(v_as_1573_, v_i_1574_, v_stop_1575_, v_b_1576_, v___y_1578_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0___boxed(lean_object* v_as_1581_, lean_object* v_i_1582_, lean_object* v_stop_1583_, lean_object* v_b_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
size_t v_i_boxed_1588_; size_t v_stop_boxed_1589_; lean_object* v_res_1590_; 
v_i_boxed_1588_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_stop_boxed_1589_ = lean_unbox_usize(v_stop_1583_);
lean_dec(v_stop_1583_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_addDecls_spec__0(v_as_1581_, v_i_boxed_1588_, v_stop_boxed_1589_, v_b_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_as_1581_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(lean_object* v_n_1594_, lean_object* v_as_1595_, size_t v_sz_1596_, size_t v_i_1597_, lean_object* v_b_1598_){
_start:
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_usize_dec_lt(v_i_1597_, v_sz_1596_);
if (v___x_1599_ == 0)
{
lean_inc_ref(v_b_1598_);
return v_b_1598_;
}
else
{
lean_object* v___x_1600_; lean_object* v_a_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1600_ = lean_box(0);
v_a_1601_ = lean_array_uget_borrowed(v_as_1595_, v_i_1597_);
v___x_1602_ = l_Lean_IR_Decl_name(v_a_1601_);
v___x_1603_ = lean_name_eq(v___x_1602_, v_n_1594_);
lean_dec(v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v___x_1604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v___x_1605_ = ((size_t)1ULL);
v___x_1606_ = lean_usize_add(v_i_1597_, v___x_1605_);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1594_, v_as_1595_, v_sz_1596_, v___x_1606_, v___x_1604_);
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_inc(v_a_1601_);
v___x_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_a_1601_);
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1600_);
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___boxed(lean_object* v_n_1611_, lean_object* v_as_1612_, lean_object* v_sz_1613_, lean_object* v_i_1614_, lean_object* v_b_1615_){
_start:
{
size_t v_sz_boxed_1616_; size_t v_i_boxed_1617_; lean_object* v_res_1618_; 
v_sz_boxed_1616_ = lean_unbox_usize(v_sz_1613_);
lean_dec(v_sz_1613_);
v_i_boxed_1617_ = lean_unbox_usize(v_i_1614_);
lean_dec(v_i_1614_);
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1611_, v_as_1612_, v_sz_boxed_1616_, v_i_boxed_1617_, v_b_1615_);
lean_dec_ref(v_b_1615_);
lean_dec_ref(v_as_1612_);
lean_dec(v_n_1611_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27(lean_object* v_env_1619_, lean_object* v_n_1620_, lean_object* v_decls_1621_){
_start:
{
lean_object* v___x_1622_; size_t v_sz_1623_; size_t v___x_1624_; lean_object* v___x_1625_; lean_object* v_fst_1626_; 
v___x_1622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0___closed__0));
v_sz_1623_ = lean_array_size(v_decls_1621_);
v___x_1624_ = ((size_t)0ULL);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_findEnvDecl_x27_spec__0(v_n_1620_, v_decls_1621_, v_sz_1623_, v___x_1624_, v___x_1622_);
v_fst_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_fst_1626_);
lean_dec_ref(v___x_1625_);
if (lean_obj_tag(v_fst_1626_) == 0)
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_IR_findEnvDecl(v_env_1619_, v_n_1620_);
return v___x_1627_;
}
else
{
lean_object* v_val_1628_; 
v_val_1628_ = lean_ctor_get(v_fst_1626_, 0);
lean_inc(v_val_1628_);
lean_dec_ref(v_fst_1626_);
if (lean_obj_tag(v_val_1628_) == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_IR_findEnvDecl(v_env_1619_, v_n_1620_);
return v___x_1629_;
}
else
{
lean_dec(v_n_1620_);
lean_dec_ref(v_env_1619_);
return v_val_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findEnvDecl_x27___boxed(lean_object* v_env_1630_, lean_object* v_n_1631_, lean_object* v_decls_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_IR_findEnvDecl_x27(v_env_1630_, v_n_1631_, v_decls_1632_);
lean_dec_ref(v_decls_1632_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg(lean_object* v_n_1634_, lean_object* v_decls_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_env_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = lean_st_ref_get(v_a_1636_);
v_env_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_ref(v_env_1639_);
lean_dec(v___x_1638_);
v___x_1640_ = l_Lean_IR_findEnvDecl_x27(v_env_1639_, v_n_1634_, v_decls_1635_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___redArg___boxed(lean_object* v_n_1642_, lean_object* v_decls_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_IR_findDecl_x27___redArg(v_n_1642_, v_decls_1643_, v_a_1644_);
lean_dec(v_a_1644_);
lean_dec_ref(v_decls_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27(lean_object* v_n_1647_, lean_object* v_decls_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_IR_findDecl_x27___redArg(v_n_1647_, v_decls_1648_, v_a_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_findDecl_x27___boxed(lean_object* v_n_1653_, lean_object* v_decls_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_IR_findDecl_x27(v_n_1653_, v_decls_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec_ref(v_decls_1654_);
return v_res_1658_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(lean_object* v_n_1659_, lean_object* v_as_1660_, size_t v_i_1661_, size_t v_stop_1662_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = lean_usize_dec_eq(v_i_1661_, v_stop_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1664_ = lean_array_uget_borrowed(v_as_1660_, v_i_1661_);
v___x_1665_ = l_Lean_IR_Decl_name(v___x_1664_);
v___x_1666_ = lean_name_eq(v___x_1665_, v_n_1659_);
lean_dec(v___x_1665_);
if (v___x_1666_ == 0)
{
size_t v___x_1667_; size_t v___x_1668_; 
v___x_1667_ = ((size_t)1ULL);
v___x_1668_ = lean_usize_add(v_i_1661_, v___x_1667_);
v_i_1661_ = v___x_1668_;
goto _start;
}
else
{
return v___x_1666_;
}
}
else
{
uint8_t v___x_1670_; 
v___x_1670_ = 0;
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0___boxed(lean_object* v_n_1671_, lean_object* v_as_1672_, lean_object* v_i_1673_, lean_object* v_stop_1674_){
_start:
{
size_t v_i_boxed_1675_; size_t v_stop_boxed_1676_; uint8_t v_res_1677_; lean_object* v_r_1678_; 
v_i_boxed_1675_ = lean_unbox_usize(v_i_1673_);
lean_dec(v_i_1673_);
v_stop_boxed_1676_ = lean_unbox_usize(v_stop_1674_);
lean_dec(v_stop_1674_);
v_res_1677_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1671_, v_as_1672_, v_i_boxed_1675_, v_stop_boxed_1676_);
lean_dec_ref(v_as_1672_);
lean_dec(v_n_1671_);
v_r_1678_ = lean_box(v_res_1677_);
return v_r_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg(lean_object* v_n_1679_, lean_object* v_decls_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_array_get_size(v_decls_1680_);
v___x_1685_ = lean_nat_dec_lt(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_IR_containsDecl___redArg(v_n_1679_, v_a_1681_);
return v___x_1686_;
}
else
{
if (v___x_1685_ == 0)
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_IR_containsDecl___redArg(v_n_1679_, v_a_1681_);
return v___x_1687_;
}
else
{
size_t v___x_1688_; size_t v___x_1689_; uint8_t v___x_1690_; 
v___x_1688_ = ((size_t)0ULL);
v___x_1689_ = lean_usize_of_nat(v___x_1684_);
v___x_1690_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_IR_containsDecl_x27_spec__0(v_n_1679_, v_decls_1680_, v___x_1688_, v___x_1689_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_IR_containsDecl___redArg(v_n_1679_, v_a_1681_);
return v___x_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v_n_1679_);
v___x_1692_ = lean_box(v___x_1690_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___redArg___boxed(lean_object* v_n_1694_, lean_object* v_decls_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1694_, v_decls_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_decls_1695_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27(lean_object* v_n_1699_, lean_object* v_decls_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_IR_containsDecl_x27___redArg(v_n_1699_, v_decls_1700_, v_a_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_containsDecl_x27___boxed(lean_object* v_n_1705_, lean_object* v_decls_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_IR_containsDecl_x27(v_n_1705_, v_decls_1706_, v_a_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec_ref(v_decls_1706_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27(lean_object* v_n_1711_, lean_object* v_decls_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1716_; lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1734_; 
lean_inc(v_n_1711_);
v___x_1716_ = l_Lean_IR_findDecl_x27___redArg(v_n_1711_, v_decls_1712_, v_a_1714_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1734_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1734_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
if (lean_obj_tag(v_a_1717_) == 1)
{
lean_object* v_val_1721_; lean_object* v___x_1723_; 
lean_dec(v_n_1711_);
v_val_1721_ = lean_ctor_get(v_a_1717_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v_a_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v_val_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_val_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
else
{
lean_object* v___x_1725_; uint8_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_del_object(v___x_1719_);
lean_dec(v_a_1717_);
v___x_1725_ = ((lean_object*)(l_Lean_IR_getDecl___closed__0));
v___x_1726_ = 1;
v___x_1727_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1711_, v___x_1726_);
v___x_1728_ = lean_string_append(v___x_1725_, v___x_1727_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = ((lean_object*)(l_Lean_IR_getDecl___closed__1));
v___x_1730_ = lean_string_append(v___x_1728_, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
v___x_1732_ = l_Lean_MessageData_ofFormat(v___x_1731_);
v___x_1733_ = l_Lean_throwError___at___00Lean_IR_getDecl_spec__0___redArg(v___x_1732_, v_a_1713_, v_a_1714_);
return v___x_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getDecl_x27___boxed(lean_object* v_n_1735_, lean_object* v_decls_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_IR_getDecl_x27(v_n_1735_, v_decls_1736_, v_a_1737_, v_a_1738_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec_ref(v_decls_1736_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* lean_decl_get_sorry_dep(lean_object* v_env_1741_, lean_object* v_declName_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_IR_findEnvDecl(v_env_1741_, v_declName_1742_);
if (lean_obj_tag(v___x_1743_) == 1)
{
lean_object* v_val_1744_; 
v_val_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1744_);
lean_dec_ref(v___x_1743_);
if (lean_obj_tag(v_val_1744_) == 0)
{
lean_object* v_info_1745_; 
v_info_1745_ = lean_ctor_get(v_val_1744_, 4);
lean_inc(v_info_1745_);
lean_dec_ref(v_val_1744_);
return v_info_1745_;
}
else
{
lean_object* v___x_1746_; 
lean_dec(v_val_1744_);
v___x_1746_ = lean_box(0);
return v___x_1746_;
}
}
else
{
lean_object* v___x_1747_; 
lean_dec(v___x_1743_);
v___x_1747_ = lean_box(0);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(lean_object* v_env_1748_, uint8_t v_level_1749_, uint8_t v_includeDecls_1750_, lean_object* v_as_1751_, size_t v_i_1752_, size_t v_stop_1753_, lean_object* v_b_1754_){
_start:
{
lean_object* v___y_1756_; uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_eq(v_i_1752_, v_stop_1753_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; uint8_t v___y_1763_; 
v___x_1761_ = lean_array_uget_borrowed(v_as_1751_, v_i_1752_);
if (v_includeDecls_1750_ == 0)
{
uint8_t v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = 1;
lean_inc(v___x_1761_);
lean_inc_ref(v_env_1748_);
v___x_1772_ = l_Lean_Environment_contains(v_env_1748_, v___x_1761_, v___x_1771_);
if (v___x_1772_ == 0)
{
goto v___jp_1767_;
}
else
{
v___y_1756_ = v_b_1754_;
goto v___jp_1755_;
}
}
else
{
goto v___jp_1767_;
}
v___jp_1762_:
{
if (v___y_1763_ == 0)
{
uint8_t v___x_1764_; 
lean_inc_ref(v_env_1748_);
v___x_1764_ = l_Lean_isDeclMeta(v_env_1748_, v___x_1761_);
if (v___x_1764_ == 0)
{
v___y_1756_ = v_b_1754_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1765_; 
lean_inc(v___x_1761_);
v___x_1765_ = lean_array_push(v_b_1754_, v___x_1761_);
v___y_1756_ = v___x_1765_;
goto v___jp_1755_;
}
}
else
{
lean_object* v___x_1766_; 
lean_inc(v___x_1761_);
v___x_1766_ = lean_array_push(v_b_1754_, v___x_1761_);
v___y_1756_ = v___x_1766_;
goto v___jp_1755_;
}
}
v___jp_1767_:
{
uint8_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = 2;
v___x_1769_ = l_Lean_instDecidableEqOLeanLevel(v_level_1749_, v___x_1768_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; 
lean_inc_ref(v_env_1748_);
v___x_1770_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1748_, v___x_1761_);
v___y_1763_ = v___x_1770_;
goto v___jp_1762_;
}
else
{
v___y_1763_ = v___x_1769_;
goto v___jp_1762_;
}
}
}
else
{
lean_dec_ref(v_env_1748_);
return v_b_1754_;
}
v___jp_1755_:
{
size_t v___x_1757_; size_t v___x_1758_; 
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1752_, v___x_1757_);
v_i_1752_ = v___x_1758_;
v_b_1754_ = v___y_1756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1___boxed(lean_object* v_env_1773_, lean_object* v_level_1774_, lean_object* v_includeDecls_1775_, lean_object* v_as_1776_, lean_object* v_i_1777_, lean_object* v_stop_1778_, lean_object* v_b_1779_){
_start:
{
uint8_t v_level_boxed_1780_; uint8_t v_includeDecls_boxed_1781_; size_t v_i_boxed_1782_; size_t v_stop_boxed_1783_; lean_object* v_res_1784_; 
v_level_boxed_1780_ = lean_unbox(v_level_1774_);
v_includeDecls_boxed_1781_ = lean_unbox(v_includeDecls_1775_);
v_i_boxed_1782_ = lean_unbox_usize(v_i_1777_);
lean_dec(v_i_1777_);
v_stop_boxed_1783_ = lean_unbox_usize(v_stop_1778_);
lean_dec(v_stop_1778_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1773_, v_level_boxed_1780_, v_includeDecls_boxed_1781_, v_as_1776_, v_i_boxed_1782_, v_stop_boxed_1783_, v_b_1779_);
lean_dec_ref(v_as_1776_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(size_t v_sz_1785_, size_t v_i_1786_, lean_object* v_bs_1787_){
_start:
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_usize_dec_lt(v_i_1786_, v_sz_1785_);
if (v___x_1788_ == 0)
{
return v_bs_1787_;
}
else
{
lean_object* v_v_1789_; lean_object* v___x_1790_; lean_object* v_bs_x27_1791_; lean_object* v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
v_v_1789_ = lean_array_uget(v_bs_1787_, v_i_1786_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v_bs_x27_1791_ = lean_array_uset(v_bs_1787_, v_i_1786_, v___x_1790_);
v___x_1792_ = l_Lean_IR_Decl_name(v_v_1789_);
lean_dec(v_v_1789_);
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_add(v_i_1786_, v___x_1793_);
v___x_1795_ = lean_array_uset(v_bs_x27_1791_, v_i_1786_, v___x_1792_);
v_i_1786_ = v___x_1794_;
v_bs_1787_ = v___x_1795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0___boxed(lean_object* v_sz_1797_, lean_object* v_i_1798_, lean_object* v_bs_1799_){
_start:
{
size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1797_);
lean_dec(v_sz_1797_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_boxed_1800_, v_i_boxed_1801_, v_bs_1799_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* lean_get_ir_extra_const_names(lean_object* v_env_1805_, uint8_t v_level_1806_, uint8_t v_includeDecls_1807_){
_start:
{
lean_object* v___x_1808_; lean_object* v_toEnvExtension_1809_; lean_object* v_asyncMode_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; size_t v_sz_1814_; size_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1808_ = l_Lean_IR_declMapExt;
v_toEnvExtension_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc_ref(v_toEnvExtension_1809_);
v_asyncMode_1810_ = lean_ctor_get(v_toEnvExtension_1809_, 2);
lean_inc(v_asyncMode_1810_);
lean_dec_ref(v_toEnvExtension_1809_);
v___x_1811_ = lean_obj_once(&l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2, &l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2_once, _init_l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_exportIREntries___closed__2);
lean_inc_ref(v_env_1805_);
v___x_1812_ = l_Lean_SimplePersistentEnvExtension_getEntries___redArg(v___x_1811_, v___x_1808_, v_env_1805_, v_asyncMode_1810_);
lean_dec(v_asyncMode_1810_);
v___x_1813_ = lean_array_mk(v___x_1812_);
v_sz_1814_ = lean_array_size(v___x_1813_);
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__0(v_sz_1814_, v___x_1815_, v___x_1813_);
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = lean_array_get_size(v___x_1816_);
v___x_1819_ = ((lean_object*)(l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___closed__0));
v___x_1820_ = lean_nat_dec_lt(v___x_1817_, v___x_1818_);
if (v___x_1820_ == 0)
{
lean_dec_ref(v___x_1816_);
lean_dec_ref(v_env_1805_);
return v___x_1819_;
}
else
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_nat_dec_le(v___x_1818_, v___x_1818_);
if (v___x_1821_ == 0)
{
if (v___x_1820_ == 0)
{
lean_dec_ref(v___x_1816_);
lean_dec_ref(v_env_1805_);
return v___x_1819_;
}
else
{
size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_usize_of_nat(v___x_1818_);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1805_, v_level_1806_, v_includeDecls_1807_, v___x_1816_, v___x_1815_, v___x_1822_, v___x_1819_);
lean_dec_ref(v___x_1816_);
return v___x_1823_;
}
}
else
{
size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_usize_of_nat(v___x_1818_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames_spec__1(v_env_1805_, v_level_1806_, v_includeDecls_1807_, v___x_1816_, v___x_1815_, v___x_1824_, v___x_1819_);
lean_dec_ref(v___x_1816_);
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_getIRExtraConstNames___boxed(lean_object* v_env_1826_, lean_object* v_level_1827_, lean_object* v_includeDecls_1828_){
_start:
{
uint8_t v_level_boxed_1829_; uint8_t v_includeDecls_boxed_1830_; lean_object* v_res_1831_; 
v_level_boxed_1829_ = lean_unbox(v_level_1827_);
v_includeDecls_boxed_1830_ = lean_unbox(v_includeDecls_1828_);
v_res_1831_ = lean_get_ir_extra_const_names(v_env_1826_, v_level_boxed_1829_, v_includeDecls_boxed_1830_);
return v_res_1831_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_IR_initFn_00___x40_Lean_Compiler_IR_CompilerM_310386119____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_declMapExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_declMapExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_CompilerM(builtin);
}
#ifdef __cplusplus
}
#endif
