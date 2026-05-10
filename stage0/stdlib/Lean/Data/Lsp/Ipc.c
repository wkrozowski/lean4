// Lean compiler output
// Module: Lean.Data.Lsp.Ipc
// Imports: public import Lean.Data.Lsp.Communication public import Lean.Data.Lsp.Diagnostics public import Lean.Data.Lsp.Extra import Init.Data.List.Sort.Basic public import Lean.Data.Lsp.LanguageFeatures import Init.While
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(lean_object*);
lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(lean_object*);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Lsp_instToJsonLeanImport_toJson(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object*);
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig = (const lean_object*)&l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Data.Lsp.Ipc"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Lsp.Ipc.shutdown"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: result.isNull\n      "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exit"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expected id "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", got id "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_shutdown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "shutdown"};
static const lean_object* l_Lean_Lsp_Ipc_shutdown___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_shutdown___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unexpected result '"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'\n"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Expected JSON-RPC response, got: '"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2_value;
static const lean_closure_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "jsonrpc"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "2.0"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5_value)}};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4_value),((lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6_value)}};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object*);
static const lean_ctor_object l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/publishDiagnostics"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Waiting for diagnostics failed: "};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1_value;
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Cannot decode publishDiagnostics parameters\n"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_collectDiagnostics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/waitForDiagnostics"};
static const lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_collectDiagnostics___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Waiting for ILeans failed: "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_waitForILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "$/lean/waitForILeans"};
static const lean_object* l_Lean_Lsp_Ipc_waitForILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_waitForILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "item"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 25, 3, 135, 237, 12, 111, 54)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "CallHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__4_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ipc"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_0),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_1),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(35, 217, 114, 230, 122, 150, 157, 83)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_2),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(200, 239, 250, 28, 105, 0, 0, 121)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromRanges"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(22, 83, 65, 87, 105, 214, 49, 248)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "children"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19_value),LEAN_SCALAR_PTR_LITERAL(207, 29, 161, 81, 49, 98, 4, 106)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object*);
static const lean_array_object l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "callHierarchy/incomingCalls"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "textDocument/prepareCallHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0_value;
static const lean_array_object l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "callHierarchy/outgoingCalls"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ModuleHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(35, 217, 114, 230, 122, 150, 157, 83)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_2),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 116, 164, 77, 111, 32, 93, 177)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "$/lean/moduleHierarchy/imports"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "$/lean/prepareModuleHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 2, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "$/lean/moduleHierarchy/importedBy"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_Ipc_runWith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_Ipc_runWith___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_runWith___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object* v_a_5_){
_start:
{
lean_object* v_stdin_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_stdin_7_ = lean_ctor_get(v_a_5_, 0);
lean_inc(v_stdin_7_);
v___x_8_ = lean_stream_of_handle(v_stdin_7_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin___boxed(lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Lsp_Ipc_stdin(v_a_10_);
lean_dec_ref(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object* v_a_13_){
_start:
{
lean_object* v_stdout_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_stdout_15_ = lean_ctor_get(v_a_13_, 1);
lean_inc(v_stdout_15_);
v___x_16_ = lean_stream_of_handle(v_stdout_15_);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout___boxed(lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Lsp_Ipc_stdout(v_a_18_);
lean_dec_ref(v_a_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object* v_inst_21_, lean_object* v_r_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_a_26_; lean_object* v___x_27_; 
v___x_25_ = l_Lean_Lsp_Ipc_stdin(v_a_23_);
v_a_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_a_26_);
lean_dec_ref(v___x_25_);
v___x_27_ = l_IO_FS_Stream_writeLspRequest___redArg(v_inst_21_, v_a_26_, v_r_22_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg___boxed(lean_object* v_inst_28_, lean_object* v_r_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Lsp_Ipc_writeRequest___redArg(v_inst_28_, v_r_29_, v_a_30_);
lean_dec_ref(v_a_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_r_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Lsp_Ipc_writeRequest___redArg(v_inst_34_, v_r_35_, v_a_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___boxed(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_r_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Lsp_Ipc_writeRequest(v_00_u03b1_39_, v_inst_40_, v_r_41_, v_a_42_);
lean_dec_ref(v_a_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object* v_inst_45_, lean_object* v_n_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; lean_object* v_a_50_; lean_object* v___x_51_; 
v___x_49_ = l_Lean_Lsp_Ipc_stdin(v_a_47_);
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v___x_49_);
v___x_51_ = l_IO_FS_Stream_writeLspNotification___redArg(v_inst_45_, v_a_50_, v_n_46_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg___boxed(lean_object* v_inst_52_, lean_object* v_n_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Lsp_Ipc_writeNotification___redArg(v_inst_52_, v_n_53_, v_a_54_);
lean_dec_ref(v_a_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_n_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Lsp_Ipc_writeNotification___redArg(v_inst_58_, v_n_59_, v_a_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___boxed(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, lean_object* v_n_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Lsp_Ipc_writeNotification(v_00_u03b1_63_, v_inst_64_, v_n_65_, v_a_66_);
lean_dec_ref(v_a_66_);
return v_res_68_;
}
}
static lean_object* _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = l_instInhabitedError;
v___x_70_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_70_, 0, lean_box(0));
lean_closure_set(v___x_70_, 1, lean_box(0));
lean_closure_set(v___x_70_, 2, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(lean_object* v_msg_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_3697__overap_76_; lean_object* v___x_77_; 
v___x_74_ = lean_obj_once(&l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0, &l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0_once, _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0);
v___f_75_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_75_, 0, v___x_74_);
v___x_3697__overap_76_ = lean_panic_fn_borrowed(v___f_75_, v_msg_71_);
lean_dec_ref(v___f_75_);
lean_inc_ref(v___y_72_);
v___x_77_ = lean_apply_2(v___x_3697__overap_76_, v___y_72_, lean_box(0));
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___boxed(lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(v_msg_78_, v___y_79_);
lean_dec_ref(v___y_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object* v_h_82_, lean_object* v_n_83_){
_start:
{
lean_object* v_method_85_; lean_object* v_param_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_106_; 
v_method_85_ = lean_ctor_get(v_n_83_, 0);
v_param_86_ = lean_ctor_get(v_n_83_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_n_83_);
if (v_isSharedCheck_106_ == 0)
{
v___x_88_ = v_n_83_;
v_isShared_89_ = v_isSharedCheck_106_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_param_86_);
lean_inc(v_method_85_);
lean_dec(v_n_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_106_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___y_91_; lean_object* v___x_96_; 
v___x_96_ = l_Lean_Json_Structured_fromJson_x3f(v_param_86_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_96_);
v___x_97_ = lean_box(0);
v___y_91_ = v___x_97_;
goto v___jp_90_;
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
v_a_98_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
v___y_91_ = v___x_103_;
goto v___jp_90_;
}
}
}
v___jp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 1);
lean_ctor_set(v___x_88_, 1, v___y_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_method_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___y_91_);
v___x_93_ = v_reuseFailAlloc_95_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; 
v___x_94_ = l_IO_FS_Stream_writeLspMessage(v_h_82_, v___x_93_);
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object* v_h_107_, lean_object* v_n_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(v_h_107_, v_n_108_);
return v_res_110_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_114_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2));
v___x_115_ = lean_unsigned_to_nat(6u);
v___x_116_ = lean_unsigned_to_nat(56u);
v___x_117_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1));
v___x_118_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0));
v___x_119_ = l_mkPanicMessageWithDecl(v___x_118_, v___x_117_, v___x_116_, v___x_115_, v___x_114_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v___x_130_, lean_object* v_requestNo_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
lean_inc_ref(v_a_128_);
v___x_134_ = l_IO_FS_Stream_readLspMessage(v_a_128_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_195_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_195_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_195_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_195_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
if (lean_obj_tag(v_a_135_) == 2)
{
lean_object* v_id_139_; lean_object* v_result_140_; uint8_t v___x_141_; 
v_id_139_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_id_139_);
v_result_140_ = lean_ctor_get(v_a_135_, 1);
lean_inc(v_result_140_);
lean_dec_ref(v_a_135_);
v___x_141_ = l_Lean_Json_isNull(v_result_140_);
lean_dec(v_result_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_id_139_);
lean_del_object(v___x_137_);
v___x_142_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3, &l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3);
v___x_143_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(v___x_142_, v___y_132_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_153_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
if (lean_obj_tag(v_a_144_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; 
lean_dec(v_requestNo_131_);
lean_dec_ref(v_a_129_);
lean_dec_ref(v_a_128_);
v_a_148_ = lean_ctor_get(v_a_144_, 0);
lean_inc(v_a_148_);
lean_dec_ref(v_a_144_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v_a_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
else
{
lean_dec_ref(v_a_144_);
lean_del_object(v___x_146_);
goto _start;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_requestNo_131_);
lean_dec_ref(v_a_129_);
lean_dec_ref(v_a_128_);
v_a_154_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_143_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_143_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v___x_162_; uint8_t v___x_174_; 
lean_dec_ref(v_a_128_);
v___x_162_ = lean_box(0);
v___x_174_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_139_, v___x_130_);
if (v___x_174_ == 0)
{
if (v___x_141_ == 0)
{
lean_dec(v_id_139_);
lean_del_object(v___x_137_);
lean_dec(v_requestNo_131_);
goto v___jp_163_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___y_181_; 
lean_dec_ref(v_a_129_);
v___x_175_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_176_ = l_Nat_reprFast(v_requestNo_131_);
v___x_177_ = lean_string_append(v___x_175_, v___x_176_);
lean_dec_ref(v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_179_ = lean_string_append(v___x_177_, v___x_178_);
switch(lean_obj_tag(v_id_139_))
{
case 0:
{
lean_object* v_s_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_s_187_ = lean_ctor_get(v_id_139_, 0);
lean_inc_ref(v_s_187_);
lean_dec_ref(v_id_139_);
v___x_188_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_189_ = lean_string_append(v___x_188_, v_s_187_);
lean_dec_ref(v_s_187_);
v___x_190_ = lean_string_append(v___x_189_, v___x_188_);
v___y_181_ = v___x_190_;
goto v___jp_180_;
}
case 1:
{
lean_object* v_n_191_; lean_object* v___x_192_; 
v_n_191_ = lean_ctor_get(v_id_139_, 0);
lean_inc_ref(v_n_191_);
lean_dec_ref(v_id_139_);
v___x_192_ = l_Lean_JsonNumber_toString(v_n_191_);
v___y_181_ = v___x_192_;
goto v___jp_180_;
}
default: 
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_181_ = v___x_193_;
goto v___jp_180_;
}
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = lean_string_append(v___x_179_, v___y_181_);
lean_dec_ref(v___y_181_);
v___x_183_ = lean_mk_io_user_error(v___x_182_);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 1);
lean_ctor_set(v___x_137_, 0, v___x_183_);
v___x_185_ = v___x_137_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_dec(v_id_139_);
lean_del_object(v___x_137_);
lean_dec(v_requestNo_131_);
goto v___jp_163_;
}
v___jp_163_:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_165_ = l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(v_a_129_, v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v___x_165_, 0);
lean_dec(v_unused_173_);
v___x_167_ = v___x_165_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_dec(v___x_165_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_162_);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_162_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
return v___x_165_;
}
}
}
}
else
{
lean_del_object(v___x_137_);
lean_dec(v_a_135_);
goto _start;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec(v_requestNo_131_);
lean_dec_ref(v_a_129_);
lean_dec_ref(v_a_128_);
v_a_196_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_134_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_134_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v___x_206_, lean_object* v_requestNo_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_204_, v_a_205_, v___x_206_, v_requestNo_207_, v___y_208_);
lean_dec_ref(v___y_208_);
lean_dec(v___x_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object* v_h_211_, lean_object* v_r_212_){
_start:
{
lean_object* v_id_214_; lean_object* v_method_215_; lean_object* v_param_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_236_; 
v_id_214_ = lean_ctor_get(v_r_212_, 0);
v_method_215_ = lean_ctor_get(v_r_212_, 1);
v_param_216_ = lean_ctor_get(v_r_212_, 2);
v_isSharedCheck_236_ = !lean_is_exclusive(v_r_212_);
if (v_isSharedCheck_236_ == 0)
{
v___x_218_ = v_r_212_;
v_isShared_219_ = v_isSharedCheck_236_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_param_216_);
lean_inc(v_method_215_);
lean_inc(v_id_214_);
lean_dec(v_r_212_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_236_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___y_221_; lean_object* v___x_226_; 
v___x_226_ = l_Lean_Json_Structured_fromJson_x3f(v_param_216_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; 
lean_dec_ref(v___x_226_);
v___x_227_ = lean_box(0);
v___y_221_ = v___x_227_;
goto v___jp_220_;
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_228_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_226_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
v___y_221_ = v___x_233_;
goto v___jp_220_;
}
}
}
v___jp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 2, v___y_221_);
v___x_223_ = v___x_218_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_id_214_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_method_215_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v___y_221_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; 
v___x_224_ = l_IO_FS_Stream_writeLspMessage(v_h_211_, v___x_223_);
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object* v_h_237_, lean_object* v_r_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_h_237_, v_r_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object* v_requestNo_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_a_246_; lean_object* v___x_247_; lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_270_; 
v___x_245_ = l_Lean_Lsp_Ipc_stdout(v_a_243_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v___x_245_);
v___x_247_ = l_Lean_Lsp_Ipc_stdin(v_a_243_);
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_270_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_270_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_270_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_inc(v_requestNo_242_);
v___x_252_ = l_Lean_JsonNumber_fromNat(v_requestNo_242_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 1);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_269_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_255_ = ((lean_object*)(l_Lean_Lsp_Ipc_shutdown___closed__0));
v___x_256_ = lean_box(0);
lean_inc_ref(v___x_254_);
v___x_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_254_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_inc(v_a_248_);
v___x_258_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_a_248_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; 
lean_dec_ref(v___x_258_);
v___x_259_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_246_, v_a_248_, v___x_254_, v_requestNo_242_, v_a_243_);
lean_dec_ref(v___x_254_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_259_, 0);
lean_dec(v_unused_268_);
v___x_261_ = v___x_259_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_dec(v___x_259_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
return v___x_259_;
}
}
else
{
lean_dec_ref(v___x_254_);
lean_dec(v_a_248_);
lean_dec(v_a_246_);
lean_dec(v_requestNo_242_);
return v___x_258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object* v_requestNo_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Lsp_Ipc_shutdown(v_requestNo_271_, v_a_272_);
lean_dec_ref(v_a_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object* v_v_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Json_Structured_fromJson_x3f(v_v_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v___x_279_, lean_object* v_requestNo_280_, lean_object* v_inst_281_, lean_object* v_a_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_277_, v_a_278_, v___x_279_, v_requestNo_280_, v___y_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v___x_288_, lean_object* v_requestNo_289_, lean_object* v_inst_290_, lean_object* v_a_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(v_a_286_, v_a_287_, v___x_288_, v_requestNo_289_, v_inst_290_, v_a_291_, v___y_292_);
lean_dec_ref(v___y_292_);
lean_dec(v___x_288_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_299_; 
v___x_297_ = l_Lean_Lsp_Ipc_stdout(v_a_295_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref(v___x_297_);
v___x_299_ = l_IO_FS_Stream_readLspMessage(v_a_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage___boxed(lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Lsp_Ipc_readMessage(v_a_300_);
lean_dec_ref(v_a_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object* v_expectedMethod_303_, lean_object* v_inst_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_309_; 
v___x_307_ = l_Lean_Lsp_Ipc_stdout(v_a_305_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_307_);
v___x_309_ = l_IO_FS_Stream_readLspRequestAs___redArg(v_a_308_, v_expectedMethod_303_, v_inst_304_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg___boxed(lean_object* v_expectedMethod_310_, lean_object* v_inst_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_310_, v_inst_311_, v_a_312_);
lean_dec_ref(v_a_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object* v_expectedMethod_315_, lean_object* v_00_u03b1_316_, lean_object* v_inst_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_315_, v_inst_317_, v_a_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___boxed(lean_object* v_expectedMethod_321_, lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Lsp_Ipc_readRequestAs(v_expectedMethod_321_, v_00_u03b1_322_, v_inst_323_, v_a_324_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(32700u);
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14);
v___x_347_ = lean_int_neg(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15);
v___x_349_ = l_Lean_JsonNumber_fromInt(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16);
v___x_351_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(32600u);
v___x_353_ = lean_nat_to_int(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18);
v___x_355_ = lean_int_neg(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19);
v___x_357_ = l_Lean_JsonNumber_fromInt(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20);
v___x_359_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(32601u);
v___x_361_ = lean_nat_to_int(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22);
v___x_363_ = lean_int_neg(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23);
v___x_365_ = l_Lean_JsonNumber_fromInt(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24);
v___x_367_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(32602u);
v___x_369_ = lean_nat_to_int(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26);
v___x_371_ = lean_int_neg(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27);
v___x_373_ = l_Lean_JsonNumber_fromInt(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28);
v___x_375_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(32603u);
v___x_377_ = lean_nat_to_int(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30);
v___x_379_ = lean_int_neg(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31);
v___x_381_ = l_Lean_JsonNumber_fromInt(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32);
v___x_383_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(32002u);
v___x_385_ = lean_nat_to_int(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34);
v___x_387_ = lean_int_neg(v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35);
v___x_389_ = l_Lean_JsonNumber_fromInt(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36);
v___x_391_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(32001u);
v___x_393_ = lean_nat_to_int(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38);
v___x_395_ = lean_int_neg(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39);
v___x_397_ = l_Lean_JsonNumber_fromInt(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40);
v___x_399_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(32801u);
v___x_401_ = lean_nat_to_int(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42);
v___x_403_ = lean_int_neg(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43);
v___x_405_ = l_Lean_JsonNumber_fromInt(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44);
v___x_407_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(32800u);
v___x_409_ = lean_nat_to_int(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46);
v___x_411_ = lean_int_neg(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47);
v___x_413_ = l_Lean_JsonNumber_fromInt(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48);
v___x_415_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(32900u);
v___x_417_ = lean_nat_to_int(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50);
v___x_419_ = lean_int_neg(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51);
v___x_421_ = l_Lean_JsonNumber_fromInt(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52);
v___x_423_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(32901u);
v___x_425_ = lean_nat_to_int(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54);
v___x_427_ = lean_int_neg(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55);
v___x_429_ = l_Lean_JsonNumber_fromInt(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56);
v___x_431_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(32902u);
v___x_433_ = lean_nat_to_int(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58);
v___x_435_ = lean_int_neg(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59);
v___x_437_ = l_Lean_JsonNumber_fromInt(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60);
v___x_439_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object* v_expectedID_440_, lean_object* v_inst_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Lsp_Ipc_stdout(v_a_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_589_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_589_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_589_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_589_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; 
v___x_449_ = l_IO_FS_Stream_readLspMessage(v_a_445_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_580_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_580_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_580_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_580_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___y_455_; lean_object* v___y_456_; 
switch(lean_obj_tag(v_a_450_))
{
case 2:
{
lean_object* v_id_462_; lean_object* v_result_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_507_; 
v_id_462_ = lean_ctor_get(v_a_450_, 0);
v_result_463_ = lean_ctor_get(v_a_450_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_507_ == 0)
{
v___x_465_ = v_a_450_;
v_isShared_466_ = v_isSharedCheck_507_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_result_463_);
lean_inc(v_id_462_);
lean_dec(v_a_450_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_507_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_462_, v_expectedID_440_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___y_470_; 
lean_del_object(v___x_465_);
lean_dec(v_result_463_);
lean_del_object(v___x_447_);
lean_dec_ref(v_inst_441_);
v___x_468_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_440_))
{
case 0:
{
lean_object* v_s_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_s_481_ = lean_ctor_get(v_expectedID_440_, 0);
lean_inc_ref(v_s_481_);
lean_dec_ref(v_expectedID_440_);
v___x_482_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_483_ = lean_string_append(v___x_482_, v_s_481_);
lean_dec_ref(v_s_481_);
v___x_484_ = lean_string_append(v___x_483_, v___x_482_);
v___y_470_ = v___x_484_;
goto v___jp_469_;
}
case 1:
{
lean_object* v_n_485_; lean_object* v___x_486_; 
v_n_485_ = lean_ctor_get(v_expectedID_440_, 0);
lean_inc_ref(v_n_485_);
lean_dec_ref(v_expectedID_440_);
v___x_486_ = l_Lean_JsonNumber_toString(v_n_485_);
v___y_470_ = v___x_486_;
goto v___jp_469_;
}
default: 
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_470_ = v___x_487_;
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_string_append(v___x_468_, v___y_470_);
lean_dec_ref(v___y_470_);
v___x_472_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
switch(lean_obj_tag(v_id_462_))
{
case 0:
{
lean_object* v_s_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_s_474_ = lean_ctor_get(v_id_462_, 0);
lean_inc_ref(v_s_474_);
lean_dec_ref(v_id_462_);
v___x_475_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_476_ = lean_string_append(v___x_475_, v_s_474_);
lean_dec_ref(v_s_474_);
v___x_477_ = lean_string_append(v___x_476_, v___x_475_);
v___y_455_ = v___x_473_;
v___y_456_ = v___x_477_;
goto v___jp_454_;
}
case 1:
{
lean_object* v_n_478_; lean_object* v___x_479_; 
v_n_478_ = lean_ctor_get(v_id_462_, 0);
lean_inc_ref(v_n_478_);
lean_dec_ref(v_id_462_);
v___x_479_ = l_Lean_JsonNumber_toString(v_n_478_);
v___y_455_ = v___x_473_;
v___y_456_ = v___x_479_;
goto v___jp_454_;
}
default: 
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_455_ = v___x_473_;
v___y_456_ = v___x_480_;
goto v___jp_454_;
}
}
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_id_462_);
lean_del_object(v___x_452_);
lean_inc(v_result_463_);
v___x_488_ = lean_apply_1(v_inst_441_, v_result_463_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
lean_del_object(v___x_465_);
lean_dec(v_expectedID_440_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
v___x_490_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_491_ = l_Lean_Json_compress(v_result_463_);
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
lean_dec_ref(v___x_491_);
v___x_493_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_494_ = lean_string_append(v___x_492_, v___x_493_);
v___x_495_ = lean_string_append(v___x_494_, v_a_489_);
lean_dec(v_a_489_);
v___x_496_ = lean_mk_io_user_error(v___x_495_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 0, v___x_496_);
v___x_498_ = v___x_447_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; 
lean_dec(v_result_463_);
v_a_500_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v___x_488_);
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 0);
lean_ctor_set(v___x_465_, 1, v_a_500_);
lean_ctor_set(v___x_465_, 0, v_expectedID_440_);
v___x_502_ = v___x_465_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_expectedID_440_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_a_500_);
v___x_502_ = v_reuseFailAlloc_506_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_502_);
v___x_504_ = v___x_447_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_508_; uint8_t v_code_509_; lean_object* v_message_510_; lean_object* v_data_x3f_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___x_544_; lean_object* v___y_546_; 
lean_del_object(v___x_452_);
lean_dec_ref(v_inst_441_);
lean_dec(v_expectedID_440_);
v_id_508_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_id_508_);
v_code_509_ = lean_ctor_get_uint8(v_a_450_, sizeof(void*)*3);
v_message_510_ = lean_ctor_get(v_a_450_, 1);
lean_inc_ref(v_message_510_);
v_data_x3f_511_ = lean_ctor_get(v_a_450_, 2);
lean_inc(v_data_x3f_511_);
lean_dec_ref(v_a_450_);
v___x_512_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_513_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3));
v___x_514_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_544_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_508_))
{
case 0:
{
lean_object* v_s_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_s_562_ = lean_ctor_get(v_id_508_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_id_508_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v_id_508_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_s_562_);
lean_dec(v_id_508_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 3);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_s_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
v___y_546_ = v___x_567_;
goto v___jp_545_;
}
}
}
case 1:
{
lean_object* v_n_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_n_570_ = lean_ctor_get(v_id_508_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_id_508_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v_id_508_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_n_570_);
lean_dec(v_id_508_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 2);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_n_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
v___y_546_ = v___x_575_;
goto v___jp_545_;
}
}
}
default: 
{
lean_object* v___x_578_; 
v___x_578_ = lean_box(0);
v___y_546_ = v___x_578_;
goto v___jp_545_;
}
}
v___jp_515_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_518_);
lean_ctor_set(v___x_520_, 1, v___y_519_);
v___x_521_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_522_, 0, v_message_510_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_520_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_528_ = l_Lean_Json_opt___redArg(v___x_513_, v___x_527_, v_data_x3f_511_);
v___x_529_ = l_List_appendTR___redArg(v___x_526_, v___x_528_);
v___x_530_ = l_Lean_Json_mkObj(v___x_529_);
lean_dec(v___x_529_);
lean_inc_ref(v___y_517_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_517_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v___x_524_);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_516_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_514_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_Json_mkObj(v___x_534_);
lean_dec_ref(v___x_534_);
v___x_536_ = l_Lean_Json_compress(v___x_535_);
v___x_537_ = lean_string_append(v___x_512_, v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v___x_540_ = lean_mk_io_user_error(v___x_539_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 0, v___x_540_);
v___x_542_ = v___x_447_;
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
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_544_);
lean_ctor_set(v___x_547_, 1, v___y_546_);
v___x_548_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_549_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_509_)
{
case 0:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_550_;
goto v___jp_515_;
}
case 1:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_551_;
goto v___jp_515_;
}
case 2:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_552_;
goto v___jp_515_;
}
case 3:
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_553_;
goto v___jp_515_;
}
case 4:
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_554_;
goto v___jp_515_;
}
case 5:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_555_;
goto v___jp_515_;
}
case 6:
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_556_;
goto v___jp_515_;
}
case 7:
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_557_;
goto v___jp_515_;
}
case 8:
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_558_;
goto v___jp_515_;
}
case 9:
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_559_;
goto v___jp_515_;
}
case 10:
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_560_;
goto v___jp_515_;
}
default: 
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_561_;
goto v___jp_515_;
}
}
}
}
default: 
{
lean_del_object(v___x_452_);
lean_dec(v_a_450_);
lean_del_object(v___x_447_);
goto _start;
}
}
v___jp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_string_append(v___y_455_, v___y_456_);
lean_dec_ref(v___y_456_);
v___x_458_ = lean_mk_io_user_error(v___x_457_);
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 1);
lean_ctor_set(v___x_452_, 0, v___x_458_);
v___x_460_ = v___x_452_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_del_object(v___x_447_);
lean_dec_ref(v_inst_441_);
lean_dec(v_expectedID_440_);
v_a_581_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_449_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_449_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v_inst_441_);
lean_dec(v_expectedID_440_);
v_a_590_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_444_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_444_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___boxed(lean_object* v_expectedID_598_, lean_object* v_inst_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_598_, v_inst_599_, v_a_600_);
lean_dec_ref(v_a_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* v_expectedID_603_, lean_object* v_00_u03b1_604_, lean_object* v_inst_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_603_, v_inst_605_, v_a_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___boxed(lean_object* v_expectedID_609_, lean_object* v_00_u03b1_610_, lean_object* v_inst_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Lsp_Ipc_readResponseAs(v_expectedID_609_, v_00_u03b1_610_, v_inst_611_, v_a_612_);
lean_dec_ref(v_a_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_618_ = lean_io_process_child_wait(v___x_617_, v_a_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Lsp_Ipc_waitForExit(v_a_619_);
lean_dec_ref(v_a_619_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object* v_d1_622_, lean_object* v_d2_623_){
_start:
{
uint8_t v___y_625_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d1_622_);
v___x_629_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d2_623_);
v___x_630_ = l_Lean_Lsp_instOrdRange_ord(v___x_628_, v___x_629_);
lean_dec_ref(v___x_629_);
lean_dec_ref(v___x_628_);
if (v___x_630_ == 1)
{
lean_object* v_message_631_; lean_object* v_message_632_; uint8_t v___x_633_; 
v_message_631_ = lean_ctor_get(v_d1_622_, 6);
v_message_632_ = lean_ctor_get(v_d2_623_, 6);
v___x_633_ = lean_string_dec_lt(v_message_631_, v_message_632_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = lean_string_dec_eq(v_message_631_, v_message_632_);
if (v___x_634_ == 0)
{
return v___x_634_;
}
else
{
v___y_625_ = v___x_630_;
goto v___jp_624_;
}
}
else
{
return v___x_633_;
}
}
else
{
v___y_625_ = v___x_630_;
goto v___jp_624_;
}
v___jp_624_:
{
if (v___y_625_ == 2)
{
uint8_t v___x_626_; 
v___x_626_ = 0;
return v___x_626_;
}
else
{
uint8_t v___x_627_; 
v___x_627_ = 1;
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object* v_d1_635_, lean_object* v_d2_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(v_d1_635_, v_d2_636_);
lean_dec_ref(v_d2_636_);
lean_dec_ref(v_d1_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object* v_p_640_){
_start:
{
lean_object* v_uri_641_; lean_object* v_version_x3f_642_; lean_object* v_isIncremental_x3f_643_; lean_object* v_diagnostics_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_655_; 
v_uri_641_ = lean_ctor_get(v_p_640_, 0);
v_version_x3f_642_ = lean_ctor_get(v_p_640_, 1);
v_isIncremental_x3f_643_ = lean_ctor_get(v_p_640_, 2);
v_diagnostics_644_ = lean_ctor_get(v_p_640_, 3);
v_isSharedCheck_655_ = !lean_is_exclusive(v_p_640_);
if (v_isSharedCheck_655_ == 0)
{
v___x_646_ = v_p_640_;
v_isShared_647_ = v_isSharedCheck_655_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_diagnostics_644_);
lean_inc(v_isIncremental_x3f_643_);
lean_inc(v_version_x3f_642_);
lean_inc(v_uri_641_);
lean_dec(v_p_640_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_655_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v_sorted_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___f_648_ = ((lean_object*)(l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0));
v___x_649_ = lean_array_to_list(v_diagnostics_644_);
v_sorted_650_ = l_List_mergeSort___redArg(v___x_649_, v___f_648_);
v___x_651_ = lean_array_mk(v_sorted_650_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 3, v___x_651_);
v___x_653_ = v___x_646_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_uri_641_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_version_x3f_642_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_isIncremental_x3f_643_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(lean_object* v_prev_x3f_659_, lean_object* v_next_660_){
_start:
{
lean_object* v_uri_661_; lean_object* v_version_x3f_662_; lean_object* v_isIncremental_x3f_663_; lean_object* v_diagnostics_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_687_; 
v_uri_661_ = lean_ctor_get(v_next_660_, 0);
v_version_x3f_662_ = lean_ctor_get(v_next_660_, 1);
v_isIncremental_x3f_663_ = lean_ctor_get(v_next_660_, 2);
v_diagnostics_664_ = lean_ctor_get(v_next_660_, 3);
v_isSharedCheck_687_ = !lean_is_exclusive(v_next_660_);
if (v_isSharedCheck_687_ == 0)
{
v___x_666_ = v_next_660_;
v_isShared_667_ = v_isSharedCheck_687_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_diagnostics_664_);
lean_inc(v_isIncremental_x3f_663_);
lean_inc(v_version_x3f_662_);
lean_inc(v_uri_661_);
lean_dec(v_next_660_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_687_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v_replace_670_; 
v___x_668_ = ((lean_object*)(l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0));
lean_inc_ref(v_diagnostics_664_);
lean_inc(v_version_x3f_662_);
lean_inc_ref(v_uri_661_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 2, v___x_668_);
v_replace_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_uri_661_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_version_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_diagnostics_664_);
v_replace_670_ = v_reuseFailAlloc_686_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
if (lean_obj_tag(v_prev_x3f_659_) == 1)
{
if (lean_obj_tag(v_isIncremental_x3f_663_) == 0)
{
lean_dec_ref(v_prev_x3f_659_);
lean_dec_ref(v_diagnostics_664_);
lean_dec(v_version_x3f_662_);
lean_dec_ref(v_uri_661_);
return v_replace_670_;
}
else
{
lean_object* v_val_671_; uint8_t v___x_672_; 
v_val_671_ = lean_ctor_get(v_isIncremental_x3f_663_, 0);
lean_inc(v_val_671_);
lean_dec_ref(v_isIncremental_x3f_663_);
v___x_672_ = lean_unbox(v_val_671_);
lean_dec(v_val_671_);
if (v___x_672_ == 0)
{
lean_dec_ref(v_prev_x3f_659_);
lean_dec_ref(v_diagnostics_664_);
lean_dec(v_version_x3f_662_);
lean_dec_ref(v_uri_661_);
return v_replace_670_;
}
else
{
lean_object* v_val_673_; lean_object* v_diagnostics_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_replace_670_);
v_val_673_ = lean_ctor_get(v_prev_x3f_659_, 0);
lean_inc(v_val_673_);
lean_dec_ref(v_prev_x3f_659_);
v_diagnostics_674_ = lean_ctor_get(v_val_673_, 3);
v_isSharedCheck_682_ = !lean_is_exclusive(v_val_673_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_683_ = lean_ctor_get(v_val_673_, 2);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_val_673_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_val_673_, 0);
lean_dec(v_unused_685_);
v___x_676_ = v_val_673_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_diagnostics_674_);
lean_dec(v_val_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Array_append___redArg(v_diagnostics_674_, v_diagnostics_664_);
lean_dec_ref(v_diagnostics_664_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 3, v___x_678_);
lean_ctor_set(v___x_676_, 2, v___x_668_);
lean_ctor_set(v___x_676_, 1, v_version_x3f_662_);
lean_ctor_set(v___x_676_, 0, v_uri_661_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_uri_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_version_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
else
{
lean_dec_ref(v_diagnostics_664_);
lean_dec(v_isIncremental_x3f_663_);
lean_dec(v_version_x3f_662_);
lean_dec_ref(v_uri_661_);
lean_dec(v_prev_x3f_659_);
return v_replace_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* v_waitForDiagnosticsId_691_, lean_object* v_accumulated_x3f_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Lsp_Ipc_readMessage(v_a_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_765_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_765_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_765_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_765_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
switch(lean_obj_tag(v_a_696_))
{
case 2:
{
lean_object* v_id_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_726_; 
v_id_700_ = lean_ctor_get(v_a_696_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_696_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_a_696_, 1);
lean_dec(v_unused_727_);
v___x_702_ = v_a_696_;
v_isShared_703_ = v_isSharedCheck_726_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_id_700_);
lean_dec(v_a_696_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_726_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_700_, v_waitForDiagnosticsId_691_);
lean_dec(v_id_700_);
if (v___x_704_ == 0)
{
lean_del_object(v___x_702_);
lean_del_object(v___x_698_);
goto _start;
}
else
{
if (lean_obj_tag(v_accumulated_x3f_692_) == 0)
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_del_object(v___x_702_);
v___x_706_ = lean_box(0);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_706_);
v___x_708_ = v___x_698_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_725_; 
v_val_710_ = lean_ctor_get(v_accumulated_x3f_692_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_accumulated_x3f_692_);
if (v_isSharedCheck_725_ == 0)
{
v___x_712_ = v_accumulated_x3f_692_;
v_isShared_713_ = v_isSharedCheck_725_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_dec(v_accumulated_x3f_692_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_725_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_715_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(v_val_710_);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 0);
lean_ctor_set(v___x_702_, 1, v___x_715_);
lean_ctor_set(v___x_702_, 0, v___x_714_);
v___x_717_ = v___x_702_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_724_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_717_);
v___x_719_ = v___x_712_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_719_);
v___x_721_ = v___x_698_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
}
}
case 3:
{
lean_object* v_id_728_; lean_object* v_message_729_; uint8_t v___x_730_; 
v_id_728_ = lean_ctor_get(v_a_696_, 0);
lean_inc(v_id_728_);
v_message_729_ = lean_ctor_get(v_a_696_, 1);
lean_inc_ref(v_message_729_);
lean_dec_ref(v_a_696_);
v___x_730_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_728_, v_waitForDiagnosticsId_691_);
lean_dec(v_id_728_);
if (v___x_730_ == 0)
{
lean_dec_ref(v_message_729_);
lean_del_object(v___x_698_);
goto _start;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec(v_accumulated_x3f_692_);
v___x_732_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1));
v___x_733_ = lean_string_append(v___x_732_, v_message_729_);
lean_dec_ref(v_message_729_);
v___x_734_ = lean_mk_io_user_error(v___x_733_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
lean_ctor_set(v___x_698_, 0, v___x_734_);
v___x_736_ = v___x_698_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
case 1:
{
lean_object* v_method_738_; lean_object* v_params_x3f_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_method_738_ = lean_ctor_get(v_a_696_, 0);
lean_inc_ref(v_method_738_);
v_params_x3f_739_ = lean_ctor_get(v_a_696_, 1);
lean_inc(v_params_x3f_739_);
lean_dec_ref(v_a_696_);
v___x_740_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_741_ = lean_string_dec_eq(v_method_738_, v___x_740_);
lean_dec_ref(v_method_738_);
if (v___x_741_ == 0)
{
lean_dec(v_params_x3f_739_);
lean_del_object(v___x_698_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_739_) == 1)
{
lean_object* v_val_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_762_; 
v_val_743_ = lean_ctor_get(v_params_x3f_739_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_params_x3f_739_);
if (v_isSharedCheck_762_ == 0)
{
v___x_745_ = v_params_x3f_739_;
v_isShared_746_ = v_isSharedCheck_762_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_val_743_);
lean_dec(v_params_x3f_739_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_762_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = l_Lean_Json_Structured_toJson(v_val_743_);
v___x_748_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
lean_del_object(v___x_745_);
lean_dec(v_accumulated_x3f_692_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_751_ = lean_string_append(v___x_750_, v_a_749_);
lean_dec(v_a_749_);
v___x_752_ = lean_mk_io_user_error(v___x_751_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
lean_ctor_set(v___x_698_, 0, v___x_752_);
v___x_754_ = v___x_698_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
lean_del_object(v___x_698_);
v_a_756_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_748_);
v___x_757_ = l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(v_accumulated_x3f_692_, v_a_756_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_757_);
v___x_759_ = v___x_745_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
v_accumulated_x3f_692_ = v___x_759_;
goto _start;
}
}
}
}
else
{
lean_dec(v_params_x3f_739_);
lean_del_object(v___x_698_);
goto _start;
}
}
}
default: 
{
lean_del_object(v___x_698_);
lean_dec(v_a_696_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_accumulated_x3f_692_);
v_a_766_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_695_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_695_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* v_waitForDiagnosticsId_774_, lean_object* v_accumulated_x3f_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_774_, v_accumulated_x3f_775_, v_a_776_);
lean_dec_ref(v_a_776_);
lean_dec(v_waitForDiagnosticsId_774_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object* v_v_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(v_v_779_);
v___x_781_ = l_Lean_Json_Structured_fromJson_x3f(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* v_h_782_, lean_object* v_r_783_){
_start:
{
lean_object* v_id_785_; lean_object* v_method_786_; lean_object* v_param_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_807_; 
v_id_785_ = lean_ctor_get(v_r_783_, 0);
v_method_786_ = lean_ctor_get(v_r_783_, 1);
v_param_787_ = lean_ctor_get(v_r_783_, 2);
v_isSharedCheck_807_ = !lean_is_exclusive(v_r_783_);
if (v_isSharedCheck_807_ == 0)
{
v___x_789_ = v_r_783_;
v_isShared_790_ = v_isSharedCheck_807_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_param_787_);
lean_inc(v_method_786_);
lean_inc(v_id_785_);
lean_dec(v_r_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_807_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___y_792_; lean_object* v___x_797_; 
v___x_797_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(v_param_787_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v___x_797_);
v___x_798_ = lean_box(0);
v___y_792_ = v___x_798_;
goto v___jp_791_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_797_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v___y_792_ = v___x_804_;
goto v___jp_791_;
}
}
}
v___jp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 2, v___y_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_id_785_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_method_786_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v___y_792_);
v___x_794_ = v_reuseFailAlloc_796_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; 
v___x_795_ = l_IO_FS_Stream_writeLspMessage(v_h_782_, v___x_794_);
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object* v_h_808_, lean_object* v_r_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_h_808_, v_r_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object* v_r_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_a_816_; lean_object* v___x_817_; 
v___x_815_ = l_Lean_Lsp_Ipc_stdin(v_a_813_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_a_816_, v_r_812_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object* v_r_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v_r_818_, v_a_819_);
lean_dec_ref(v_a_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* v_waitForDiagnosticsId_823_, lean_object* v_target_824_, lean_object* v_version_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_828_ = ((lean_object*)(l_Lean_Lsp_Ipc_collectDiagnostics___closed__0));
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_target_824_);
lean_ctor_set(v___x_829_, 1, v_version_825_);
lean_inc(v_waitForDiagnosticsId_823_);
v___x_830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_830_, 0, v_waitForDiagnosticsId_823_);
lean_ctor_set(v___x_830_, 1, v___x_828_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
v___x_831_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v___x_830_, v_a_826_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v___x_831_);
v___x_832_ = lean_box(0);
v___x_833_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_823_, v___x_832_, v_a_826_);
lean_dec(v_waitForDiagnosticsId_823_);
return v___x_833_;
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_waitForDiagnosticsId_823_);
v_a_834_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_831_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object* v_waitForDiagnosticsId_842_, lean_object* v_target_843_, lean_object* v_version_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Lsp_Ipc_collectDiagnostics(v_waitForDiagnosticsId_842_, v_target_843_, v_version_844_, v_a_845_);
lean_dec_ref(v_a_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object* v_v_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(v_v_848_);
v___x_850_ = l_Lean_Json_Structured_fromJson_x3f(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* v_h_851_, lean_object* v_r_852_){
_start:
{
lean_object* v_id_854_; lean_object* v_method_855_; lean_object* v_param_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_876_; 
v_id_854_ = lean_ctor_get(v_r_852_, 0);
v_method_855_ = lean_ctor_get(v_r_852_, 1);
v_param_856_ = lean_ctor_get(v_r_852_, 2);
v_isSharedCheck_876_ = !lean_is_exclusive(v_r_852_);
if (v_isSharedCheck_876_ == 0)
{
v___x_858_ = v_r_852_;
v_isShared_859_ = v_isSharedCheck_876_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_param_856_);
lean_inc(v_method_855_);
lean_inc(v_id_854_);
lean_dec(v_r_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_876_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___y_861_; lean_object* v___x_866_; 
v___x_866_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(v_param_856_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_867_; 
lean_dec_ref(v___x_866_);
v___x_867_ = lean_box(0);
v___y_861_ = v___x_867_;
goto v___jp_860_;
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_866_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
v___y_861_ = v___x_873_;
goto v___jp_860_;
}
}
}
v___jp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 2, v___y_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_id_854_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_method_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v___y_861_);
v___x_863_ = v_reuseFailAlloc_865_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; 
v___x_864_ = l_IO_FS_Stream_writeLspMessage(v_h_851_, v___x_863_);
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object* v_h_877_, lean_object* v_r_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_h_877_, v_r_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object* v_r_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_886_; 
v___x_884_ = l_Lean_Lsp_Ipc_stdin(v_a_882_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v___x_886_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_a_885_, v_r_881_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object* v_r_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v_r_887_, v_a_888_);
lean_dec_ref(v_a_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object* v_waitForILeansId_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Lsp_Ipc_readMessage(v___y_898_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_923_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_923_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_923_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_923_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
switch(lean_obj_tag(v_a_901_))
{
case 2:
{
lean_object* v_id_905_; uint8_t v___x_906_; 
v_id_905_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_id_905_);
lean_dec_ref(v_a_901_);
v___x_906_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_905_, v_waitForILeansId_897_);
lean_dec(v_id_905_);
if (v___x_906_ == 0)
{
lean_del_object(v___x_903_);
goto _start;
}
else
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1));
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_908_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
case 3:
{
lean_object* v_id_912_; lean_object* v_message_913_; uint8_t v___x_914_; 
v_id_912_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_id_912_);
v_message_913_ = lean_ctor_get(v_a_901_, 1);
lean_inc_ref(v_message_913_);
lean_dec_ref(v_a_901_);
v___x_914_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_912_, v_waitForILeansId_897_);
lean_dec(v_id_912_);
if (v___x_914_ == 0)
{
lean_dec_ref(v_message_913_);
lean_del_object(v___x_903_);
goto _start;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_916_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2));
v___x_917_ = lean_string_append(v___x_916_, v_message_913_);
lean_dec_ref(v_message_913_);
v___x_918_ = lean_mk_io_user_error(v___x_917_);
if (v_isShared_904_ == 0)
{
lean_ctor_set_tag(v___x_903_, 1);
lean_ctor_set(v___x_903_, 0, v___x_918_);
v___x_920_ = v___x_903_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
default: 
{
lean_del_object(v___x_903_);
lean_dec(v_a_901_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_900_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_900_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object* v_waitForILeansId_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_932_, v___y_933_);
lean_dec_ref(v___y_933_);
lean_dec(v_waitForILeansId_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object* v_waitForILeansId_937_, lean_object* v_target_938_, lean_object* v_version_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_942_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v_target_938_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_version_939_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
lean_inc(v_waitForILeansId_937_);
v___x_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_946_, 0, v_waitForILeansId_937_);
lean_ctor_set(v___x_946_, 1, v___x_942_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
v___x_947_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_946_, v_a_940_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v___x_948_; 
lean_dec_ref(v___x_947_);
v___x_948_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_937_, v_a_940_);
lean_dec(v_waitForILeansId_937_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_962_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_962_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_962_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_962_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_fst_953_; 
v_fst_953_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_fst_953_);
lean_dec(v_a_949_);
if (lean_obj_tag(v_fst_953_) == 0)
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_box(0);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_954_);
v___x_956_ = v___x_951_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
else
{
lean_object* v_val_958_; lean_object* v___x_960_; 
v_val_958_ = lean_ctor_get(v_fst_953_, 0);
lean_inc(v_val_958_);
lean_dec_ref(v_fst_953_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_val_958_);
v___x_960_ = v___x_951_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_val_958_);
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
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_948_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_948_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
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
lean_dec(v_waitForILeansId_937_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object* v_waitForILeansId_971_, lean_object* v_target_972_, lean_object* v_version_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Lsp_Ipc_waitForILeans(v_waitForILeansId_971_, v_target_972_, v_version_973_, v_a_974_);
lean_dec_ref(v_a_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object* v_waitForILeansId_977_, lean_object* v_inst_978_, lean_object* v_a_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_977_, v___y_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object* v_waitForILeansId_983_, lean_object* v_inst_984_, lean_object* v_a_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(v_waitForILeansId_983_, v_inst_984_, v_a_985_, v___y_986_);
lean_dec_ref(v___y_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_waitForILeansId_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object* v_waitForILeansId_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_994_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_995_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0));
lean_inc(v_waitForILeansId_991_);
v___x_996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_996_, 0, v_waitForILeansId_991_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
lean_ctor_set(v___x_996_, 2, v___x_995_);
v___x_997_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_996_, v_a_992_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; 
lean_dec_ref(v___x_997_);
v___x_998_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_991_, v_a_992_);
lean_dec(v_waitForILeansId_991_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1012_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_fst_1003_; 
v_fst_1003_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_fst_1003_);
lean_dec(v_a_999_);
if (lean_obj_tag(v_fst_1003_) == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_box(0);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1006_ = v___x_1001_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
v_val_1008_ = lean_ctor_get(v_fst_1003_, 0);
lean_inc(v_val_1008_);
lean_dec_ref(v_fst_1003_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_val_1008_);
v___x_1010_ = v___x_1001_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_val_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_998_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_998_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_991_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object* v_waitForILeansId_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Lsp_Ipc_waitForWatchdogILeans(v_waitForILeansId_1021_, v_a_1022_);
lean_dec_ref(v_a_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object* v_msg_1025_, lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = lean_usize_dec_eq(v_i_1027_, v_stop_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v_message_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_array_uget_borrowed(v_as_1026_, v_i_1027_);
v_message_1031_ = lean_ctor_get(v___x_1030_, 6);
v___x_1032_ = lean_string_dec_eq(v_message_1031_, v_msg_1025_);
if (v___x_1032_ == 0)
{
size_t v___x_1033_; size_t v___x_1034_; 
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_add(v_i_1027_, v___x_1033_);
v_i_1027_ = v___x_1034_;
goto _start;
}
else
{
return v___x_1032_;
}
}
else
{
uint8_t v___x_1036_; 
v___x_1036_ = 0;
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object* v_msg_1037_, lean_object* v_as_1038_, lean_object* v_i_1039_, lean_object* v_stop_1040_){
_start:
{
size_t v_i_boxed_1041_; size_t v_stop_boxed_1042_; uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_i_boxed_1041_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_stop_boxed_1042_ = lean_unbox_usize(v_stop_1040_);
lean_dec(v_stop_1040_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(v_msg_1037_, v_as_1038_, v_i_boxed_1041_, v_stop_boxed_1042_);
lean_dec_ref(v_as_1038_);
lean_dec_ref(v_msg_1037_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(lean_object* v_msg_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Lsp_Ipc_readMessage(v_a_1046_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1085_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1085_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1085_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
if (lean_obj_tag(v_a_1049_) == 1)
{
lean_object* v_method_1053_; lean_object* v_params_x3f_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_method_1053_ = lean_ctor_get(v_a_1049_, 0);
lean_inc_ref(v_method_1053_);
v_params_x3f_1054_ = lean_ctor_get(v_a_1049_, 1);
lean_inc(v_params_x3f_1054_);
lean_dec_ref(v_a_1049_);
v___x_1055_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_1056_ = lean_string_dec_eq(v_method_1053_, v___x_1055_);
lean_dec_ref(v_method_1053_);
if (v___x_1056_ == 0)
{
lean_dec(v_params_x3f_1054_);
lean_del_object(v___x_1051_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_1054_) == 1)
{
lean_object* v_val_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_val_1058_ = lean_ctor_get(v_params_x3f_1054_, 0);
lean_inc(v_val_1058_);
lean_dec_ref(v_params_x3f_1054_);
v___x_1059_ = l_Lean_Json_Structured_toJson(v_val_1058_);
v___x_1060_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_1059_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_1063_ = lean_string_append(v___x_1062_, v_a_1061_);
lean_dec(v_a_1061_);
v___x_1064_ = lean_mk_io_user_error(v___x_1063_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
lean_ctor_set(v___x_1051_, 0, v___x_1064_);
v___x_1066_ = v___x_1051_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
else
{
lean_object* v_a_1068_; lean_object* v_diagnostics_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_a_1068_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1068_);
lean_dec_ref(v___x_1060_);
v_diagnostics_1069_ = lean_ctor_get(v_a_1068_, 3);
lean_inc_ref(v_diagnostics_1069_);
lean_dec(v_a_1068_);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = lean_array_get_size(v_diagnostics_1069_);
v___x_1072_ = lean_nat_dec_lt(v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v_diagnostics_1069_);
lean_del_object(v___x_1051_);
goto _start;
}
else
{
if (v___x_1072_ == 0)
{
lean_dec_ref(v_diagnostics_1069_);
lean_del_object(v___x_1051_);
goto _start;
}
else
{
size_t v___x_1075_; size_t v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = ((size_t)0ULL);
v___x_1076_ = lean_usize_of_nat(v___x_1071_);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(v_msg_1045_, v_diagnostics_1069_, v___x_1075_, v___x_1076_);
lean_dec_ref(v_diagnostics_1069_);
if (v___x_1077_ == 0)
{
lean_del_object(v___x_1051_);
goto _start;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1079_);
v___x_1081_ = v___x_1051_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
}
else
{
lean_dec(v_params_x3f_1054_);
lean_del_object(v___x_1051_);
goto _start;
}
}
}
else
{
lean_del_object(v___x_1051_);
lean_dec(v_a_1049_);
goto _start;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1048_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1048_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object* v_msg_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(v_msg_1094_, v_a_1095_);
lean_dec_ref(v_a_1095_);
lean_dec_ref(v_msg_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object* v_msg_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(v_msg_1098_, v_a_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object* v_msg_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Lsp_Ipc_waitForMessage(v_msg_1102_, v_a_1103_);
lean_dec_ref(v_a_1103_);
lean_dec_ref(v_msg_1102_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object* v_j_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = l_Lean_Json_getObjValD(v_j_1106_, v_k_1107_);
v___x_1109_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object* v_j_1110_, lean_object* v_k_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_j_1110_, v_k_1111_);
lean_dec_ref(v_k_1111_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1113_, size_t v_i_1114_, lean_object* v_bs_1115_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_lt(v_i_1114_, v_sz_1113_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_bs_1115_);
return v___x_1117_;
}
else
{
lean_object* v_v_1118_; lean_object* v___x_1119_; 
v_v_1118_ = lean_array_uget_borrowed(v_bs_1115_, v_i_1114_);
lean_inc(v_v_1118_);
v___x_1119_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_v_1118_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_bs_1115_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v_bs_x27_1130_; size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; 
v_a_1128_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1119_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v_bs_x27_1130_ = lean_array_uset(v_bs_1115_, v_i_1114_, v___x_1129_);
v___x_1131_ = ((size_t)1ULL);
v___x_1132_ = lean_usize_add(v_i_1114_, v___x_1131_);
v___x_1133_ = lean_array_uset(v_bs_x27_1130_, v_i_1114_, v_a_1128_);
v_i_1114_ = v___x_1132_;
v_bs_1115_ = v___x_1133_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1135_, lean_object* v_i_1136_, lean_object* v_bs_1137_){
_start:
{
size_t v_sz_boxed_1138_; size_t v_i_boxed_1139_; lean_object* v_res_1140_; 
v_sz_boxed_1138_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1139_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1138_, v_i_boxed_1139_, v_bs_1137_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1142_) == 4)
{
lean_object* v_elems_1143_; size_t v_sz_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v_elems_1143_ = lean_ctor_get(v_x_1142_, 0);
lean_inc_ref(v_elems_1143_);
lean_dec_ref(v_x_1142_);
v_sz_1144_ = lean_array_size(v_elems_1143_);
v___x_1145_ = ((size_t)0ULL);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_1144_, v___x_1145_, v_elems_1143_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1147_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1148_ = lean_unsigned_to_nat(80u);
v___x_1149_ = l_Lean_Json_pretty(v_x_1142_, v___x_1148_);
v___x_1150_ = lean_string_append(v___x_1147_, v___x_1149_);
lean_dec_ref(v___x_1149_);
v___x_1151_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1152_ = lean_string_append(v___x_1150_, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object* v_j_1154_, lean_object* v_k_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = l_Lean_Json_getObjValD(v_j_1154_, v_k_1155_);
v___x_1157_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object* v_j_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_j_1158_, v_k_1159_);
lean_dec_ref(v_k_1159_);
return v_res_1160_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = 1;
v___x_1166_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9));
v___x_1167_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = 1;
v___x_1179_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5));
v___x_1180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1179_, v___x_1178_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_1182_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6);
v___x_1183_ = lean_string_append(v___x_1182_, v___x_1181_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_1185_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1186_ = lean_string_append(v___x_1185_, v___x_1184_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1188_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11);
v___x_1189_ = lean_string_append(v___x_1188_, v___x_1187_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = 1;
v___x_1194_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15));
v___x_1195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1194_, v___x_1193_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16);
v___x_1197_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1198_ = lean_string_append(v___x_1197_, v___x_1196_);
return v___x_1198_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1200_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17);
v___x_1201_ = lean_string_append(v___x_1200_, v___x_1199_);
return v___x_1201_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = 1;
v___x_1206_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20));
v___x_1207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1206_, v___x_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_1209_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1210_ = lean_string_append(v___x_1209_, v___x_1208_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1212_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22);
v___x_1213_ = lean_string_append(v___x_1212_, v___x_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object* v_json_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_1214_);
v___x_1216_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_json_1214_, v___x_1215_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_json_1214_);
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1226_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1226_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1221_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13);
v___x_1222_ = lean_string_append(v___x_1221_, v_a_1217_);
lean_dec(v_a_1217_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1222_);
v___x_1224_ = v___x_1219_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_json_1214_);
v_a_1227_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1216_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1216_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 0);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_a_1235_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1216_);
v___x_1236_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
lean_inc(v_json_1214_);
v___x_1237_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_json_1214_, v___x_1236_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1247_; 
lean_dec(v_a_1235_);
lean_dec(v_json_1214_);
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1247_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1242_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18);
v___x_1243_ = lean_string_append(v___x_1242_, v_a_1238_);
lean_dec(v_a_1238_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1243_);
v___x_1245_ = v___x_1240_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_a_1235_);
lean_dec(v_json_1214_);
v_a_1248_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1237_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1237_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set_tag(v___x_1250_, 0);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_a_1256_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v___x_1237_);
v___x_1257_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1258_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_json_1214_, v___x_1257_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_a_1256_);
lean_dec(v_a_1235_);
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1263_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23);
v___x_1264_ = lean_string_append(v___x_1263_, v_a_1259_);
lean_dec(v_a_1259_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1264_);
v___x_1266_ = v___x_1261_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
else
{
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_a_1256_);
lean_dec(v_a_1235_);
v_a_1269_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1258_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1258_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 0);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
v_a_1277_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1279_ = v___x_1258_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1258_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1281_, 0, v_a_1235_);
lean_ctor_set(v___x_1281_, 1, v_a_1256_);
lean_ctor_set(v___x_1281_, 2, v_a_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t v_sz_1286_, size_t v_i_1287_, lean_object* v_bs_1288_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_usize_dec_lt(v_i_1287_, v_sz_1286_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_bs_1288_);
return v___x_1290_;
}
else
{
lean_object* v_v_1291_; lean_object* v___x_1292_; 
v_v_1291_ = lean_array_uget_borrowed(v_bs_1288_, v_i_1287_);
lean_inc(v_v_1291_);
v___x_1292_ = l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(v_v_1291_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v_bs_1288_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v_bs_x27_1303_; size_t v___x_1304_; size_t v___x_1305_; lean_object* v___x_1306_; 
v_a_1301_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1301_);
lean_dec_ref(v___x_1292_);
v___x_1302_ = lean_unsigned_to_nat(0u);
v_bs_x27_1303_ = lean_array_uset(v_bs_1288_, v_i_1287_, v___x_1302_);
v___x_1304_ = ((size_t)1ULL);
v___x_1305_ = lean_usize_add(v_i_1287_, v___x_1304_);
v___x_1306_ = lean_array_uset(v_bs_x27_1303_, v_i_1287_, v_a_1301_);
v_i_1287_ = v___x_1305_;
v_bs_1288_ = v___x_1306_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object* v_x_1308_){
_start:
{
if (lean_obj_tag(v_x_1308_) == 4)
{
lean_object* v_elems_1309_; size_t v_sz_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v_elems_1309_ = lean_ctor_get(v_x_1308_, 0);
lean_inc_ref(v_elems_1309_);
lean_dec_ref(v_x_1308_);
v_sz_1310_ = lean_array_size(v_elems_1309_);
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_1310_, v___x_1311_, v_elems_1309_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1313_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1314_ = lean_unsigned_to_nat(80u);
v___x_1315_ = l_Lean_Json_pretty(v_x_1308_, v___x_1314_);
v___x_1316_ = lean_string_append(v___x_1313_, v___x_1315_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object* v_j_1320_, lean_object* v_k_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = l_Lean_Json_getObjValD(v_j_1320_, v_k_1321_);
v___x_1323_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object* v_j_1324_, lean_object* v_k_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_j_1324_, v_k_1325_);
lean_dec_ref(v_k_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1327_, lean_object* v_i_1328_, lean_object* v_bs_1329_){
_start:
{
size_t v_sz_boxed_1330_; size_t v_i_boxed_1331_; lean_object* v_res_1332_; 
v_sz_boxed_1330_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_i_boxed_1331_ = lean_unbox_usize(v_i_1328_);
lean_dec(v_i_1328_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_boxed_1330_, v_i_boxed_1331_, v_bs_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
if (lean_obj_tag(v_a_1335_) == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_array_to_list(v_a_1336_);
return v___x_1337_;
}
else
{
lean_object* v_head_1338_; lean_object* v_tail_1339_; lean_object* v___x_1340_; 
v_head_1338_ = lean_ctor_get(v_a_1335_, 0);
lean_inc(v_head_1338_);
v_tail_1339_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_tail_1339_);
lean_dec_ref(v_a_1335_);
v___x_1340_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1336_, v_head_1338_);
v_a_1335_ = v_tail_1339_;
v_a_1336_ = v___x_1340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t v_sz_1342_, size_t v_i_1343_, lean_object* v_bs_1344_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_usize_dec_lt(v_i_1343_, v_sz_1342_);
if (v___x_1345_ == 0)
{
return v_bs_1344_;
}
else
{
lean_object* v_v_1346_; lean_object* v___x_1347_; lean_object* v_bs_x27_1348_; lean_object* v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v_v_1346_ = lean_array_uget(v_bs_1344_, v_i_1343_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v_bs_x27_1348_ = lean_array_uset(v_bs_1344_, v_i_1343_, v___x_1347_);
v___x_1349_ = l_Lean_Lsp_instToJsonRange_toJson(v_v_1346_);
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_add(v_i_1343_, v___x_1350_);
v___x_1352_ = lean_array_uset(v_bs_x27_1348_, v_i_1343_, v___x_1349_);
v_i_1343_ = v___x_1351_;
v_bs_1344_ = v___x_1352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1354_, lean_object* v_i_1355_, lean_object* v_bs_1356_){
_start:
{
size_t v_sz_boxed_1357_; size_t v_i_boxed_1358_; lean_object* v_res_1359_; 
v_sz_boxed_1357_ = lean_unbox_usize(v_sz_1354_);
lean_dec(v_sz_1354_);
v_i_boxed_1358_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_boxed_1357_, v_i_boxed_1358_, v_bs_1356_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object* v_a_1360_){
_start:
{
size_t v_sz_1361_; size_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_sz_1361_ = lean_array_size(v_a_1360_);
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_1361_, v___x_1362_, v_a_1360_);
v___x_1364_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object* v_x_1367_){
_start:
{
lean_object* v_item_1368_; lean_object* v_fromRanges_1369_; lean_object* v_children_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_item_1368_ = lean_ctor_get(v_x_1367_, 0);
lean_inc_ref(v_item_1368_);
v_fromRanges_1369_ = lean_ctor_get(v_x_1367_, 1);
lean_inc_ref(v_fromRanges_1369_);
v_children_1370_ = lean_ctor_get(v_x_1367_, 2);
lean_inc_ref(v_children_1370_);
lean_dec_ref(v_x_1367_);
v___x_1371_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_1372_ = l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(v_item_1368_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
v___x_1377_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(v_fromRanges_1369_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___x_1374_);
v___x_1380_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1381_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(v_children_1370_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1374_);
v___x_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___x_1374_);
v___x_1385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1379_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1375_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_1388_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_1386_, v___x_1387_);
v___x_1389_ = l_Lean_Json_mkObj(v___x_1388_);
lean_dec(v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t v_sz_1390_, size_t v_i_1391_, lean_object* v_bs_1392_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_usize_dec_lt(v_i_1391_, v_sz_1390_);
if (v___x_1393_ == 0)
{
return v_bs_1392_;
}
else
{
lean_object* v_v_1394_; lean_object* v___x_1395_; lean_object* v_bs_x27_1396_; lean_object* v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; lean_object* v___x_1400_; 
v_v_1394_ = lean_array_uget(v_bs_1392_, v_i_1391_);
v___x_1395_ = lean_unsigned_to_nat(0u);
v_bs_x27_1396_ = lean_array_uset(v_bs_1392_, v_i_1391_, v___x_1395_);
v___x_1397_ = l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(v_v_1394_);
v___x_1398_ = ((size_t)1ULL);
v___x_1399_ = lean_usize_add(v_i_1391_, v___x_1398_);
v___x_1400_ = lean_array_uset(v_bs_x27_1396_, v_i_1391_, v___x_1397_);
v_i_1391_ = v___x_1399_;
v_bs_1392_ = v___x_1400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object* v_a_1402_){
_start:
{
size_t v_sz_1403_; size_t v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_sz_1403_ = lean_array_size(v_a_1402_);
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_1403_, v___x_1404_, v_a_1402_);
v___x_1406_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object* v_sz_1407_, lean_object* v_i_1408_, lean_object* v_bs_1409_){
_start:
{
size_t v_sz_boxed_1410_; size_t v_i_boxed_1411_; lean_object* v_res_1412_; 
v_sz_boxed_1410_ = lean_unbox_usize(v_sz_1407_);
lean_dec(v_sz_1407_);
v_i_boxed_1411_ = lean_unbox_usize(v_i_1408_);
lean_dec(v_i_1408_);
v_res_1412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_boxed_1410_, v_i_boxed_1411_, v_bs_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object* v_k_1415_, lean_object* v_v_1416_, lean_object* v_t_1417_){
_start:
{
if (lean_obj_tag(v_t_1417_) == 0)
{
lean_object* v_size_1418_; lean_object* v_k_1419_; lean_object* v_v_1420_; lean_object* v_l_1421_; lean_object* v_r_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1703_; 
v_size_1418_ = lean_ctor_get(v_t_1417_, 0);
v_k_1419_ = lean_ctor_get(v_t_1417_, 1);
v_v_1420_ = lean_ctor_get(v_t_1417_, 2);
v_l_1421_ = lean_ctor_get(v_t_1417_, 3);
v_r_1422_ = lean_ctor_get(v_t_1417_, 4);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_t_1417_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1424_ = v_t_1417_;
v_isShared_1425_ = v_isSharedCheck_1703_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_r_1422_);
lean_inc(v_l_1421_);
lean_inc(v_v_1420_);
lean_inc(v_k_1419_);
lean_inc(v_size_1418_);
lean_dec(v_t_1417_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1703_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_string_dec_lt(v_k_1415_, v_k_1419_);
if (v___x_1426_ == 0)
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_string_dec_eq(v_k_1415_, v_k_1419_);
if (v___x_1427_ == 0)
{
lean_object* v_impl_1428_; lean_object* v___x_1429_; 
lean_dec(v_size_1418_);
v_impl_1428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1415_, v_v_1416_, v_r_1422_);
v___x_1429_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1421_) == 0)
{
lean_object* v_size_1430_; lean_object* v_size_1431_; lean_object* v_k_1432_; lean_object* v_v_1433_; lean_object* v_l_1434_; lean_object* v_r_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_size_1430_ = lean_ctor_get(v_l_1421_, 0);
v_size_1431_ = lean_ctor_get(v_impl_1428_, 0);
lean_inc(v_size_1431_);
v_k_1432_ = lean_ctor_get(v_impl_1428_, 1);
lean_inc(v_k_1432_);
v_v_1433_ = lean_ctor_get(v_impl_1428_, 2);
lean_inc(v_v_1433_);
v_l_1434_ = lean_ctor_get(v_impl_1428_, 3);
lean_inc(v_l_1434_);
v_r_1435_ = lean_ctor_get(v_impl_1428_, 4);
lean_inc(v_r_1435_);
v___x_1436_ = lean_unsigned_to_nat(3u);
v___x_1437_ = lean_nat_mul(v___x_1436_, v_size_1430_);
v___x_1438_ = lean_nat_dec_lt(v___x_1437_, v_size_1431_);
lean_dec(v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_dec(v_r_1435_);
lean_dec(v_l_1434_);
lean_dec(v_v_1433_);
lean_dec(v_k_1432_);
v___x_1439_ = lean_nat_add(v___x_1429_, v_size_1430_);
v___x_1440_ = lean_nat_add(v___x_1439_, v_size_1431_);
lean_dec(v_size_1431_);
lean_dec(v___x_1439_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_impl_1428_);
lean_ctor_set(v___x_1424_, 0, v___x_1440_);
v___x_1442_ = v___x_1424_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_l_1421_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_impl_1428_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
else
{
lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1507_; 
v_isSharedCheck_1507_ = !lean_is_exclusive(v_impl_1428_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; 
v_unused_1508_ = lean_ctor_get(v_impl_1428_, 4);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_impl_1428_, 3);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_impl_1428_, 2);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_impl_1428_, 1);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_impl_1428_, 0);
lean_dec(v_unused_1512_);
v___x_1445_ = v_impl_1428_;
v_isShared_1446_ = v_isSharedCheck_1507_;
goto v_resetjp_1444_;
}
else
{
lean_dec(v_impl_1428_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1507_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v_size_1447_; lean_object* v_k_1448_; lean_object* v_v_1449_; lean_object* v_l_1450_; lean_object* v_r_1451_; lean_object* v_size_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v_size_1447_ = lean_ctor_get(v_l_1434_, 0);
v_k_1448_ = lean_ctor_get(v_l_1434_, 1);
v_v_1449_ = lean_ctor_get(v_l_1434_, 2);
v_l_1450_ = lean_ctor_get(v_l_1434_, 3);
v_r_1451_ = lean_ctor_get(v_l_1434_, 4);
v_size_1452_ = lean_ctor_get(v_r_1435_, 0);
v___x_1453_ = lean_unsigned_to_nat(2u);
v___x_1454_ = lean_nat_mul(v___x_1453_, v_size_1452_);
v___x_1455_ = lean_nat_dec_lt(v_size_1447_, v___x_1454_);
lean_dec(v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1483_; 
lean_inc(v_r_1451_);
lean_inc(v_l_1450_);
lean_inc(v_v_1449_);
lean_inc(v_k_1448_);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_l_1434_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1484_ = lean_ctor_get(v_l_1434_, 4);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_l_1434_, 3);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_l_1434_, 2);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_l_1434_, 1);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_l_1434_, 0);
lean_dec(v_unused_1488_);
v___x_1457_ = v_l_1434_;
v_isShared_1458_ = v_isSharedCheck_1483_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v_l_1434_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1483_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1473_; 
v___x_1459_ = lean_nat_add(v___x_1429_, v_size_1430_);
v___x_1460_ = lean_nat_add(v___x_1459_, v_size_1431_);
lean_dec(v_size_1431_);
if (lean_obj_tag(v_l_1450_) == 0)
{
lean_object* v_size_1481_; 
v_size_1481_ = lean_ctor_get(v_l_1450_, 0);
lean_inc(v_size_1481_);
v___y_1473_ = v_size_1481_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_unsigned_to_nat(0u);
v___y_1473_ = v___x_1482_;
goto v___jp_1472_;
}
v___jp_1461_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_nat_add(v___y_1462_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec(v___y_1462_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_r_1435_);
lean_ctor_set(v___x_1457_, 3, v_r_1451_);
lean_ctor_set(v___x_1457_, 2, v_v_1433_);
lean_ctor_set(v___x_1457_, 1, v_k_1432_);
lean_ctor_set(v___x_1457_, 0, v___x_1465_);
v___x_1467_ = v___x_1457_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_k_1432_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_v_1433_);
lean_ctor_set(v_reuseFailAlloc_1471_, 3, v_r_1451_);
lean_ctor_set(v_reuseFailAlloc_1471_, 4, v_r_1435_);
v___x_1467_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1467_);
lean_ctor_set(v___x_1445_, 3, v___y_1463_);
lean_ctor_set(v___x_1445_, 2, v_v_1449_);
lean_ctor_set(v___x_1445_, 1, v_k_1448_);
lean_ctor_set(v___x_1445_, 0, v___x_1460_);
v___x_1469_ = v___x_1445_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_k_1448_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_v_1449_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v___y_1463_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
v___jp_1472_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_nat_add(v___x_1459_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec(v___x_1459_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_l_1450_);
lean_ctor_set(v___x_1424_, 0, v___x_1474_);
v___x_1476_ = v___x_1424_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_l_1421_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_l_1450_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_nat_add(v___x_1429_, v_size_1452_);
if (lean_obj_tag(v_r_1451_) == 0)
{
lean_object* v_size_1478_; 
v_size_1478_ = lean_ctor_get(v_r_1451_, 0);
lean_inc(v_size_1478_);
v___y_1462_ = v___x_1477_;
v___y_1463_ = v___x_1476_;
v___y_1464_ = v_size_1478_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_unsigned_to_nat(0u);
v___y_1462_ = v___x_1477_;
v___y_1463_ = v___x_1476_;
v___y_1464_ = v___x_1479_;
goto v___jp_1461_;
}
}
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_del_object(v___x_1424_);
v___x_1489_ = lean_nat_add(v___x_1429_, v_size_1430_);
v___x_1490_ = lean_nat_add(v___x_1489_, v_size_1431_);
lean_dec(v_size_1431_);
v___x_1491_ = lean_nat_add(v___x_1489_, v_size_1447_);
lean_dec(v___x_1489_);
lean_inc_ref(v_l_1421_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_l_1434_);
lean_ctor_set(v___x_1445_, 3, v_l_1421_);
lean_ctor_set(v___x_1445_, 2, v_v_1420_);
lean_ctor_set(v___x_1445_, 1, v_k_1419_);
lean_ctor_set(v___x_1445_, 0, v___x_1491_);
v___x_1493_ = v___x_1445_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_l_1421_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_l_1434_);
v___x_1493_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_isSharedCheck_1500_ = !lean_is_exclusive(v_l_1421_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; lean_object* v_unused_1502_; lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1501_ = lean_ctor_get(v_l_1421_, 4);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_l_1421_, 3);
lean_dec(v_unused_1502_);
v_unused_1503_ = lean_ctor_get(v_l_1421_, 2);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_l_1421_, 1);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_l_1421_, 0);
lean_dec(v_unused_1505_);
v___x_1495_ = v_l_1421_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v_l_1421_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 4, v_r_1435_);
lean_ctor_set(v___x_1495_, 3, v___x_1493_);
lean_ctor_set(v___x_1495_, 2, v_v_1433_);
lean_ctor_set(v___x_1495_, 1, v_k_1432_);
lean_ctor_set(v___x_1495_, 0, v___x_1490_);
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1432_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1433_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_r_1435_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1513_; 
v_l_1513_ = lean_ctor_get(v_impl_1428_, 3);
lean_inc(v_l_1513_);
if (lean_obj_tag(v_l_1513_) == 0)
{
lean_object* v_r_1514_; lean_object* v_k_1515_; lean_object* v_v_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1539_; 
v_r_1514_ = lean_ctor_get(v_impl_1428_, 4);
v_k_1515_ = lean_ctor_get(v_impl_1428_, 1);
v_v_1516_ = lean_ctor_get(v_impl_1428_, 2);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_impl_1428_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; lean_object* v_unused_1541_; 
v_unused_1540_ = lean_ctor_get(v_impl_1428_, 3);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_impl_1428_, 0);
lean_dec(v_unused_1541_);
v___x_1518_ = v_impl_1428_;
v_isShared_1519_ = v_isSharedCheck_1539_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_r_1514_);
lean_inc(v_v_1516_);
lean_inc(v_k_1515_);
lean_dec(v_impl_1428_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1539_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1535_; 
v_k_1520_ = lean_ctor_get(v_l_1513_, 1);
v_v_1521_ = lean_ctor_get(v_l_1513_, 2);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_l_1513_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; 
v_unused_1536_ = lean_ctor_get(v_l_1513_, 4);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_l_1513_, 3);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_l_1513_, 0);
lean_dec(v_unused_1538_);
v___x_1523_ = v_l_1513_;
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_v_1521_);
lean_inc(v_k_1520_);
lean_dec(v_l_1513_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1525_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1514_, 2);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 4, v_r_1514_);
lean_ctor_set(v___x_1523_, 3, v_r_1514_);
lean_ctor_set(v___x_1523_, 2, v_v_1420_);
lean_ctor_set(v___x_1523_, 1, v_k_1419_);
lean_ctor_set(v___x_1523_, 0, v___x_1429_);
v___x_1527_ = v___x_1523_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1534_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1534_, 3, v_r_1514_);
lean_ctor_set(v_reuseFailAlloc_1534_, 4, v_r_1514_);
v___x_1527_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
lean_inc(v_r_1514_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 3, v_r_1514_);
lean_ctor_set(v___x_1518_, 0, v___x_1429_);
v___x_1529_ = v___x_1518_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1515_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1516_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_r_1514_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_r_1514_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v___x_1529_);
lean_ctor_set(v___x_1424_, 3, v___x_1527_);
lean_ctor_set(v___x_1424_, 2, v_v_1521_);
lean_ctor_set(v___x_1424_, 1, v_k_1520_);
lean_ctor_set(v___x_1424_, 0, v___x_1525_);
v___x_1531_ = v___x_1424_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1520_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1521_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v___x_1527_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
}
else
{
lean_object* v_r_1542_; 
v_r_1542_ = lean_ctor_get(v_impl_1428_, 4);
lean_inc(v_r_1542_);
if (lean_obj_tag(v_r_1542_) == 0)
{
lean_object* v_k_1543_; lean_object* v_v_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1555_; 
v_k_1543_ = lean_ctor_get(v_impl_1428_, 1);
v_v_1544_ = lean_ctor_get(v_impl_1428_, 2);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_impl_1428_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; lean_object* v_unused_1557_; lean_object* v_unused_1558_; 
v_unused_1556_ = lean_ctor_get(v_impl_1428_, 4);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_impl_1428_, 3);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_impl_1428_, 0);
lean_dec(v_unused_1558_);
v___x_1546_ = v_impl_1428_;
v_isShared_1547_ = v_isSharedCheck_1555_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_v_1544_);
lean_inc(v_k_1543_);
lean_dec(v_impl_1428_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1555_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(3u);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 4, v_l_1513_);
lean_ctor_set(v___x_1546_, 2, v_v_1420_);
lean_ctor_set(v___x_1546_, 1, v_k_1419_);
lean_ctor_set(v___x_1546_, 0, v___x_1429_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_l_1513_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_l_1513_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_r_1542_);
lean_ctor_set(v___x_1424_, 3, v___x_1550_);
lean_ctor_set(v___x_1424_, 2, v_v_1544_);
lean_ctor_set(v___x_1424_, 1, v_k_1543_);
lean_ctor_set(v___x_1424_, 0, v___x_1548_);
v___x_1552_ = v___x_1424_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1543_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1544_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_r_1542_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1559_ = lean_unsigned_to_nat(2u);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_impl_1428_);
lean_ctor_set(v___x_1424_, 3, v_r_1542_);
lean_ctor_set(v___x_1424_, 0, v___x_1559_);
v___x_1561_ = v___x_1424_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_r_1542_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_impl_1428_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
else
{
lean_object* v___x_1564_; 
lean_dec(v_v_1420_);
lean_dec(v_k_1419_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 2, v_v_1416_);
lean_ctor_set(v___x_1424_, 1, v_k_1415_);
v___x_1564_ = v___x_1424_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_size_1418_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_l_1421_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_r_1422_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_object* v_impl_1566_; lean_object* v___x_1567_; 
lean_dec(v_size_1418_);
v_impl_1566_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1415_, v_v_1416_, v_l_1421_);
v___x_1567_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1422_) == 0)
{
lean_object* v_size_1568_; lean_object* v_size_1569_; lean_object* v_k_1570_; lean_object* v_v_1571_; lean_object* v_l_1572_; lean_object* v_r_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_size_1568_ = lean_ctor_get(v_r_1422_, 0);
v_size_1569_ = lean_ctor_get(v_impl_1566_, 0);
lean_inc(v_size_1569_);
v_k_1570_ = lean_ctor_get(v_impl_1566_, 1);
lean_inc(v_k_1570_);
v_v_1571_ = lean_ctor_get(v_impl_1566_, 2);
lean_inc(v_v_1571_);
v_l_1572_ = lean_ctor_get(v_impl_1566_, 3);
lean_inc(v_l_1572_);
v_r_1573_ = lean_ctor_get(v_impl_1566_, 4);
lean_inc(v_r_1573_);
v___x_1574_ = lean_unsigned_to_nat(3u);
v___x_1575_ = lean_nat_mul(v___x_1574_, v_size_1568_);
v___x_1576_ = lean_nat_dec_lt(v___x_1575_, v_size_1569_);
lean_dec(v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_r_1573_);
lean_dec(v_l_1572_);
lean_dec(v_v_1571_);
lean_dec(v_k_1570_);
v___x_1577_ = lean_nat_add(v___x_1567_, v_size_1569_);
lean_dec(v_size_1569_);
v___x_1578_ = lean_nat_add(v___x_1577_, v_size_1568_);
lean_dec(v___x_1577_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 3, v_impl_1566_);
lean_ctor_set(v___x_1424_, 0, v___x_1578_);
v___x_1580_ = v___x_1424_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_impl_1566_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v_r_1422_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1647_; 
v_isSharedCheck_1647_ = !lean_is_exclusive(v_impl_1566_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; lean_object* v_unused_1649_; lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; 
v_unused_1648_ = lean_ctor_get(v_impl_1566_, 4);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_impl_1566_, 3);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_impl_1566_, 2);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_impl_1566_, 1);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_impl_1566_, 0);
lean_dec(v_unused_1652_);
v___x_1583_ = v_impl_1566_;
v_isShared_1584_ = v_isSharedCheck_1647_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v_impl_1566_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1647_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_size_1585_; lean_object* v_size_1586_; lean_object* v_k_1587_; lean_object* v_v_1588_; lean_object* v_l_1589_; lean_object* v_r_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_size_1585_ = lean_ctor_get(v_l_1572_, 0);
v_size_1586_ = lean_ctor_get(v_r_1573_, 0);
v_k_1587_ = lean_ctor_get(v_r_1573_, 1);
v_v_1588_ = lean_ctor_get(v_r_1573_, 2);
v_l_1589_ = lean_ctor_get(v_r_1573_, 3);
v_r_1590_ = lean_ctor_get(v_r_1573_, 4);
v___x_1591_ = lean_unsigned_to_nat(2u);
v___x_1592_ = lean_nat_mul(v___x_1591_, v_size_1585_);
v___x_1593_ = lean_nat_dec_lt(v_size_1586_, v___x_1592_);
lean_dec(v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1622_; 
lean_inc(v_r_1590_);
lean_inc(v_l_1589_);
lean_inc(v_v_1588_);
lean_inc(v_k_1587_);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_r_1573_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; lean_object* v_unused_1626_; lean_object* v_unused_1627_; 
v_unused_1623_ = lean_ctor_get(v_r_1573_, 4);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_r_1573_, 3);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_r_1573_, 2);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_r_1573_, 1);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_r_1573_, 0);
lean_dec(v_unused_1627_);
v___x_1595_ = v_r_1573_;
v_isShared_1596_ = v_isSharedCheck_1622_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_r_1573_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1622_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___x_1610_; lean_object* v___y_1612_; 
v___x_1597_ = lean_nat_add(v___x_1567_, v_size_1569_);
lean_dec(v_size_1569_);
v___x_1598_ = lean_nat_add(v___x_1597_, v_size_1568_);
lean_dec(v___x_1597_);
v___x_1610_ = lean_nat_add(v___x_1567_, v_size_1585_);
if (lean_obj_tag(v_l_1589_) == 0)
{
lean_object* v_size_1620_; 
v_size_1620_ = lean_ctor_get(v_l_1589_, 0);
lean_inc(v_size_1620_);
v___y_1612_ = v_size_1620_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___y_1612_ = v___x_1621_;
goto v___jp_1611_;
}
v___jp_1599_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_nat_add(v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec(v___y_1601_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 4, v_r_1422_);
lean_ctor_set(v___x_1595_, 3, v_r_1590_);
lean_ctor_set(v___x_1595_, 2, v_v_1420_);
lean_ctor_set(v___x_1595_, 1, v_k_1419_);
lean_ctor_set(v___x_1595_, 0, v___x_1603_);
v___x_1605_ = v___x_1595_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_r_1590_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_r_1422_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v___x_1605_);
lean_ctor_set(v___x_1583_, 3, v___y_1600_);
lean_ctor_set(v___x_1583_, 2, v_v_1588_);
lean_ctor_set(v___x_1583_, 1, v_k_1587_);
lean_ctor_set(v___x_1583_, 0, v___x_1598_);
v___x_1607_ = v___x_1583_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v___y_1600_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
v___jp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_nat_add(v___x_1610_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec(v___x_1610_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_l_1589_);
lean_ctor_set(v___x_1424_, 3, v_l_1572_);
lean_ctor_set(v___x_1424_, 2, v_v_1571_);
lean_ctor_set(v___x_1424_, 1, v_k_1570_);
lean_ctor_set(v___x_1424_, 0, v___x_1613_);
v___x_1615_ = v___x_1424_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_k_1570_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_v_1571_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_l_1572_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_l_1589_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_nat_add(v___x_1567_, v_size_1568_);
if (lean_obj_tag(v_r_1590_) == 0)
{
lean_object* v_size_1617_; 
v_size_1617_ = lean_ctor_get(v_r_1590_, 0);
lean_inc(v_size_1617_);
v___y_1600_ = v___x_1615_;
v___y_1601_ = v___x_1616_;
v___y_1602_ = v_size_1617_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v___y_1600_ = v___x_1615_;
v___y_1601_ = v___x_1616_;
v___y_1602_ = v___x_1618_;
goto v___jp_1599_;
}
}
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_del_object(v___x_1424_);
v___x_1628_ = lean_nat_add(v___x_1567_, v_size_1569_);
lean_dec(v_size_1569_);
v___x_1629_ = lean_nat_add(v___x_1628_, v_size_1568_);
lean_dec(v___x_1628_);
v___x_1630_ = lean_nat_add(v___x_1567_, v_size_1568_);
v___x_1631_ = lean_nat_add(v___x_1630_, v_size_1586_);
lean_dec(v___x_1630_);
lean_inc_ref(v_r_1422_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_r_1422_);
lean_ctor_set(v___x_1583_, 3, v_r_1573_);
lean_ctor_set(v___x_1583_, 2, v_v_1420_);
lean_ctor_set(v___x_1583_, 1, v_k_1419_);
lean_ctor_set(v___x_1583_, 0, v___x_1631_);
v___x_1633_ = v___x_1583_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_r_1573_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_r_1422_);
v___x_1633_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_isSharedCheck_1640_ = !lean_is_exclusive(v_r_1422_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1641_ = lean_ctor_get(v_r_1422_, 4);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_r_1422_, 3);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_r_1422_, 2);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_r_1422_, 1);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_r_1422_, 0);
lean_dec(v_unused_1645_);
v___x_1635_ = v_r_1422_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v_r_1422_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 4, v___x_1633_);
lean_ctor_set(v___x_1635_, 3, v_l_1572_);
lean_ctor_set(v___x_1635_, 2, v_v_1571_);
lean_ctor_set(v___x_1635_, 1, v_k_1570_);
lean_ctor_set(v___x_1635_, 0, v___x_1629_);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1570_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1571_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_l_1572_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v___x_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1653_; 
v_l_1653_ = lean_ctor_get(v_impl_1566_, 3);
lean_inc(v_l_1653_);
if (lean_obj_tag(v_l_1653_) == 0)
{
lean_object* v_r_1654_; lean_object* v_k_1655_; lean_object* v_v_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1667_; 
v_r_1654_ = lean_ctor_get(v_impl_1566_, 4);
v_k_1655_ = lean_ctor_get(v_impl_1566_, 1);
v_v_1656_ = lean_ctor_get(v_impl_1566_, 2);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_impl_1566_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; lean_object* v_unused_1669_; 
v_unused_1668_ = lean_ctor_get(v_impl_1566_, 3);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_impl_1566_, 0);
lean_dec(v_unused_1669_);
v___x_1658_ = v_impl_1566_;
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_r_1654_);
lean_inc(v_v_1656_);
lean_inc(v_k_1655_);
lean_dec(v_impl_1566_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1667_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1654_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 3, v_r_1654_);
lean_ctor_set(v___x_1658_, 2, v_v_1420_);
lean_ctor_set(v___x_1658_, 1, v_k_1419_);
lean_ctor_set(v___x_1658_, 0, v___x_1567_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v_r_1654_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v_r_1654_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v___x_1662_);
lean_ctor_set(v___x_1424_, 3, v_l_1653_);
lean_ctor_set(v___x_1424_, 2, v_v_1656_);
lean_ctor_set(v___x_1424_, 1, v_k_1655_);
lean_ctor_set(v___x_1424_, 0, v___x_1660_);
v___x_1664_ = v___x_1424_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1655_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_l_1653_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_r_1670_; 
v_r_1670_ = lean_ctor_get(v_impl_1566_, 4);
lean_inc(v_r_1670_);
if (lean_obj_tag(v_r_1670_) == 0)
{
lean_object* v_k_1671_; lean_object* v_v_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1695_; 
v_k_1671_ = lean_ctor_get(v_impl_1566_, 1);
v_v_1672_ = lean_ctor_get(v_impl_1566_, 2);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_impl_1566_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; 
v_unused_1696_ = lean_ctor_get(v_impl_1566_, 4);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_impl_1566_, 3);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_impl_1566_, 0);
lean_dec(v_unused_1698_);
v___x_1674_ = v_impl_1566_;
v_isShared_1675_ = v_isSharedCheck_1695_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_v_1672_);
lean_inc(v_k_1671_);
lean_dec(v_impl_1566_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1695_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v_k_1676_; lean_object* v_v_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1691_; 
v_k_1676_ = lean_ctor_get(v_r_1670_, 1);
v_v_1677_ = lean_ctor_get(v_r_1670_, 2);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_r_1670_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; 
v_unused_1692_ = lean_ctor_get(v_r_1670_, 4);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_r_1670_, 3);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_r_1670_, 0);
lean_dec(v_unused_1694_);
v___x_1679_ = v_r_1670_;
v_isShared_1680_ = v_isSharedCheck_1691_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_v_1677_);
lean_inc(v_k_1676_);
lean_dec(v_r_1670_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1691_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_unsigned_to_nat(3u);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 4, v_l_1653_);
lean_ctor_set(v___x_1679_, 3, v_l_1653_);
lean_ctor_set(v___x_1679_, 2, v_v_1672_);
lean_ctor_set(v___x_1679_, 1, v_k_1671_);
lean_ctor_set(v___x_1679_, 0, v___x_1567_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_k_1671_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_v_1672_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_l_1653_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_l_1653_);
v___x_1683_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v_l_1653_);
lean_ctor_set(v___x_1674_, 2, v_v_1420_);
lean_ctor_set(v___x_1674_, 1, v_k_1419_);
lean_ctor_set(v___x_1674_, 0, v___x_1567_);
v___x_1685_ = v___x_1674_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_l_1653_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_l_1653_);
v___x_1685_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v___x_1685_);
lean_ctor_set(v___x_1424_, 3, v___x_1683_);
lean_ctor_set(v___x_1424_, 2, v_v_1677_);
lean_ctor_set(v___x_1424_, 1, v_k_1676_);
lean_ctor_set(v___x_1424_, 0, v___x_1681_);
v___x_1687_ = v___x_1424_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_k_1676_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_v_1677_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = lean_unsigned_to_nat(2u);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 4, v_r_1670_);
lean_ctor_set(v___x_1424_, 3, v_impl_1566_);
lean_ctor_set(v___x_1424_, 0, v___x_1699_);
v___x_1701_ = v___x_1424_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_k_1419_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_v_1420_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_impl_1566_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v_r_1670_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_unsigned_to_nat(1u);
v___x_1705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_k_1415_);
lean_ctor_set(v___x_1705_, 2, v_v_1416_);
lean_ctor_set(v___x_1705_, 3, v_t_1417_);
lean_ctor_set(v___x_1705_, 4, v_t_1417_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object* v_k_1706_, lean_object* v_x_1707_){
_start:
{
if (lean_obj_tag(v_x_1707_) == 0)
{
lean_object* v___x_1708_; 
lean_dec_ref(v_k_1706_);
v___x_1708_ = lean_box(0);
return v___x_1708_;
}
else
{
lean_object* v_val_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_val_1709_ = lean_ctor_get(v_x_1707_, 0);
lean_inc(v_val_1709_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_k_1706_);
lean_ctor_set(v___x_1710_, 1, v_val_1709_);
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object* v_k_1713_, lean_object* v_x_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v_k_1713_, v_x_1714_);
lean_dec(v_x_1714_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t v_sz_1716_, size_t v_i_1717_, lean_object* v_bs_1718_){
_start:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_usize_dec_lt(v_i_1717_, v_sz_1716_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_bs_1718_);
return v___x_1720_;
}
else
{
lean_object* v_v_1721_; lean_object* v___x_1722_; 
v_v_1721_ = lean_array_uget_borrowed(v_bs_1718_, v_i_1717_);
lean_inc(v_v_1721_);
v___x_1722_ = l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(v_v_1721_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v_bs_1718_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1732_; lean_object* v_bs_x27_1733_; size_t v___x_1734_; size_t v___x_1735_; lean_object* v___x_1736_; 
v_a_1731_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1722_);
v___x_1732_ = lean_unsigned_to_nat(0u);
v_bs_x27_1733_ = lean_array_uset(v_bs_1718_, v_i_1717_, v___x_1732_);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_add(v_i_1717_, v___x_1734_);
v___x_1736_ = lean_array_uset(v_bs_x27_1733_, v_i_1717_, v_a_1731_);
v_i_1717_ = v___x_1735_;
v_bs_1718_ = v___x_1736_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1738_, lean_object* v_i_1739_, lean_object* v_bs_1740_){
_start:
{
size_t v_sz_boxed_1741_; size_t v_i_boxed_1742_; lean_object* v_res_1743_; 
v_sz_boxed_1741_ = lean_unbox_usize(v_sz_1738_);
lean_dec(v_sz_1738_);
v_i_boxed_1742_ = lean_unbox_usize(v_i_1739_);
lean_dec(v_i_1739_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_boxed_1741_, v_i_boxed_1742_, v_bs_1740_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object* v_x_1744_){
_start:
{
if (lean_obj_tag(v_x_1744_) == 4)
{
lean_object* v_elems_1745_; size_t v_sz_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v_elems_1745_ = lean_ctor_get(v_x_1744_, 0);
lean_inc_ref(v_elems_1745_);
lean_dec_ref(v_x_1744_);
v_sz_1746_ = lean_array_size(v_elems_1745_);
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_1746_, v___x_1747_, v_elems_1745_);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1749_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1750_ = lean_unsigned_to_nat(80u);
v___x_1751_ = l_Lean_Json_pretty(v_x_1744_, v___x_1750_);
v___x_1752_ = lean_string_append(v___x_1749_, v___x_1751_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1754_ = lean_string_append(v___x_1752_, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 0)
{
lean_object* v___x_1759_; 
v___x_1759_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0));
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(v_x_1758_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1777_; 
v_a_1769_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1771_ = v___x_1760_;
v_isShared_1772_ = v_isSharedCheck_1777_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1760_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1777_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_a_1769_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1773_);
v___x_1775_ = v___x_1771_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object* v_expectedID_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Lsp_Ipc_stdout(v_a_1779_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1925_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1925_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1925_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_IO_FS_Stream_readLspMessage(v_a_1782_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1916_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1916_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1916_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___y_1792_; lean_object* v___y_1793_; 
switch(lean_obj_tag(v_a_1787_))
{
case 2:
{
lean_object* v_id_1799_; lean_object* v_result_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1844_; 
v_id_1799_ = lean_ctor_get(v_a_1787_, 0);
v_result_1800_ = lean_ctor_get(v_a_1787_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_a_1787_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1802_ = v_a_1787_;
v_isShared_1803_ = v_isSharedCheck_1844_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_result_1800_);
lean_inc(v_id_1799_);
lean_dec(v_a_1787_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1844_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
uint8_t v___x_1804_; 
v___x_1804_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_1799_, v_expectedID_1778_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___y_1807_; 
lean_del_object(v___x_1802_);
lean_dec(v_result_1800_);
lean_del_object(v___x_1784_);
v___x_1805_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_1778_))
{
case 0:
{
lean_object* v_s_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_s_1818_ = lean_ctor_get(v_expectedID_1778_, 0);
lean_inc_ref(v_s_1818_);
lean_dec_ref(v_expectedID_1778_);
v___x_1819_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1820_ = lean_string_append(v___x_1819_, v_s_1818_);
lean_dec_ref(v_s_1818_);
v___x_1821_ = lean_string_append(v___x_1820_, v___x_1819_);
v___y_1807_ = v___x_1821_;
goto v___jp_1806_;
}
case 1:
{
lean_object* v_n_1822_; lean_object* v___x_1823_; 
v_n_1822_ = lean_ctor_get(v_expectedID_1778_, 0);
lean_inc_ref(v_n_1822_);
lean_dec_ref(v_expectedID_1778_);
v___x_1823_ = l_Lean_JsonNumber_toString(v_n_1822_);
v___y_1807_ = v___x_1823_;
goto v___jp_1806_;
}
default: 
{
lean_object* v___x_1824_; 
v___x_1824_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1807_ = v___x_1824_;
goto v___jp_1806_;
}
}
v___jp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_string_append(v___x_1805_, v___y_1807_);
lean_dec_ref(v___y_1807_);
v___x_1809_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_1810_ = lean_string_append(v___x_1808_, v___x_1809_);
switch(lean_obj_tag(v_id_1799_))
{
case 0:
{
lean_object* v_s_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_s_1811_ = lean_ctor_get(v_id_1799_, 0);
lean_inc_ref(v_s_1811_);
lean_dec_ref(v_id_1799_);
v___x_1812_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1813_ = lean_string_append(v___x_1812_, v_s_1811_);
lean_dec_ref(v_s_1811_);
v___x_1814_ = lean_string_append(v___x_1813_, v___x_1812_);
v___y_1792_ = v___x_1810_;
v___y_1793_ = v___x_1814_;
goto v___jp_1791_;
}
case 1:
{
lean_object* v_n_1815_; lean_object* v___x_1816_; 
v_n_1815_ = lean_ctor_get(v_id_1799_, 0);
lean_inc_ref(v_n_1815_);
lean_dec_ref(v_id_1799_);
v___x_1816_ = l_Lean_JsonNumber_toString(v_n_1815_);
v___y_1792_ = v___x_1810_;
v___y_1793_ = v___x_1816_;
goto v___jp_1791_;
}
default: 
{
lean_object* v___x_1817_; 
v___x_1817_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1792_ = v___x_1810_;
v___y_1793_ = v___x_1817_;
goto v___jp_1791_;
}
}
}
}
else
{
lean_object* v___x_1825_; 
lean_dec(v_id_1799_);
lean_del_object(v___x_1789_);
lean_inc(v_result_1800_);
v___x_1825_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(v_result_1800_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_del_object(v___x_1802_);
lean_dec(v_expectedID_1778_);
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_1828_ = l_Lean_Json_compress(v_result_1800_);
v___x_1829_ = lean_string_append(v___x_1827_, v___x_1828_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_1831_ = lean_string_append(v___x_1829_, v___x_1830_);
v___x_1832_ = lean_string_append(v___x_1831_, v_a_1826_);
lean_dec(v_a_1826_);
v___x_1833_ = lean_mk_io_user_error(v___x_1832_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 1);
lean_ctor_set(v___x_1784_, 0, v___x_1833_);
v___x_1835_ = v___x_1784_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; 
lean_dec(v_result_1800_);
v_a_1837_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1825_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 0);
lean_ctor_set(v___x_1802_, 1, v_a_1837_);
lean_ctor_set(v___x_1802_, 0, v_expectedID_1778_);
v___x_1839_ = v___x_1802_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_expectedID_1778_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_a_1837_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1839_);
v___x_1841_ = v___x_1784_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_1845_; uint8_t v_code_1846_; lean_object* v_message_1847_; lean_object* v_data_x3f_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___x_1880_; lean_object* v___y_1882_; 
lean_del_object(v___x_1789_);
lean_dec(v_expectedID_1778_);
v_id_1845_ = lean_ctor_get(v_a_1787_, 0);
lean_inc(v_id_1845_);
v_code_1846_ = lean_ctor_get_uint8(v_a_1787_, sizeof(void*)*3);
v_message_1847_ = lean_ctor_get(v_a_1787_, 1);
lean_inc_ref(v_message_1847_);
v_data_x3f_1848_ = lean_ctor_get(v_a_1787_, 2);
lean_inc(v_data_x3f_1848_);
lean_dec_ref(v_a_1787_);
v___x_1849_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_1850_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_1880_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_1845_))
{
case 0:
{
lean_object* v_s_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_s_1898_ = lean_ctor_get(v_id_1845_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_id_1845_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v_id_1845_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_s_1898_);
lean_dec(v_id_1845_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 3);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_s_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
v___y_1882_ = v___x_1903_;
goto v___jp_1881_;
}
}
}
case 1:
{
lean_object* v_n_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_n_1906_ = lean_ctor_get(v_id_1845_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_id_1845_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v_id_1845_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_n_1906_);
lean_dec(v_id_1845_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 2);
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_n_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
v___y_1882_ = v___x_1911_;
goto v___jp_1881_;
}
}
}
default: 
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_box(0);
v___y_1882_ = v___x_1914_;
goto v___jp_1881_;
}
}
v___jp_1851_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1852_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___y_1852_);
lean_ctor_set(v___x_1856_, 1, v___y_1855_);
v___x_1857_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_1858_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_message_1847_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1856_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_1864_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_1863_, v_data_x3f_1848_);
lean_dec(v_data_x3f_1848_);
v___x_1865_ = l_List_appendTR___redArg(v___x_1862_, v___x_1864_);
v___x_1866_ = l_Lean_Json_mkObj(v___x_1865_);
lean_dec(v___x_1865_);
lean_inc_ref(v___y_1853_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___y_1853_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___x_1860_);
v___x_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___y_1854_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1850_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_Json_mkObj(v___x_1870_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = l_Lean_Json_compress(v___x_1871_);
v___x_1873_ = lean_string_append(v___x_1849_, v___x_1872_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1875_ = lean_string_append(v___x_1873_, v___x_1874_);
v___x_1876_ = lean_mk_io_user_error(v___x_1875_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 1);
lean_ctor_set(v___x_1784_, 0, v___x_1876_);
v___x_1878_ = v___x_1784_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
v___jp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1880_);
lean_ctor_set(v___x_1883_, 1, v___y_1882_);
v___x_1884_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_1885_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_1846_)
{
case 0:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1886_;
goto v___jp_1851_;
}
case 1:
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1887_;
goto v___jp_1851_;
}
case 2:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1888_;
goto v___jp_1851_;
}
case 3:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1889_;
goto v___jp_1851_;
}
case 4:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1890_;
goto v___jp_1851_;
}
case 5:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1891_;
goto v___jp_1851_;
}
case 6:
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1892_;
goto v___jp_1851_;
}
case 7:
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1893_;
goto v___jp_1851_;
}
case 8:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1894_;
goto v___jp_1851_;
}
case 9:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1895_;
goto v___jp_1851_;
}
case 10:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1896_;
goto v___jp_1851_;
}
default: 
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_1852_ = v___x_1885_;
v___y_1853_ = v___x_1884_;
v___y_1854_ = v___x_1883_;
v___y_1855_ = v___x_1897_;
goto v___jp_1851_;
}
}
}
}
default: 
{
lean_del_object(v___x_1789_);
lean_dec(v_a_1787_);
lean_del_object(v___x_1784_);
goto _start;
}
}
v___jp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1794_ = lean_string_append(v___y_1792_, v___y_1793_);
lean_dec_ref(v___y_1793_);
v___x_1795_ = lean_mk_io_user_error(v___x_1794_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 1);
lean_ctor_set(v___x_1789_, 0, v___x_1795_);
v___x_1797_ = v___x_1789_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_del_object(v___x_1784_);
lean_dec(v_expectedID_1778_);
v_a_1917_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1786_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1786_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec(v_expectedID_1778_);
v_a_1926_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1781_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1781_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object* v_expectedID_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v_expectedID_1934_, v_a_1935_);
lean_dec_ref(v_a_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object* v_v_1938_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(v_v_1938_);
v___x_1940_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object* v_h_1941_, lean_object* v_r_1942_){
_start:
{
lean_object* v_id_1944_; lean_object* v_method_1945_; lean_object* v_param_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1966_; 
v_id_1944_ = lean_ctor_get(v_r_1942_, 0);
v_method_1945_ = lean_ctor_get(v_r_1942_, 1);
v_param_1946_ = lean_ctor_get(v_r_1942_, 2);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1948_ = v_r_1942_;
v_isShared_1949_ = v_isSharedCheck_1966_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_param_1946_);
lean_inc(v_method_1945_);
lean_inc(v_id_1944_);
lean_dec(v_r_1942_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1966_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___y_1951_; lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(v_param_1946_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; 
lean_dec_ref(v___x_1956_);
v___x_1957_ = lean_box(0);
v___y_1951_ = v___x_1957_;
goto v___jp_1950_;
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_a_1958_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1956_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
v___y_1951_ = v___x_1963_;
goto v___jp_1950_;
}
}
}
v___jp_1950_:
{
lean_object* v___x_1953_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 2, v___y_1951_);
v___x_1953_ = v___x_1948_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_id_1944_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_method_1945_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v___y_1951_);
v___x_1953_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_IO_FS_Stream_writeLspMessage(v_h_1941_, v___x_1953_);
return v___x_1954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object* v_h_1967_, lean_object* v_r_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_h_1967_, v_r_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object* v_r_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1974_; lean_object* v_a_1975_; lean_object* v___x_1976_; 
v___x_1974_ = l_Lean_Lsp_Ipc_stdin(v_a_1972_);
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref(v___x_1974_);
v___x_1976_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_a_1975_, v_r_1971_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object* v_r_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v_r_1977_, v_a_1978_);
lean_dec_ref(v_a_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object* v_k_1981_, lean_object* v_t_1982_){
_start:
{
if (lean_obj_tag(v_t_1982_) == 0)
{
lean_object* v_k_1983_; lean_object* v_l_1984_; lean_object* v_r_1985_; uint8_t v___x_1986_; 
v_k_1983_ = lean_ctor_get(v_t_1982_, 1);
v_l_1984_ = lean_ctor_get(v_t_1982_, 3);
v_r_1985_ = lean_ctor_get(v_t_1982_, 4);
v___x_1986_ = lean_string_dec_lt(v_k_1981_, v_k_1983_);
if (v___x_1986_ == 0)
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_string_dec_eq(v_k_1981_, v_k_1983_);
if (v___x_1987_ == 0)
{
v_t_1982_ = v_r_1985_;
goto _start;
}
else
{
return v___x_1987_;
}
}
else
{
v_t_1982_ = v_l_1984_;
goto _start;
}
}
else
{
uint8_t v___x_1990_; 
v___x_1990_ = 0;
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object* v_k_1991_, lean_object* v_t_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_1991_, v_t_1992_);
lean_dec(v_t_1992_);
lean_dec_ref(v_k_1991_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object* v_requestNo_2002_, lean_object* v_item_2003_, lean_object* v_fromRanges_2004_, lean_object* v_visited_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_name_2008_; uint8_t v___x_2009_; 
v_name_2008_ = lean_ctor_get(v_item_2003_, 0);
v___x_2009_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2008_, v_visited_2005_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_inc(v_requestNo_2002_);
v___x_2010_ = l_Lean_JsonNumber_fromNat(v_requestNo_2002_);
v___x_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
v___x_2012_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_2003_);
lean_inc_ref(v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
lean_ctor_set(v___x_2013_, 2, v_item_2003_);
v___x_2014_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v___x_2013_, v_a_2006_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref(v___x_2014_);
v___x_2015_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v___x_2011_, v_a_2006_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2053_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_box(0);
lean_inc_ref(v_name_2008_);
v___x_2060_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2008_, v___x_2059_, v_visited_2005_);
v___y_2053_ = v___x_2060_;
goto v___jp_2052_;
}
else
{
v___y_2053_ = v_visited_2005_;
goto v___jp_2052_;
}
v___jp_2017_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; size_t v_sz_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2021_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___y_2019_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v_sz_2023_ = lean_array_size(v___y_2020_);
v___x_2024_ = ((size_t)0ULL);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___y_2018_, v___y_2020_, v_sz_2023_, v___x_2024_, v___x_2022_, v_a_2006_);
lean_dec_ref(v___y_2020_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2043_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2043_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2043_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2042_; 
v_fst_2030_ = lean_ctor_get(v_a_2026_, 0);
v_snd_2031_ = lean_ctor_get(v_a_2026_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_2026_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2033_ = v_a_2026_;
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_snd_2031_);
lean_inc(v_fst_2030_);
lean_dec(v_a_2026_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2035_, 0, v_item_2003_);
lean_ctor_set(v___x_2035_, 1, v_fromRanges_2004_);
lean_ctor_set(v___x_2035_, 2, v_snd_2031_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v_fst_2030_);
lean_ctor_set(v___x_2033_, 0, v___x_2035_);
v___x_2037_ = v___x_2033_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_fst_2030_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2037_);
v___x_2039_ = v___x_2028_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
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
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref(v_fromRanges_2004_);
lean_dec_ref(v_item_2003_);
v_a_2044_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2025_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2025_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
v___jp_2052_:
{
lean_object* v_result_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_result_2054_ = lean_ctor_get(v_a_2016_, 1);
lean_inc(v_result_2054_);
lean_dec(v_a_2016_);
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_add(v_requestNo_2002_, v___x_2055_);
lean_dec(v_requestNo_2002_);
if (lean_obj_tag(v_result_2054_) == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2));
v___y_2018_ = v___y_2053_;
v___y_2019_ = v___x_2056_;
v___y_2020_ = v___x_2057_;
goto v___jp_2017_;
}
else
{
lean_object* v_val_2058_; 
v_val_2058_ = lean_ctor_get(v_result_2054_, 0);
lean_inc(v_val_2058_);
lean_dec_ref(v_result_2054_);
v___y_2018_ = v___y_2053_;
v___y_2019_ = v___x_2056_;
v___y_2020_ = v_val_2058_;
goto v___jp_2017_;
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_visited_2005_);
lean_dec_ref(v_fromRanges_2004_);
lean_dec_ref(v_item_2003_);
lean_dec(v_requestNo_2002_);
v_a_2061_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2015_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2015_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v___x_2011_);
lean_dec(v_visited_2005_);
lean_dec_ref(v_fromRanges_2004_);
lean_dec_ref(v_item_2003_);
lean_dec(v_requestNo_2002_);
v_a_2069_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2014_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2014_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec(v_visited_2005_);
lean_dec_ref(v_fromRanges_2004_);
v___x_2077_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2078_, 0, v_item_2003_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
lean_ctor_set(v___x_2078_, 2, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_requestNo_2002_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object* v___x_2081_, lean_object* v_as_2082_, size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_usize_dec_lt(v_i_2084_, v_sz_2083_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v___x_2081_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_b_2085_);
return v___x_2089_;
}
else
{
lean_object* v_fst_2090_; lean_object* v_snd_2091_; lean_object* v_a_2092_; lean_object* v_from_2093_; lean_object* v_fromRanges_2094_; lean_object* v___x_2095_; 
v_fst_2090_ = lean_ctor_get(v_b_2085_, 0);
lean_inc(v_fst_2090_);
v_snd_2091_ = lean_ctor_get(v_b_2085_, 1);
lean_inc(v_snd_2091_);
lean_dec_ref(v_b_2085_);
v_a_2092_ = lean_array_uget_borrowed(v_as_2082_, v_i_2084_);
v_from_2093_ = lean_ctor_get(v_a_2092_, 0);
v_fromRanges_2094_ = lean_ctor_get(v_a_2092_, 1);
lean_inc(v___x_2081_);
lean_inc_ref(v_fromRanges_2094_);
lean_inc_ref(v_from_2093_);
v___x_2095_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2090_, v_from_2093_, v_fromRanges_2094_, v___x_2081_, v___y_2086_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v_fst_2097_; lean_object* v_snd_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2109_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref(v___x_2095_);
v_fst_2097_ = lean_ctor_get(v_a_2096_, 0);
v_snd_2098_ = lean_ctor_get(v_a_2096_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_a_2096_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2100_ = v_a_2096_;
v_isShared_2101_ = v_isSharedCheck_2109_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_snd_2098_);
lean_inc(v_fst_2097_);
lean_dec(v_a_2096_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2109_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2102_ = lean_array_push(v_snd_2091_, v_fst_2097_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 1, v___x_2102_);
lean_ctor_set(v___x_2100_, 0, v_snd_2098_);
v___x_2104_ = v___x_2100_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_snd_2098_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
size_t v___x_2105_; size_t v___x_2106_; 
v___x_2105_ = ((size_t)1ULL);
v___x_2106_ = lean_usize_add(v_i_2084_, v___x_2105_);
v_i_2084_ = v___x_2106_;
v_b_2085_ = v___x_2104_;
goto _start;
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v_snd_2091_);
lean_dec(v___x_2081_);
v_a_2110_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2095_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2095_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3___boxed(lean_object* v___x_2118_, lean_object* v_as_2119_, lean_object* v_sz_2120_, lean_object* v_i_2121_, lean_object* v_b_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
size_t v_sz_boxed_2125_; size_t v_i_boxed_2126_; lean_object* v_res_2127_; 
v_sz_boxed_2125_ = lean_unbox_usize(v_sz_2120_);
lean_dec(v_sz_2120_);
v_i_boxed_2126_ = lean_unbox_usize(v_i_2121_);
lean_dec(v_i_2121_);
v_res_2127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___x_2118_, v_as_2119_, v_sz_boxed_2125_, v_i_boxed_2126_, v_b_2122_, v___y_2123_);
lean_dec_ref(v___y_2123_);
lean_dec_ref(v_as_2119_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___boxed(lean_object* v_requestNo_2128_, lean_object* v_item_2129_, lean_object* v_fromRanges_2130_, lean_object* v_visited_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_requestNo_2128_, v_item_2129_, v_fromRanges_2130_, v_visited_2131_, v_a_2132_);
lean_dec_ref(v_a_2132_);
return v_res_2134_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object* v_00_u03b2_2135_, lean_object* v_k_2136_, lean_object* v_t_2137_){
_start:
{
uint8_t v___x_2138_; 
v___x_2138_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_2136_, v_t_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object* v_00_u03b2_2139_, lean_object* v_k_2140_, lean_object* v_t_2141_){
_start:
{
uint8_t v_res_2142_; lean_object* v_r_2143_; 
v_res_2142_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(v_00_u03b2_2139_, v_k_2140_, v_t_2141_);
lean_dec(v_t_2141_);
lean_dec_ref(v_k_2140_);
v_r_2143_ = lean_box(v_res_2142_);
return v_r_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object* v_00_u03b2_2144_, lean_object* v_k_2145_, lean_object* v_v_2146_, lean_object* v_t_2147_, lean_object* v_hl_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_2145_, v_v_2146_, v_t_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2150_, size_t v_i_2151_, lean_object* v_bs_2152_){
_start:
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_usize_dec_lt(v_i_2151_, v_sz_2150_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_bs_2152_);
return v___x_2154_;
}
else
{
lean_object* v_v_2155_; lean_object* v___x_2156_; 
v_v_2155_ = lean_array_uget_borrowed(v_bs_2152_, v_i_2151_);
lean_inc(v_v_2155_);
v___x_2156_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v_v_2155_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v_bs_2152_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v_bs_x27_2167_; size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v_a_2165_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2156_);
v___x_2166_ = lean_unsigned_to_nat(0u);
v_bs_x27_2167_ = lean_array_uset(v_bs_2152_, v_i_2151_, v___x_2166_);
v___x_2168_ = ((size_t)1ULL);
v___x_2169_ = lean_usize_add(v_i_2151_, v___x_2168_);
v___x_2170_ = lean_array_uset(v_bs_x27_2167_, v_i_2151_, v_a_2165_);
v_i_2151_ = v___x_2169_;
v_bs_2152_ = v___x_2170_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2172_, lean_object* v_i_2173_, lean_object* v_bs_2174_){
_start:
{
size_t v_sz_boxed_2175_; size_t v_i_boxed_2176_; lean_object* v_res_2177_; 
v_sz_boxed_2175_ = lean_unbox_usize(v_sz_2172_);
lean_dec(v_sz_2172_);
v_i_boxed_2176_ = lean_unbox_usize(v_i_2173_);
lean_dec(v_i_2173_);
v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2175_, v_i_boxed_2176_, v_bs_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object* v_x_2178_){
_start:
{
if (lean_obj_tag(v_x_2178_) == 4)
{
lean_object* v_elems_2179_; size_t v_sz_2180_; size_t v___x_2181_; lean_object* v___x_2182_; 
v_elems_2179_ = lean_ctor_get(v_x_2178_, 0);
lean_inc_ref(v_elems_2179_);
lean_dec_ref(v_x_2178_);
v_sz_2180_ = lean_array_size(v_elems_2179_);
v___x_2181_ = ((size_t)0ULL);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_2180_, v___x_2181_, v_elems_2179_);
return v___x_2182_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2183_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2184_ = lean_unsigned_to_nat(80u);
v___x_2185_ = l_Lean_Json_pretty(v_x_2178_, v___x_2184_);
v___x_2186_ = lean_string_append(v___x_2183_, v___x_2185_);
lean_dec_ref(v___x_2185_);
v___x_2187_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2188_ = lean_string_append(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object* v_x_2192_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
lean_object* v___x_2193_; 
v___x_2193_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0));
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(v_x_2192_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2211_; 
v_a_2203_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2205_ = v___x_2194_;
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2194_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2211_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2207_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object* v_expectedID_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_Lsp_Ipc_stdout(v_a_2213_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2359_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2359_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2359_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_IO_FS_Stream_readLspMessage(v_a_2216_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2350_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2350_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2350_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___y_2226_; lean_object* v___y_2227_; 
switch(lean_obj_tag(v_a_2221_))
{
case 2:
{
lean_object* v_id_2233_; lean_object* v_result_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2278_; 
v_id_2233_ = lean_ctor_get(v_a_2221_, 0);
v_result_2234_ = lean_ctor_get(v_a_2221_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_a_2221_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2236_ = v_a_2221_;
v_isShared_2237_ = v_isSharedCheck_2278_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_result_2234_);
lean_inc(v_id_2233_);
lean_dec(v_a_2221_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2278_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
uint8_t v___x_2238_; 
v___x_2238_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2233_, v_expectedID_2212_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___y_2241_; 
lean_del_object(v___x_2236_);
lean_dec(v_result_2234_);
lean_del_object(v___x_2218_);
v___x_2239_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2212_))
{
case 0:
{
lean_object* v_s_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_s_2252_ = lean_ctor_get(v_expectedID_2212_, 0);
lean_inc_ref(v_s_2252_);
lean_dec_ref(v_expectedID_2212_);
v___x_2253_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2254_ = lean_string_append(v___x_2253_, v_s_2252_);
lean_dec_ref(v_s_2252_);
v___x_2255_ = lean_string_append(v___x_2254_, v___x_2253_);
v___y_2241_ = v___x_2255_;
goto v___jp_2240_;
}
case 1:
{
lean_object* v_n_2256_; lean_object* v___x_2257_; 
v_n_2256_ = lean_ctor_get(v_expectedID_2212_, 0);
lean_inc_ref(v_n_2256_);
lean_dec_ref(v_expectedID_2212_);
v___x_2257_ = l_Lean_JsonNumber_toString(v_n_2256_);
v___y_2241_ = v___x_2257_;
goto v___jp_2240_;
}
default: 
{
lean_object* v___x_2258_; 
v___x_2258_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2241_ = v___x_2258_;
goto v___jp_2240_;
}
}
v___jp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_string_append(v___x_2239_, v___y_2241_);
lean_dec_ref(v___y_2241_);
v___x_2243_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2244_ = lean_string_append(v___x_2242_, v___x_2243_);
switch(lean_obj_tag(v_id_2233_))
{
case 0:
{
lean_object* v_s_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v_s_2245_ = lean_ctor_get(v_id_2233_, 0);
lean_inc_ref(v_s_2245_);
lean_dec_ref(v_id_2233_);
v___x_2246_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2247_ = lean_string_append(v___x_2246_, v_s_2245_);
lean_dec_ref(v_s_2245_);
v___x_2248_ = lean_string_append(v___x_2247_, v___x_2246_);
v___y_2226_ = v___x_2244_;
v___y_2227_ = v___x_2248_;
goto v___jp_2225_;
}
case 1:
{
lean_object* v_n_2249_; lean_object* v___x_2250_; 
v_n_2249_ = lean_ctor_get(v_id_2233_, 0);
lean_inc_ref(v_n_2249_);
lean_dec_ref(v_id_2233_);
v___x_2250_ = l_Lean_JsonNumber_toString(v_n_2249_);
v___y_2226_ = v___x_2244_;
v___y_2227_ = v___x_2250_;
goto v___jp_2225_;
}
default: 
{
lean_object* v___x_2251_; 
v___x_2251_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2226_ = v___x_2244_;
v___y_2227_ = v___x_2251_;
goto v___jp_2225_;
}
}
}
}
else
{
lean_object* v___x_2259_; 
lean_dec(v_id_2233_);
lean_del_object(v___x_2223_);
lean_inc(v_result_2234_);
v___x_2259_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(v_result_2234_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
lean_del_object(v___x_2236_);
lean_dec(v_expectedID_2212_);
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2259_);
v___x_2261_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2262_ = l_Lean_Json_compress(v_result_2234_);
v___x_2263_ = lean_string_append(v___x_2261_, v___x_2262_);
lean_dec_ref(v___x_2262_);
v___x_2264_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2265_ = lean_string_append(v___x_2263_, v___x_2264_);
v___x_2266_ = lean_string_append(v___x_2265_, v_a_2260_);
lean_dec(v_a_2260_);
v___x_2267_ = lean_mk_io_user_error(v___x_2266_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 1);
lean_ctor_set(v___x_2218_, 0, v___x_2267_);
v___x_2269_ = v___x_2218_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; 
lean_dec(v_result_2234_);
v_a_2271_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2271_);
lean_dec_ref(v___x_2259_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 0);
lean_ctor_set(v___x_2236_, 1, v_a_2271_);
lean_ctor_set(v___x_2236_, 0, v_expectedID_2212_);
v___x_2273_ = v___x_2236_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_expectedID_2212_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_a_2271_);
v___x_2273_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2275_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2273_);
v___x_2275_ = v___x_2218_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2279_; uint8_t v_code_2280_; lean_object* v_message_2281_; lean_object* v_data_x3f_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___x_2314_; lean_object* v___y_2316_; 
lean_del_object(v___x_2223_);
lean_dec(v_expectedID_2212_);
v_id_2279_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_id_2279_);
v_code_2280_ = lean_ctor_get_uint8(v_a_2221_, sizeof(void*)*3);
v_message_2281_ = lean_ctor_get(v_a_2221_, 1);
lean_inc_ref(v_message_2281_);
v_data_x3f_2282_ = lean_ctor_get(v_a_2221_, 2);
lean_inc(v_data_x3f_2282_);
lean_dec_ref(v_a_2221_);
v___x_2283_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2284_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2314_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2279_))
{
case 0:
{
lean_object* v_s_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_s_2332_ = lean_ctor_get(v_id_2279_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_id_2279_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v_id_2279_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_s_2332_);
lean_dec(v_id_2279_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set_tag(v___x_2334_, 3);
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_s_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
v___y_2316_ = v___x_2337_;
goto v___jp_2315_;
}
}
}
case 1:
{
lean_object* v_n_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_n_2340_ = lean_ctor_get(v_id_2279_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_id_2279_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v_id_2279_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_n_2340_);
lean_dec(v_id_2279_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set_tag(v___x_2342_, 2);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_n_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
v___y_2316_ = v___x_2345_;
goto v___jp_2315_;
}
}
}
default: 
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_box(0);
v___y_2316_ = v___x_2348_;
goto v___jp_2315_;
}
}
v___jp_2285_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
lean_inc(v___y_2289_);
lean_inc_ref(v___y_2287_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___y_2287_);
lean_ctor_set(v___x_2290_, 1, v___y_2289_);
v___x_2291_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_message_2281_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2290_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2298_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2297_, v_data_x3f_2282_);
lean_dec(v_data_x3f_2282_);
v___x_2299_ = l_List_appendTR___redArg(v___x_2296_, v___x_2298_);
v___x_2300_ = l_Lean_Json_mkObj(v___x_2299_);
lean_dec(v___x_2299_);
lean_inc_ref(v___y_2288_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___y_2288_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v___x_2294_);
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___y_2286_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2284_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = l_Lean_Json_mkObj(v___x_2304_);
lean_dec_ref(v___x_2304_);
v___x_2306_ = l_Lean_Json_compress(v___x_2305_);
v___x_2307_ = lean_string_append(v___x_2283_, v___x_2306_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2309_ = lean_string_append(v___x_2307_, v___x_2308_);
v___x_2310_ = lean_mk_io_user_error(v___x_2309_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 1);
lean_ctor_set(v___x_2218_, 0, v___x_2310_);
v___x_2312_ = v___x_2218_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
v___jp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___y_2316_);
v___x_2318_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2319_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2280_)
{
case 0:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2320_;
goto v___jp_2285_;
}
case 1:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2321_;
goto v___jp_2285_;
}
case 2:
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2322_;
goto v___jp_2285_;
}
case 3:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2323_;
goto v___jp_2285_;
}
case 4:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2324_;
goto v___jp_2285_;
}
case 5:
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2325_;
goto v___jp_2285_;
}
case 6:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2326_;
goto v___jp_2285_;
}
case 7:
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2327_;
goto v___jp_2285_;
}
case 8:
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2328_;
goto v___jp_2285_;
}
case 9:
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2329_;
goto v___jp_2285_;
}
case 10:
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2330_;
goto v___jp_2285_;
}
default: 
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2286_ = v___x_2317_;
v___y_2287_ = v___x_2319_;
v___y_2288_ = v___x_2318_;
v___y_2289_ = v___x_2331_;
goto v___jp_2285_;
}
}
}
}
default: 
{
lean_del_object(v___x_2223_);
lean_dec(v_a_2221_);
lean_del_object(v___x_2218_);
goto _start;
}
}
v___jp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2228_ = lean_string_append(v___y_2226_, v___y_2227_);
lean_dec_ref(v___y_2227_);
v___x_2229_ = lean_mk_io_user_error(v___x_2228_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2229_);
v___x_2231_ = v___x_2223_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_del_object(v___x_2218_);
lean_dec(v_expectedID_2212_);
v_a_2351_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2220_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2220_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_expectedID_2212_);
v_a_2360_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2215_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2215_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object* v_expectedID_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v_expectedID_2368_, v_a_2369_);
lean_dec_ref(v_a_2369_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object* v_as_2372_, size_t v_sz_2373_, size_t v_i_2374_, lean_object* v_b_2375_, lean_object* v___y_2376_){
_start:
{
uint8_t v___x_2378_; 
v___x_2378_ = lean_usize_dec_lt(v_i_2374_, v_sz_2373_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v_b_2375_);
return v___x_2379_;
}
else
{
lean_object* v_fst_2380_; lean_object* v_snd_2381_; lean_object* v_a_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_fst_2380_ = lean_ctor_get(v_b_2375_, 0);
lean_inc(v_fst_2380_);
v_snd_2381_ = lean_ctor_get(v_b_2375_, 1);
lean_inc(v_snd_2381_);
lean_dec_ref(v_b_2375_);
v_a_2382_ = lean_array_uget_borrowed(v_as_2372_, v_i_2374_);
v___x_2383_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2384_ = lean_box(1);
lean_inc(v_a_2382_);
v___x_2385_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2380_, v_a_2382_, v___x_2383_, v___x_2384_, v___y_2376_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v_fst_2387_; lean_object* v_snd_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2399_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref(v___x_2385_);
v_fst_2387_ = lean_ctor_get(v_a_2386_, 0);
v_snd_2388_ = lean_ctor_get(v_a_2386_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_a_2386_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2390_ = v_a_2386_;
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_snd_2388_);
lean_inc(v_fst_2387_);
lean_dec(v_a_2386_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_array_push(v_snd_2381_, v_fst_2387_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v___x_2392_);
lean_ctor_set(v___x_2390_, 0, v_snd_2388_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_snd_2388_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
size_t v___x_2395_; size_t v___x_2396_; 
v___x_2395_ = ((size_t)1ULL);
v___x_2396_ = lean_usize_add(v_i_2374_, v___x_2395_);
v_i_2374_ = v___x_2396_;
v_b_2375_ = v___x_2394_;
goto _start;
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_snd_2381_);
v_a_2400_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2385_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2385_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object* v_as_2408_, lean_object* v_sz_2409_, lean_object* v_i_2410_, lean_object* v_b_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
size_t v_sz_boxed_2414_; size_t v_i_boxed_2415_; lean_object* v_res_2416_; 
v_sz_boxed_2414_ = lean_unbox_usize(v_sz_2409_);
lean_dec(v_sz_2409_);
v_i_boxed_2415_ = lean_unbox_usize(v_i_2410_);
lean_dec(v_i_2410_);
v_res_2416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v_as_2408_, v_sz_boxed_2414_, v_i_boxed_2415_, v_b_2411_, v___y_2412_);
lean_dec_ref(v___y_2412_);
lean_dec_ref(v_as_2408_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object* v_v_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(v_v_2417_);
v___x_2419_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object* v_h_2420_, lean_object* v_r_2421_){
_start:
{
lean_object* v_id_2423_; lean_object* v_method_2424_; lean_object* v_param_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2445_; 
v_id_2423_ = lean_ctor_get(v_r_2421_, 0);
v_method_2424_ = lean_ctor_get(v_r_2421_, 1);
v_param_2425_ = lean_ctor_get(v_r_2421_, 2);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_r_2421_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2427_ = v_r_2421_;
v_isShared_2428_ = v_isSharedCheck_2445_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_param_2425_);
lean_inc(v_method_2424_);
lean_inc(v_id_2423_);
lean_dec(v_r_2421_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2445_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___y_2430_; lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(v_param_2425_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v___x_2436_; 
lean_dec_ref(v___x_2435_);
v___x_2436_ = lean_box(0);
v___y_2430_ = v___x_2436_;
goto v___jp_2429_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
v_a_2437_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
v___y_2430_ = v___x_2442_;
goto v___jp_2429_;
}
}
}
v___jp_2429_:
{
lean_object* v___x_2432_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 2, v___y_2430_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_id_2423_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_method_2424_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v___y_2430_);
v___x_2432_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_IO_FS_Stream_writeLspMessage(v_h_2420_, v___x_2432_);
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object* v_h_2446_, lean_object* v_r_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_h_2446_, v_r_2447_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object* v_r_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v___x_2453_; lean_object* v_a_2454_; lean_object* v___x_2455_; 
v___x_2453_ = l_Lean_Lsp_Ipc_stdin(v_a_2451_);
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref(v___x_2453_);
v___x_2455_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_a_2454_, v_r_2450_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object* v_r_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v_r_2456_, v_a_2457_);
lean_dec_ref(v_a_2457_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object* v_requestNo_2463_, lean_object* v_uri_2464_, lean_object* v_pos_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_inc(v_requestNo_2463_);
v___x_2468_ = l_Lean_JsonNumber_fromNat(v_requestNo_2463_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
v___x_2470_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v_uri_2464_);
lean_ctor_set(v___x_2471_, 1, v_pos_2465_);
lean_inc_ref(v___x_2469_);
v___x_2472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2469_);
lean_ctor_set(v___x_2472_, 1, v___x_2470_);
lean_ctor_set(v___x_2472_, 2, v___x_2471_);
v___x_2473_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2472_, v_a_2466_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref(v___x_2473_);
v___x_2474_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2469_, v_a_2466_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v_result_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2518_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref(v___x_2474_);
v_result_2476_ = lean_ctor_get(v_a_2475_, 1);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_a_2475_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v_a_2475_, 0);
lean_dec(v_unused_2519_);
v___x_2478_ = v_a_2475_;
v_isShared_2479_ = v_isSharedCheck_2518_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_result_2476_);
lean_dec(v_a_2475_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2518_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___y_2483_; 
v___x_2480_ = lean_unsigned_to_nat(1u);
v___x_2481_ = lean_nat_add(v_requestNo_2463_, v___x_2480_);
lean_dec(v_requestNo_2463_);
if (lean_obj_tag(v_result_2476_) == 0)
{
lean_object* v___x_2516_; 
v___x_2516_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2483_ = v___x_2516_;
goto v___jp_2482_;
}
else
{
lean_object* v_val_2517_; 
v_val_2517_ = lean_ctor_get(v_result_2476_, 0);
lean_inc(v_val_2517_);
lean_dec_ref(v_result_2476_);
v___y_2483_ = v_val_2517_;
goto v___jp_2482_;
}
v___jp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 1, v___x_2484_);
lean_ctor_set(v___x_2478_, 0, v___x_2481_);
v___x_2486_ = v___x_2478_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
size_t v_sz_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v_sz_2487_ = lean_array_size(v___y_2483_);
v___x_2488_ = ((size_t)0ULL);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v___y_2483_, v_sz_2487_, v___x_2488_, v___x_2486_, v_a_2466_);
lean_dec_ref(v___y_2483_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2506_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2506_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2506_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v_fst_2494_; lean_object* v_snd_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2505_; 
v_fst_2494_ = lean_ctor_get(v_a_2490_, 0);
v_snd_2495_ = lean_ctor_get(v_a_2490_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2490_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2497_ = v_a_2490_;
v_isShared_2498_ = v_isSharedCheck_2505_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_snd_2495_);
lean_inc(v_fst_2494_);
lean_dec(v_a_2490_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2505_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v_fst_2494_);
lean_ctor_set(v___x_2497_, 0, v_snd_2495_);
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_snd_2495_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_fst_2494_);
v___x_2500_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2502_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2500_);
v___x_2502_ = v___x_2492_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
v_a_2507_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2489_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2489_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_requestNo_2463_);
v_a_2520_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2474_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2474_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v___x_2469_);
lean_dec(v_requestNo_2463_);
v_a_2528_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2473_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2473_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object* v_requestNo_2536_, lean_object* v_uri_2537_, lean_object* v_pos_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(v_requestNo_2536_, v_uri_2537_, v_pos_2538_, v_a_2539_);
lean_dec_ref(v_a_2539_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2542_, size_t v_i_2543_, lean_object* v_bs_2544_){
_start:
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_usize_dec_lt(v_i_2543_, v_sz_2542_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_bs_2544_);
return v___x_2546_;
}
else
{
lean_object* v_v_2547_; lean_object* v___x_2548_; 
v_v_2547_ = lean_array_uget_borrowed(v_bs_2544_, v_i_2543_);
lean_inc(v_v_2547_);
v___x_2548_ = l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(v_v_2547_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v_bs_2544_);
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2558_; lean_object* v_bs_x27_2559_; size_t v___x_2560_; size_t v___x_2561_; lean_object* v___x_2562_; 
v_a_2557_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2557_);
lean_dec_ref(v___x_2548_);
v___x_2558_ = lean_unsigned_to_nat(0u);
v_bs_x27_2559_ = lean_array_uset(v_bs_2544_, v_i_2543_, v___x_2558_);
v___x_2560_ = ((size_t)1ULL);
v___x_2561_ = lean_usize_add(v_i_2543_, v___x_2560_);
v___x_2562_ = lean_array_uset(v_bs_x27_2559_, v_i_2543_, v_a_2557_);
v_i_2543_ = v___x_2561_;
v_bs_2544_ = v___x_2562_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2564_, lean_object* v_i_2565_, lean_object* v_bs_2566_){
_start:
{
size_t v_sz_boxed_2567_; size_t v_i_boxed_2568_; lean_object* v_res_2569_; 
v_sz_boxed_2567_ = lean_unbox_usize(v_sz_2564_);
lean_dec(v_sz_2564_);
v_i_boxed_2568_ = lean_unbox_usize(v_i_2565_);
lean_dec(v_i_2565_);
v_res_2569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2567_, v_i_boxed_2568_, v_bs_2566_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object* v_x_2570_){
_start:
{
if (lean_obj_tag(v_x_2570_) == 4)
{
lean_object* v_elems_2571_; size_t v_sz_2572_; size_t v___x_2573_; lean_object* v___x_2574_; 
v_elems_2571_ = lean_ctor_get(v_x_2570_, 0);
lean_inc_ref(v_elems_2571_);
lean_dec_ref(v_x_2570_);
v_sz_2572_ = lean_array_size(v_elems_2571_);
v___x_2573_ = ((size_t)0ULL);
v___x_2574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_2572_, v___x_2573_, v_elems_2571_);
return v___x_2574_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2575_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2576_ = lean_unsigned_to_nat(80u);
v___x_2577_ = l_Lean_Json_pretty(v_x_2570_, v___x_2576_);
v___x_2578_ = lean_string_append(v___x_2575_, v___x_2577_);
lean_dec_ref(v___x_2577_);
v___x_2579_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2580_ = lean_string_append(v___x_2578_, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
return v___x_2581_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object* v_x_2584_){
_start:
{
if (lean_obj_tag(v_x_2584_) == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0));
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(v_x_2584_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2603_; 
v_a_2595_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2597_ = v___x_2586_;
v_isShared_2598_ = v_isSharedCheck_2603_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2586_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2603_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_a_2595_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2599_);
v___x_2601_ = v___x_2597_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object* v_expectedID_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Lsp_Ipc_stdout(v_a_2605_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2751_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2751_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2751_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; 
v___x_2612_ = l_IO_FS_Stream_readLspMessage(v_a_2608_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2742_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2742_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2742_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___y_2618_; lean_object* v___y_2619_; 
switch(lean_obj_tag(v_a_2613_))
{
case 2:
{
lean_object* v_id_2625_; lean_object* v_result_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2670_; 
v_id_2625_ = lean_ctor_get(v_a_2613_, 0);
v_result_2626_ = lean_ctor_get(v_a_2613_, 1);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_a_2613_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2628_ = v_a_2613_;
v_isShared_2629_ = v_isSharedCheck_2670_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_result_2626_);
lean_inc(v_id_2625_);
lean_dec(v_a_2613_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2670_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
uint8_t v___x_2630_; 
v___x_2630_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2625_, v_expectedID_2604_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___y_2633_; 
lean_del_object(v___x_2628_);
lean_dec(v_result_2626_);
lean_del_object(v___x_2610_);
v___x_2631_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2604_))
{
case 0:
{
lean_object* v_s_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_s_2644_ = lean_ctor_get(v_expectedID_2604_, 0);
lean_inc_ref(v_s_2644_);
lean_dec_ref(v_expectedID_2604_);
v___x_2645_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2646_ = lean_string_append(v___x_2645_, v_s_2644_);
lean_dec_ref(v_s_2644_);
v___x_2647_ = lean_string_append(v___x_2646_, v___x_2645_);
v___y_2633_ = v___x_2647_;
goto v___jp_2632_;
}
case 1:
{
lean_object* v_n_2648_; lean_object* v___x_2649_; 
v_n_2648_ = lean_ctor_get(v_expectedID_2604_, 0);
lean_inc_ref(v_n_2648_);
lean_dec_ref(v_expectedID_2604_);
v___x_2649_ = l_Lean_JsonNumber_toString(v_n_2648_);
v___y_2633_ = v___x_2649_;
goto v___jp_2632_;
}
default: 
{
lean_object* v___x_2650_; 
v___x_2650_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2633_ = v___x_2650_;
goto v___jp_2632_;
}
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_string_append(v___x_2631_, v___y_2633_);
lean_dec_ref(v___y_2633_);
v___x_2635_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2636_ = lean_string_append(v___x_2634_, v___x_2635_);
switch(lean_obj_tag(v_id_2625_))
{
case 0:
{
lean_object* v_s_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_s_2637_ = lean_ctor_get(v_id_2625_, 0);
lean_inc_ref(v_s_2637_);
lean_dec_ref(v_id_2625_);
v___x_2638_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2639_ = lean_string_append(v___x_2638_, v_s_2637_);
lean_dec_ref(v_s_2637_);
v___x_2640_ = lean_string_append(v___x_2639_, v___x_2638_);
v___y_2618_ = v___x_2636_;
v___y_2619_ = v___x_2640_;
goto v___jp_2617_;
}
case 1:
{
lean_object* v_n_2641_; lean_object* v___x_2642_; 
v_n_2641_ = lean_ctor_get(v_id_2625_, 0);
lean_inc_ref(v_n_2641_);
lean_dec_ref(v_id_2625_);
v___x_2642_ = l_Lean_JsonNumber_toString(v_n_2641_);
v___y_2618_ = v___x_2636_;
v___y_2619_ = v___x_2642_;
goto v___jp_2617_;
}
default: 
{
lean_object* v___x_2643_; 
v___x_2643_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2618_ = v___x_2636_;
v___y_2619_ = v___x_2643_;
goto v___jp_2617_;
}
}
}
}
else
{
lean_object* v___x_2651_; 
lean_dec(v_id_2625_);
lean_del_object(v___x_2615_);
lean_inc(v_result_2626_);
v___x_2651_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(v_result_2626_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
lean_del_object(v___x_2628_);
lean_dec(v_expectedID_2604_);
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2651_);
v___x_2653_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2654_ = l_Lean_Json_compress(v_result_2626_);
v___x_2655_ = lean_string_append(v___x_2653_, v___x_2654_);
lean_dec_ref(v___x_2654_);
v___x_2656_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2657_ = lean_string_append(v___x_2655_, v___x_2656_);
v___x_2658_ = lean_string_append(v___x_2657_, v_a_2652_);
lean_dec(v_a_2652_);
v___x_2659_ = lean_mk_io_user_error(v___x_2658_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set_tag(v___x_2610_, 1);
lean_ctor_set(v___x_2610_, 0, v___x_2659_);
v___x_2661_ = v___x_2610_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; 
lean_dec(v_result_2626_);
v_a_2663_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2663_);
lean_dec_ref(v___x_2651_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 0);
lean_ctor_set(v___x_2628_, 1, v_a_2663_);
lean_ctor_set(v___x_2628_, 0, v_expectedID_2604_);
v___x_2665_ = v___x_2628_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_expectedID_2604_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_a_2663_);
v___x_2665_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2665_);
v___x_2667_ = v___x_2610_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2671_; uint8_t v_code_2672_; lean_object* v_message_2673_; lean_object* v_data_x3f_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___x_2706_; lean_object* v___y_2708_; 
lean_del_object(v___x_2615_);
lean_dec(v_expectedID_2604_);
v_id_2671_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_id_2671_);
v_code_2672_ = lean_ctor_get_uint8(v_a_2613_, sizeof(void*)*3);
v_message_2673_ = lean_ctor_get(v_a_2613_, 1);
lean_inc_ref(v_message_2673_);
v_data_x3f_2674_ = lean_ctor_get(v_a_2613_, 2);
lean_inc(v_data_x3f_2674_);
lean_dec_ref(v_a_2613_);
v___x_2675_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2676_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2706_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2671_))
{
case 0:
{
lean_object* v_s_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_s_2724_ = lean_ctor_get(v_id_2671_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_id_2671_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v_id_2671_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_s_2724_);
lean_dec(v_id_2671_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set_tag(v___x_2726_, 3);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_s_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
v___y_2708_ = v___x_2729_;
goto v___jp_2707_;
}
}
}
case 1:
{
lean_object* v_n_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
v_n_2732_ = lean_ctor_get(v_id_2671_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_id_2671_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v_id_2671_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_n_2732_);
lean_dec(v_id_2671_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set_tag(v___x_2734_, 2);
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_n_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
v___y_2708_ = v___x_2737_;
goto v___jp_2707_;
}
}
}
default: 
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_box(0);
v___y_2708_ = v___x_2740_;
goto v___jp_2707_;
}
}
v___jp_2677_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
lean_inc(v___y_2681_);
lean_inc_ref(v___y_2679_);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___y_2679_);
lean_ctor_set(v___x_2682_, 1, v___y_2681_);
v___x_2683_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2684_, 0, v_message_2673_);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_box(0);
v___x_2687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2682_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2690_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2689_, v_data_x3f_2674_);
lean_dec(v_data_x3f_2674_);
v___x_2691_ = l_List_appendTR___redArg(v___x_2688_, v___x_2690_);
v___x_2692_ = l_Lean_Json_mkObj(v___x_2691_);
lean_dec(v___x_2691_);
lean_inc_ref(v___y_2680_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___y_2680_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v___x_2686_);
v___x_2695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___y_2678_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2676_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_Json_mkObj(v___x_2696_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = l_Lean_Json_compress(v___x_2697_);
v___x_2699_ = lean_string_append(v___x_2675_, v___x_2698_);
lean_dec_ref(v___x_2698_);
v___x_2700_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2701_ = lean_string_append(v___x_2699_, v___x_2700_);
v___x_2702_ = lean_mk_io_user_error(v___x_2701_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set_tag(v___x_2610_, 1);
lean_ctor_set(v___x_2610_, 0, v___x_2702_);
v___x_2704_ = v___x_2610_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
v___jp_2707_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2706_);
lean_ctor_set(v___x_2709_, 1, v___y_2708_);
v___x_2710_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2711_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2672_)
{
case 0:
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2712_;
goto v___jp_2677_;
}
case 1:
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2713_;
goto v___jp_2677_;
}
case 2:
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2714_;
goto v___jp_2677_;
}
case 3:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2715_;
goto v___jp_2677_;
}
case 4:
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2716_;
goto v___jp_2677_;
}
case 5:
{
lean_object* v___x_2717_; 
v___x_2717_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2717_;
goto v___jp_2677_;
}
case 6:
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2718_;
goto v___jp_2677_;
}
case 7:
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2719_;
goto v___jp_2677_;
}
case 8:
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2720_;
goto v___jp_2677_;
}
case 9:
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2721_;
goto v___jp_2677_;
}
case 10:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2722_;
goto v___jp_2677_;
}
default: 
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2678_ = v___x_2709_;
v___y_2679_ = v___x_2711_;
v___y_2680_ = v___x_2710_;
v___y_2681_ = v___x_2723_;
goto v___jp_2677_;
}
}
}
}
default: 
{
lean_del_object(v___x_2615_);
lean_dec(v_a_2613_);
lean_del_object(v___x_2610_);
goto _start;
}
}
v___jp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2620_ = lean_string_append(v___y_2618_, v___y_2619_);
lean_dec_ref(v___y_2619_);
v___x_2621_ = lean_mk_io_user_error(v___x_2620_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set_tag(v___x_2615_, 1);
lean_ctor_set(v___x_2615_, 0, v___x_2621_);
v___x_2623_ = v___x_2615_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_del_object(v___x_2610_);
lean_dec(v_expectedID_2604_);
v_a_2743_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2612_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2612_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_expectedID_2604_);
v_a_2752_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2607_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2607_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object* v_expectedID_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v_expectedID_2760_, v_a_2761_);
lean_dec_ref(v_a_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object* v_v_2764_){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(v_v_2764_);
v___x_2766_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object* v_h_2767_, lean_object* v_r_2768_){
_start:
{
lean_object* v_id_2770_; lean_object* v_method_2771_; lean_object* v_param_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2792_; 
v_id_2770_ = lean_ctor_get(v_r_2768_, 0);
v_method_2771_ = lean_ctor_get(v_r_2768_, 1);
v_param_2772_ = lean_ctor_get(v_r_2768_, 2);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_r_2768_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2774_ = v_r_2768_;
v_isShared_2775_ = v_isSharedCheck_2792_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_param_2772_);
lean_inc(v_method_2771_);
lean_inc(v_id_2770_);
lean_dec(v_r_2768_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2792_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___y_2777_; lean_object* v___x_2782_; 
v___x_2782_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(v_param_2772_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v___x_2783_; 
lean_dec_ref(v___x_2782_);
v___x_2783_ = lean_box(0);
v___y_2777_ = v___x_2783_;
goto v___jp_2776_;
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v_a_2784_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2782_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2782_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
v___y_2777_ = v___x_2789_;
goto v___jp_2776_;
}
}
}
v___jp_2776_:
{
lean_object* v___x_2779_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 2, v___y_2777_);
v___x_2779_ = v___x_2774_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_id_2770_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_method_2771_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v___y_2777_);
v___x_2779_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_IO_FS_Stream_writeLspMessage(v_h_2767_, v___x_2779_);
return v___x_2780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object* v_h_2793_, lean_object* v_r_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_h_2793_, v_r_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object* v_r_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2800_; lean_object* v_a_2801_; lean_object* v___x_2802_; 
v___x_2800_ = l_Lean_Lsp_Ipc_stdin(v_a_2798_);
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref(v___x_2800_);
v___x_2802_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_a_2801_, v_r_2797_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object* v_r_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v_r_2803_, v_a_2804_);
lean_dec_ref(v_a_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object* v_requestNo_2810_, lean_object* v_item_2811_, lean_object* v_fromRanges_2812_, lean_object* v_visited_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v_name_2816_; uint8_t v___x_2817_; 
v_name_2816_ = lean_ctor_get(v_item_2811_, 0);
v___x_2817_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2816_, v_visited_2813_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_inc(v_requestNo_2810_);
v___x_2818_ = l_Lean_JsonNumber_fromNat(v_requestNo_2810_);
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
v___x_2820_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_2811_);
lean_inc_ref(v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
lean_ctor_set(v___x_2821_, 2, v_item_2811_);
v___x_2822_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v___x_2821_, v_a_2814_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v___x_2823_; 
lean_dec_ref(v___x_2822_);
v___x_2823_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v___x_2819_, v_a_2814_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2861_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref(v___x_2823_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_box(0);
lean_inc_ref(v_name_2816_);
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2816_, v___x_2867_, v_visited_2813_);
v___y_2861_ = v___x_2868_;
goto v___jp_2860_;
}
else
{
v___y_2861_ = v_visited_2813_;
goto v___jp_2860_;
}
v___jp_2825_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; size_t v_sz_2831_; size_t v___x_2832_; lean_object* v___x_2833_; 
v___x_2829_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___y_2827_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
v_sz_2831_ = lean_array_size(v___y_2828_);
v___x_2832_ = ((size_t)0ULL);
v___x_2833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___y_2826_, v___y_2828_, v_sz_2831_, v___x_2832_, v___x_2830_, v_a_2814_);
lean_dec_ref(v___y_2828_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2851_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2851_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2851_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2850_; 
v_fst_2838_ = lean_ctor_get(v_a_2834_, 0);
v_snd_2839_ = lean_ctor_get(v_a_2834_, 1);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_a_2834_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2841_ = v_a_2834_;
v_isShared_2842_ = v_isSharedCheck_2850_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_snd_2839_);
lean_inc(v_fst_2838_);
lean_dec(v_a_2834_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2850_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2843_, 0, v_item_2811_);
lean_ctor_set(v___x_2843_, 1, v_fromRanges_2812_);
lean_ctor_set(v___x_2843_, 2, v_snd_2839_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 1, v_fst_2838_);
lean_ctor_set(v___x_2841_, 0, v___x_2843_);
v___x_2845_ = v___x_2841_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_fst_2838_);
v___x_2845_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2845_);
v___x_2847_ = v___x_2836_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v_fromRanges_2812_);
lean_dec_ref(v_item_2811_);
v_a_2852_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2833_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2833_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
v___jp_2860_:
{
lean_object* v_result_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_result_2862_ = lean_ctor_get(v_a_2824_, 1);
lean_inc(v_result_2862_);
lean_dec(v_a_2824_);
v___x_2863_ = lean_unsigned_to_nat(1u);
v___x_2864_ = lean_nat_add(v_requestNo_2810_, v___x_2863_);
lean_dec(v_requestNo_2810_);
if (lean_obj_tag(v_result_2862_) == 0)
{
lean_object* v___x_2865_; 
v___x_2865_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1));
v___y_2826_ = v___y_2861_;
v___y_2827_ = v___x_2864_;
v___y_2828_ = v___x_2865_;
goto v___jp_2825_;
}
else
{
lean_object* v_val_2866_; 
v_val_2866_ = lean_ctor_get(v_result_2862_, 0);
lean_inc(v_val_2866_);
lean_dec_ref(v_result_2862_);
v___y_2826_ = v___y_2861_;
v___y_2827_ = v___x_2864_;
v___y_2828_ = v_val_2866_;
goto v___jp_2825_;
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v_visited_2813_);
lean_dec_ref(v_fromRanges_2812_);
lean_dec_ref(v_item_2811_);
lean_dec(v_requestNo_2810_);
v_a_2869_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2823_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2823_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref(v___x_2819_);
lean_dec(v_visited_2813_);
lean_dec_ref(v_fromRanges_2812_);
lean_dec_ref(v_item_2811_);
lean_dec(v_requestNo_2810_);
v_a_2877_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2822_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2822_);
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
else
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v_visited_2813_);
lean_dec_ref(v_fromRanges_2812_);
v___x_2885_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2886_, 0, v_item_2811_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
lean_ctor_set(v___x_2886_, 2, v___x_2885_);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v_requestNo_2810_);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object* v___x_2889_, lean_object* v_as_2890_, size_t v_sz_2891_, size_t v_i_2892_, lean_object* v_b_2893_, lean_object* v___y_2894_){
_start:
{
uint8_t v___x_2896_; 
v___x_2896_ = lean_usize_dec_lt(v_i_2892_, v_sz_2891_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; 
lean_dec(v___x_2889_);
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_b_2893_);
return v___x_2897_;
}
else
{
lean_object* v_fst_2898_; lean_object* v_snd_2899_; lean_object* v_a_2900_; lean_object* v_to_2901_; lean_object* v_fromRanges_2902_; lean_object* v___x_2903_; 
v_fst_2898_ = lean_ctor_get(v_b_2893_, 0);
lean_inc(v_fst_2898_);
v_snd_2899_ = lean_ctor_get(v_b_2893_, 1);
lean_inc(v_snd_2899_);
lean_dec_ref(v_b_2893_);
v_a_2900_ = lean_array_uget_borrowed(v_as_2890_, v_i_2892_);
v_to_2901_ = lean_ctor_get(v_a_2900_, 0);
v_fromRanges_2902_ = lean_ctor_get(v_a_2900_, 1);
lean_inc(v___x_2889_);
lean_inc_ref(v_fromRanges_2902_);
lean_inc_ref(v_to_2901_);
v___x_2903_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2898_, v_to_2901_, v_fromRanges_2902_, v___x_2889_, v___y_2894_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v_fst_2905_; lean_object* v_snd_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2917_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref(v___x_2903_);
v_fst_2905_ = lean_ctor_get(v_a_2904_, 0);
v_snd_2906_ = lean_ctor_get(v_a_2904_, 1);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_a_2904_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2908_ = v_a_2904_;
v_isShared_2909_ = v_isSharedCheck_2917_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_snd_2906_);
lean_inc(v_fst_2905_);
lean_dec(v_a_2904_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2917_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = lean_array_push(v_snd_2899_, v_fst_2905_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 1, v___x_2910_);
lean_ctor_set(v___x_2908_, 0, v_snd_2906_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_snd_2906_);
lean_ctor_set(v_reuseFailAlloc_2916_, 1, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
size_t v___x_2913_; size_t v___x_2914_; 
v___x_2913_ = ((size_t)1ULL);
v___x_2914_ = lean_usize_add(v_i_2892_, v___x_2913_);
v_i_2892_ = v___x_2914_;
v_b_2893_ = v___x_2912_;
goto _start;
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_snd_2899_);
lean_dec(v___x_2889_);
v_a_2918_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2903_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2903_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object* v___x_2926_, lean_object* v_as_2927_, lean_object* v_sz_2928_, lean_object* v_i_2929_, lean_object* v_b_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
size_t v_sz_boxed_2933_; size_t v_i_boxed_2934_; lean_object* v_res_2935_; 
v_sz_boxed_2933_ = lean_unbox_usize(v_sz_2928_);
lean_dec(v_sz_2928_);
v_i_boxed_2934_ = lean_unbox_usize(v_i_2929_);
lean_dec(v_i_2929_);
v_res_2935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2926_, v_as_2927_, v_sz_boxed_2933_, v_i_boxed_2934_, v_b_2930_, v___y_2931_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v_as_2927_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object* v_requestNo_2936_, lean_object* v_item_2937_, lean_object* v_fromRanges_2938_, lean_object* v_visited_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_requestNo_2936_, v_item_2937_, v_fromRanges_2938_, v_visited_2939_, v_a_2940_);
lean_dec_ref(v_a_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object* v_as_2943_, size_t v_sz_2944_, size_t v_i_2945_, lean_object* v_b_2946_, lean_object* v___y_2947_){
_start:
{
uint8_t v___x_2949_; 
v___x_2949_ = lean_usize_dec_lt(v_i_2945_, v_sz_2944_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_b_2946_);
return v___x_2950_;
}
else
{
lean_object* v_fst_2951_; lean_object* v_snd_2952_; lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_fst_2951_ = lean_ctor_get(v_b_2946_, 0);
lean_inc(v_fst_2951_);
v_snd_2952_ = lean_ctor_get(v_b_2946_, 1);
lean_inc(v_snd_2952_);
lean_dec_ref(v_b_2946_);
v_a_2953_ = lean_array_uget_borrowed(v_as_2943_, v_i_2945_);
v___x_2954_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2955_ = lean_box(1);
lean_inc(v_a_2953_);
v___x_2956_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2951_, v_a_2953_, v___x_2954_, v___x_2955_, v___y_2947_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_fst_2958_; lean_object* v_snd_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2970_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v___x_2956_);
v_fst_2958_ = lean_ctor_get(v_a_2957_, 0);
v_snd_2959_ = lean_ctor_get(v_a_2957_, 1);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2961_ = v_a_2957_;
v_isShared_2962_ = v_isSharedCheck_2970_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_snd_2959_);
lean_inc(v_fst_2958_);
lean_dec(v_a_2957_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2970_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2963_ = lean_array_push(v_snd_2952_, v_fst_2958_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_2963_);
lean_ctor_set(v___x_2961_, 0, v_snd_2959_);
v___x_2965_ = v___x_2961_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_snd_2959_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
size_t v___x_2966_; size_t v___x_2967_; 
v___x_2966_ = ((size_t)1ULL);
v___x_2967_ = lean_usize_add(v_i_2945_, v___x_2966_);
v_i_2945_ = v___x_2967_;
v_b_2946_ = v___x_2965_;
goto _start;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_snd_2952_);
v_a_2971_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2956_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2956_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object* v_as_2979_, lean_object* v_sz_2980_, lean_object* v_i_2981_, lean_object* v_b_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
size_t v_sz_boxed_2985_; size_t v_i_boxed_2986_; lean_object* v_res_2987_; 
v_sz_boxed_2985_ = lean_unbox_usize(v_sz_2980_);
lean_dec(v_sz_2980_);
v_i_boxed_2986_ = lean_unbox_usize(v_i_2981_);
lean_dec(v_i_2981_);
v_res_2987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v_as_2979_, v_sz_boxed_2985_, v_i_boxed_2986_, v_b_2982_, v___y_2983_);
lean_dec_ref(v___y_2983_);
lean_dec_ref(v_as_2979_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object* v_requestNo_2988_, lean_object* v_uri_2989_, lean_object* v_pos_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_inc(v_requestNo_2988_);
v___x_2993_ = l_Lean_JsonNumber_fromNat(v_requestNo_2988_);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
v___x_2995_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v_uri_2989_);
lean_ctor_set(v___x_2996_, 1, v_pos_2990_);
lean_inc_ref(v___x_2994_);
v___x_2997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2994_);
lean_ctor_set(v___x_2997_, 1, v___x_2995_);
lean_ctor_set(v___x_2997_, 2, v___x_2996_);
v___x_2998_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2997_, v_a_2991_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v___x_2999_; 
lean_dec_ref(v___x_2998_);
v___x_2999_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2994_, v_a_2991_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v_result_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3043_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref(v___x_2999_);
v_result_3001_ = lean_ctor_get(v_a_3000_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_a_3000_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; 
v_unused_3044_ = lean_ctor_get(v_a_3000_, 0);
lean_dec(v_unused_3044_);
v___x_3003_ = v_a_3000_;
v_isShared_3004_ = v_isSharedCheck_3043_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_result_3001_);
lean_dec(v_a_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3043_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___y_3008_; 
v___x_3005_ = lean_unsigned_to_nat(1u);
v___x_3006_ = lean_nat_add(v_requestNo_2988_, v___x_3005_);
lean_dec(v_requestNo_2988_);
if (lean_obj_tag(v_result_3001_) == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_3008_ = v___x_3041_;
goto v___jp_3007_;
}
else
{
lean_object* v_val_3042_; 
v_val_3042_ = lean_ctor_get(v_result_3001_, 0);
lean_inc(v_val_3042_);
lean_dec_ref(v_result_3001_);
v___y_3008_ = v_val_3042_;
goto v___jp_3007_;
}
v___jp_3007_:
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 1, v___x_3009_);
lean_ctor_set(v___x_3003_, 0, v___x_3006_);
v___x_3011_ = v___x_3003_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
size_t v_sz_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
v_sz_3012_ = lean_array_size(v___y_3008_);
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v___y_3008_, v_sz_3012_, v___x_3013_, v___x_3011_, v_a_2991_);
lean_dec_ref(v___y_3008_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3031_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3031_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3031_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v_fst_3019_; lean_object* v_snd_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3030_; 
v_fst_3019_ = lean_ctor_get(v_a_3015_, 0);
v_snd_3020_ = lean_ctor_get(v_a_3015_, 1);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_a_3015_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3022_ = v_a_3015_;
v_isShared_3023_ = v_isSharedCheck_3030_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_snd_3020_);
lean_inc(v_fst_3019_);
lean_dec(v_a_3015_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3030_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v_fst_3019_);
lean_ctor_set(v___x_3022_, 0, v_snd_3020_);
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_snd_3020_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_fst_3019_);
v___x_3025_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3025_);
v___x_3027_ = v___x_3017_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3032_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3014_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3014_);
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
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v_requestNo_2988_);
v_a_3045_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2999_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2999_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v___x_2994_);
lean_dec(v_requestNo_2988_);
v_a_3053_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2998_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2998_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object* v_requestNo_3061_, lean_object* v_uri_3062_, lean_object* v_pos_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(v_requestNo_3061_, v_uri_3062_, v_pos_3063_, v_a_3064_);
lean_dec_ref(v_a_3064_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object* v_j_3067_, lean_object* v_k_3068_){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = l_Lean_Json_getObjValD(v_j_3067_, v_k_3068_);
v___x_3070_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object* v_j_3071_, lean_object* v_k_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_j_3071_, v_k_3072_);
lean_dec_ref(v_k_3072_);
return v_res_3073_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = 1;
v___x_3081_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1));
v___x_3082_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_3084_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2);
v___x_3085_ = lean_string_append(v___x_3084_, v___x_3083_);
return v___x_3085_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_3087_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3088_ = lean_string_append(v___x_3087_, v___x_3086_);
return v___x_3088_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3090_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4);
v___x_3091_ = lean_string_append(v___x_3090_, v___x_3089_);
return v___x_3091_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_3093_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3094_ = lean_string_append(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3096_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6);
v___x_3097_ = lean_string_append(v___x_3096_, v___x_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object* v_json_3098_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_3098_);
v___x_3100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_json_3098_, v___x_3099_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v_json_3098_);
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3110_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3110_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3105_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5);
v___x_3106_ = lean_string_append(v___x_3105_, v_a_3101_);
lean_dec(v_a_3101_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3106_);
v___x_3108_ = v___x_3103_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
else
{
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec(v_json_3098_);
v_a_3111_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3100_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3100_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
lean_ctor_set_tag(v___x_3113_, 0);
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v_a_3119_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3119_);
lean_dec_ref(v___x_3100_);
v___x_3120_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3121_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_json_3098_, v___x_3120_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3131_; 
lean_dec(v_a_3119_);
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3131_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3131_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3126_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7);
v___x_3127_ = lean_string_append(v___x_3126_, v_a_3122_);
lean_dec(v_a_3122_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3127_);
v___x_3129_ = v___x_3124_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
else
{
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v_a_3119_);
v_a_3132_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3121_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3121_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set_tag(v___x_3134_, 0);
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3148_; 
v_a_3140_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3142_ = v___x_3121_;
v_isShared_3143_ = v_isSharedCheck_3148_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3121_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3148_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v_a_3119_);
lean_ctor_set(v___x_3144_, 1, v_a_3140_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3144_);
v___x_3146_ = v___x_3142_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3149_, size_t v_i_3150_, lean_object* v_bs_3151_){
_start:
{
uint8_t v___x_3152_; 
v___x_3152_ = lean_usize_dec_lt(v_i_3150_, v_sz_3149_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_bs_3151_);
return v___x_3153_;
}
else
{
lean_object* v_v_3154_; lean_object* v___x_3155_; 
v_v_3154_ = lean_array_uget_borrowed(v_bs_3151_, v_i_3150_);
lean_inc(v_v_3154_);
v___x_3155_ = l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(v_v_3154_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v_bs_3151_);
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3155_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3155_);
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
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3164_; lean_object* v___x_3165_; lean_object* v_bs_x27_3166_; size_t v___x_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v_a_3164_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3164_);
lean_dec_ref(v___x_3155_);
v___x_3165_ = lean_unsigned_to_nat(0u);
v_bs_x27_3166_ = lean_array_uset(v_bs_3151_, v_i_3150_, v___x_3165_);
v___x_3167_ = ((size_t)1ULL);
v___x_3168_ = lean_usize_add(v_i_3150_, v___x_3167_);
v___x_3169_ = lean_array_uset(v_bs_x27_3166_, v_i_3150_, v_a_3164_);
v_i_3150_ = v___x_3168_;
v_bs_3151_ = v___x_3169_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_3171_){
_start:
{
if (lean_obj_tag(v_x_3171_) == 4)
{
lean_object* v_elems_3172_; size_t v_sz_3173_; size_t v___x_3174_; lean_object* v___x_3175_; 
v_elems_3172_ = lean_ctor_get(v_x_3171_, 0);
lean_inc_ref(v_elems_3172_);
lean_dec_ref(v_x_3171_);
v_sz_3173_ = lean_array_size(v_elems_3172_);
v___x_3174_ = ((size_t)0ULL);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_3173_, v___x_3174_, v_elems_3172_);
return v___x_3175_;
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3176_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3177_ = lean_unsigned_to_nat(80u);
v___x_3178_ = l_Lean_Json_pretty(v_x_3171_, v___x_3177_);
v___x_3179_ = lean_string_append(v___x_3176_, v___x_3178_);
lean_dec_ref(v___x_3178_);
v___x_3180_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3181_ = lean_string_append(v___x_3179_, v___x_3180_);
v___x_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object* v_j_3183_, lean_object* v_k_3184_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = l_Lean_Json_getObjValD(v_j_3183_, v_k_3184_);
v___x_3186_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object* v_j_3187_, lean_object* v_k_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_j_3187_, v_k_3188_);
lean_dec_ref(v_k_3188_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3190_, lean_object* v_i_3191_, lean_object* v_bs_3192_){
_start:
{
size_t v_sz_boxed_3193_; size_t v_i_boxed_3194_; lean_object* v_res_3195_; 
v_sz_boxed_3193_ = lean_unbox_usize(v_sz_3190_);
lean_dec(v_sz_3190_);
v_i_boxed_3194_ = lean_unbox_usize(v_i_3191_);
lean_dec(v_i_3191_);
v_res_3195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3193_, v_i_boxed_3194_, v_bs_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object* v_x_3198_){
_start:
{
lean_object* v_item_3199_; lean_object* v_children_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3220_; 
v_item_3199_ = lean_ctor_get(v_x_3198_, 0);
v_children_3200_ = lean_ctor_get(v_x_3198_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_x_3198_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3202_ = v_x_3198_;
v_isShared_3203_ = v_isSharedCheck_3220_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_children_3200_);
lean_inc(v_item_3199_);
lean_dec(v_x_3198_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3220_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3204_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_3205_ = l_Lean_Lsp_instToJsonLeanImport_toJson(v_item_3199_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v___x_3205_);
lean_ctor_set(v___x_3202_, 0, v___x_3204_);
v___x_3207_ = v___x_3202_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3208_ = lean_box(0);
v___x_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3207_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3211_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(v_children_3200_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v___x_3208_);
v___x_3214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v___x_3208_);
v___x_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3209_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_3217_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_3215_, v___x_3216_);
v___x_3218_ = l_Lean_Json_mkObj(v___x_3217_);
lean_dec(v___x_3217_);
return v___x_3218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t v_sz_3221_, size_t v_i_3222_, lean_object* v_bs_3223_){
_start:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_usize_dec_lt(v_i_3222_, v_sz_3221_);
if (v___x_3224_ == 0)
{
return v_bs_3223_;
}
else
{
lean_object* v_v_3225_; lean_object* v___x_3226_; lean_object* v_bs_x27_3227_; lean_object* v___x_3228_; size_t v___x_3229_; size_t v___x_3230_; lean_object* v___x_3231_; 
v_v_3225_ = lean_array_uget(v_bs_3223_, v_i_3222_);
v___x_3226_ = lean_unsigned_to_nat(0u);
v_bs_x27_3227_ = lean_array_uset(v_bs_3223_, v_i_3222_, v___x_3226_);
v___x_3228_ = l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(v_v_3225_);
v___x_3229_ = ((size_t)1ULL);
v___x_3230_ = lean_usize_add(v_i_3222_, v___x_3229_);
v___x_3231_ = lean_array_uset(v_bs_x27_3227_, v_i_3222_, v___x_3228_);
v_i_3222_ = v___x_3230_;
v_bs_3223_ = v___x_3231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object* v_a_3233_){
_start:
{
size_t v_sz_3234_; size_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v_sz_3234_ = lean_array_size(v_a_3233_);
v___x_3235_ = ((size_t)0ULL);
v___x_3236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_3234_, v___x_3235_, v_a_3233_);
v___x_3237_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3238_, lean_object* v_i_3239_, lean_object* v_bs_3240_){
_start:
{
size_t v_sz_boxed_3241_; size_t v_i_boxed_3242_; lean_object* v_res_3243_; 
v_sz_boxed_3241_ = lean_unbox_usize(v_sz_3238_);
lean_dec(v_sz_3238_);
v_i_boxed_3242_ = lean_unbox_usize(v_i_3239_);
lean_dec(v_i_3239_);
v_res_3243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_boxed_3241_, v_i_boxed_3242_, v_bs_3240_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t v_sz_3246_, size_t v_i_3247_, lean_object* v_bs_3248_){
_start:
{
uint8_t v___x_3249_; 
v___x_3249_ = lean_usize_dec_lt(v_i_3247_, v_sz_3246_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_bs_3248_);
return v___x_3250_;
}
else
{
lean_object* v_v_3251_; lean_object* v___x_3252_; 
v_v_3251_ = lean_array_uget_borrowed(v_bs_3248_, v_i_3247_);
lean_inc(v_v_3251_);
v___x_3252_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v_v_3251_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v_bs_3248_);
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3262_; lean_object* v_bs_x27_3263_; size_t v___x_3264_; size_t v___x_3265_; lean_object* v___x_3266_; 
v_a_3261_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___x_3252_);
v___x_3262_ = lean_unsigned_to_nat(0u);
v_bs_x27_3263_ = lean_array_uset(v_bs_3248_, v_i_3247_, v___x_3262_);
v___x_3264_ = ((size_t)1ULL);
v___x_3265_ = lean_usize_add(v_i_3247_, v___x_3264_);
v___x_3266_ = lean_array_uset(v_bs_x27_3263_, v_i_3247_, v_a_3261_);
v_i_3247_ = v___x_3265_;
v_bs_3248_ = v___x_3266_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_3268_, lean_object* v_i_3269_, lean_object* v_bs_3270_){
_start:
{
size_t v_sz_boxed_3271_; size_t v_i_boxed_3272_; lean_object* v_res_3273_; 
v_sz_boxed_3271_ = lean_unbox_usize(v_sz_3268_);
lean_dec(v_sz_3268_);
v_i_boxed_3272_ = lean_unbox_usize(v_i_3269_);
lean_dec(v_i_3269_);
v_res_3273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_boxed_3271_, v_i_boxed_3272_, v_bs_3270_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object* v_x_3274_){
_start:
{
if (lean_obj_tag(v_x_3274_) == 4)
{
lean_object* v_elems_3275_; size_t v_sz_3276_; size_t v___x_3277_; lean_object* v___x_3278_; 
v_elems_3275_ = lean_ctor_get(v_x_3274_, 0);
lean_inc_ref(v_elems_3275_);
lean_dec_ref(v_x_3274_);
v_sz_3276_ = lean_array_size(v_elems_3275_);
v___x_3277_ = ((size_t)0ULL);
v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_3276_, v___x_3277_, v_elems_3275_);
return v___x_3278_;
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3279_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3280_ = lean_unsigned_to_nat(80u);
v___x_3281_ = l_Lean_Json_pretty(v_x_3274_, v___x_3280_);
v___x_3282_ = lean_string_append(v___x_3279_, v___x_3281_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3284_ = lean_string_append(v___x_3282_, v___x_3283_);
v___x_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
return v___x_3285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object* v_expectedID_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_Lsp_Ipc_stdout(v_a_3287_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3433_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3433_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3433_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_IO_FS_Stream_readLspMessage(v_a_3290_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3424_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3424_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3424_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___y_3300_; lean_object* v___y_3301_; 
switch(lean_obj_tag(v_a_3295_))
{
case 2:
{
lean_object* v_id_3307_; lean_object* v_result_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3352_; 
v_id_3307_ = lean_ctor_get(v_a_3295_, 0);
v_result_3308_ = lean_ctor_get(v_a_3295_, 1);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_a_3295_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3310_ = v_a_3295_;
v_isShared_3311_ = v_isSharedCheck_3352_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_result_3308_);
lean_inc(v_id_3307_);
lean_dec(v_a_3295_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3352_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
uint8_t v___x_3312_; 
v___x_3312_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3307_, v_expectedID_3286_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___y_3315_; 
lean_del_object(v___x_3310_);
lean_dec(v_result_3308_);
lean_del_object(v___x_3292_);
v___x_3313_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3286_))
{
case 0:
{
lean_object* v_s_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_s_3326_ = lean_ctor_get(v_expectedID_3286_, 0);
lean_inc_ref(v_s_3326_);
lean_dec_ref(v_expectedID_3286_);
v___x_3327_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3328_ = lean_string_append(v___x_3327_, v_s_3326_);
lean_dec_ref(v_s_3326_);
v___x_3329_ = lean_string_append(v___x_3328_, v___x_3327_);
v___y_3315_ = v___x_3329_;
goto v___jp_3314_;
}
case 1:
{
lean_object* v_n_3330_; lean_object* v___x_3331_; 
v_n_3330_ = lean_ctor_get(v_expectedID_3286_, 0);
lean_inc_ref(v_n_3330_);
lean_dec_ref(v_expectedID_3286_);
v___x_3331_ = l_Lean_JsonNumber_toString(v_n_3330_);
v___y_3315_ = v___x_3331_;
goto v___jp_3314_;
}
default: 
{
lean_object* v___x_3332_; 
v___x_3332_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3315_ = v___x_3332_;
goto v___jp_3314_;
}
}
v___jp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_string_append(v___x_3313_, v___y_3315_);
lean_dec_ref(v___y_3315_);
v___x_3317_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3318_ = lean_string_append(v___x_3316_, v___x_3317_);
switch(lean_obj_tag(v_id_3307_))
{
case 0:
{
lean_object* v_s_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_s_3319_ = lean_ctor_get(v_id_3307_, 0);
lean_inc_ref(v_s_3319_);
lean_dec_ref(v_id_3307_);
v___x_3320_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3321_ = lean_string_append(v___x_3320_, v_s_3319_);
lean_dec_ref(v_s_3319_);
v___x_3322_ = lean_string_append(v___x_3321_, v___x_3320_);
v___y_3300_ = v___x_3318_;
v___y_3301_ = v___x_3322_;
goto v___jp_3299_;
}
case 1:
{
lean_object* v_n_3323_; lean_object* v___x_3324_; 
v_n_3323_ = lean_ctor_get(v_id_3307_, 0);
lean_inc_ref(v_n_3323_);
lean_dec_ref(v_id_3307_);
v___x_3324_ = l_Lean_JsonNumber_toString(v_n_3323_);
v___y_3300_ = v___x_3318_;
v___y_3301_ = v___x_3324_;
goto v___jp_3299_;
}
default: 
{
lean_object* v___x_3325_; 
v___x_3325_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3300_ = v___x_3318_;
v___y_3301_ = v___x_3325_;
goto v___jp_3299_;
}
}
}
}
else
{
lean_object* v___x_3333_; 
lean_dec(v_id_3307_);
lean_del_object(v___x_3297_);
lean_inc(v_result_3308_);
v___x_3333_ = l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(v_result_3308_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
lean_del_object(v___x_3310_);
lean_dec(v_expectedID_3286_);
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref(v___x_3333_);
v___x_3335_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3336_ = l_Lean_Json_compress(v_result_3308_);
v___x_3337_ = lean_string_append(v___x_3335_, v___x_3336_);
lean_dec_ref(v___x_3336_);
v___x_3338_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3339_ = lean_string_append(v___x_3337_, v___x_3338_);
v___x_3340_ = lean_string_append(v___x_3339_, v_a_3334_);
lean_dec(v_a_3334_);
v___x_3341_ = lean_mk_io_user_error(v___x_3340_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set_tag(v___x_3292_, 1);
lean_ctor_set(v___x_3292_, 0, v___x_3341_);
v___x_3343_ = v___x_3292_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; 
lean_dec(v_result_3308_);
v_a_3345_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3345_);
lean_dec_ref(v___x_3333_);
if (v_isShared_3311_ == 0)
{
lean_ctor_set_tag(v___x_3310_, 0);
lean_ctor_set(v___x_3310_, 1, v_a_3345_);
lean_ctor_set(v___x_3310_, 0, v_expectedID_3286_);
v___x_3347_ = v___x_3310_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_expectedID_3286_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_a_3345_);
v___x_3347_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3349_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3347_);
v___x_3349_ = v___x_3292_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3353_; uint8_t v_code_3354_; lean_object* v_message_3355_; lean_object* v_data_x3f_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___x_3388_; lean_object* v___y_3390_; 
lean_del_object(v___x_3297_);
lean_dec(v_expectedID_3286_);
v_id_3353_ = lean_ctor_get(v_a_3295_, 0);
lean_inc(v_id_3353_);
v_code_3354_ = lean_ctor_get_uint8(v_a_3295_, sizeof(void*)*3);
v_message_3355_ = lean_ctor_get(v_a_3295_, 1);
lean_inc_ref(v_message_3355_);
v_data_x3f_3356_ = lean_ctor_get(v_a_3295_, 2);
lean_inc(v_data_x3f_3356_);
lean_dec_ref(v_a_3295_);
v___x_3357_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3358_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3388_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3353_))
{
case 0:
{
lean_object* v_s_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
v_s_3406_ = lean_ctor_get(v_id_3353_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_id_3353_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v_id_3353_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_s_3406_);
lean_dec(v_id_3353_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set_tag(v___x_3408_, 3);
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_s_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
v___y_3390_ = v___x_3411_;
goto v___jp_3389_;
}
}
}
case 1:
{
lean_object* v_n_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
v_n_3414_ = lean_ctor_get(v_id_3353_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_id_3353_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v_id_3353_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_n_3414_);
lean_dec(v_id_3353_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 2);
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_n_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
v___y_3390_ = v___x_3419_;
goto v___jp_3389_;
}
}
}
default: 
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_box(0);
v___y_3390_ = v___x_3422_;
goto v___jp_3389_;
}
}
v___jp_3359_:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
lean_inc(v___y_3363_);
lean_inc_ref(v___y_3361_);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___y_3361_);
lean_ctor_set(v___x_3364_, 1, v___y_3363_);
v___x_3365_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_message_3355_);
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = lean_box(0);
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3364_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3372_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3371_, v_data_x3f_3356_);
lean_dec(v_data_x3f_3356_);
v___x_3373_ = l_List_appendTR___redArg(v___x_3370_, v___x_3372_);
v___x_3374_ = l_Lean_Json_mkObj(v___x_3373_);
lean_dec(v___x_3373_);
lean_inc_ref(v___y_3362_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___y_3362_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
lean_ctor_set(v___x_3376_, 1, v___x_3368_);
v___x_3377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___y_3360_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3358_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = l_Lean_Json_mkObj(v___x_3378_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = l_Lean_Json_compress(v___x_3379_);
v___x_3381_ = lean_string_append(v___x_3357_, v___x_3380_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3383_ = lean_string_append(v___x_3381_, v___x_3382_);
v___x_3384_ = lean_mk_io_user_error(v___x_3383_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set_tag(v___x_3292_, 1);
lean_ctor_set(v___x_3292_, 0, v___x_3384_);
v___x_3386_ = v___x_3292_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
v___jp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3388_);
lean_ctor_set(v___x_3391_, 1, v___y_3390_);
v___x_3392_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3393_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3354_)
{
case 0:
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3394_;
goto v___jp_3359_;
}
case 1:
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3395_;
goto v___jp_3359_;
}
case 2:
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3396_;
goto v___jp_3359_;
}
case 3:
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3397_;
goto v___jp_3359_;
}
case 4:
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3398_;
goto v___jp_3359_;
}
case 5:
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3399_;
goto v___jp_3359_;
}
case 6:
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3400_;
goto v___jp_3359_;
}
case 7:
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3401_;
goto v___jp_3359_;
}
case 8:
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3402_;
goto v___jp_3359_;
}
case 9:
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3403_;
goto v___jp_3359_;
}
case 10:
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3404_;
goto v___jp_3359_;
}
default: 
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___x_3393_;
v___y_3362_ = v___x_3392_;
v___y_3363_ = v___x_3405_;
goto v___jp_3359_;
}
}
}
}
default: 
{
lean_del_object(v___x_3297_);
lean_dec(v_a_3295_);
lean_del_object(v___x_3292_);
goto _start;
}
}
v___jp_3299_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3305_; 
v___x_3302_ = lean_string_append(v___y_3300_, v___y_3301_);
lean_dec_ref(v___y_3301_);
v___x_3303_ = lean_mk_io_user_error(v___x_3302_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set_tag(v___x_3297_, 1);
lean_ctor_set(v___x_3297_, 0, v___x_3303_);
v___x_3305_ = v___x_3297_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_del_object(v___x_3292_);
lean_dec(v_expectedID_3286_);
v_a_3425_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3294_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3294_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v_expectedID_3286_);
v_a_3434_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3289_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3289_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object* v_expectedID_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v_expectedID_3442_, v_a_3443_);
lean_dec_ref(v_a_3443_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object* v_v_3446_){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_v_3446_);
v___x_3448_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_v_3449_);
lean_dec_ref(v_v_3449_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object* v_h_3451_, lean_object* v_r_3452_){
_start:
{
lean_object* v_id_3454_; lean_object* v_method_3455_; lean_object* v_param_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3476_; 
v_id_3454_ = lean_ctor_get(v_r_3452_, 0);
v_method_3455_ = lean_ctor_get(v_r_3452_, 1);
v_param_3456_ = lean_ctor_get(v_r_3452_, 2);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_r_3452_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3458_ = v_r_3452_;
v_isShared_3459_ = v_isSharedCheck_3476_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_param_3456_);
lean_inc(v_method_3455_);
lean_inc(v_id_3454_);
lean_dec(v_r_3452_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3476_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___y_3461_; lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_param_3456_);
lean_dec(v_param_3456_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref(v___x_3466_);
v___x_3467_ = lean_box(0);
v___y_3461_ = v___x_3467_;
goto v___jp_3460_;
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
v_a_3468_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3466_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3466_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
v___y_3461_ = v___x_3473_;
goto v___jp_3460_;
}
}
}
v___jp_3460_:
{
lean_object* v___x_3463_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 2, v___y_3461_);
v___x_3463_ = v___x_3458_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_id_3454_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_method_3455_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v___y_3461_);
v___x_3463_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_IO_FS_Stream_writeLspMessage(v_h_3451_, v___x_3463_);
return v___x_3464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object* v_h_3477_, lean_object* v_r_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_h_3477_, v_r_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object* v_r_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v___x_3484_; lean_object* v_a_3485_; lean_object* v___x_3486_; 
v___x_3484_ = l_Lean_Lsp_Ipc_stdin(v_a_3482_);
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref(v___x_3484_);
v___x_3486_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_a_3485_, v_r_3481_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object* v_r_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v_r_3487_, v_a_3488_);
lean_dec_ref(v_a_3488_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object* v_requestNo_3494_, lean_object* v_item_3495_, lean_object* v_visited_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_module_3499_; lean_object* v_name_3500_; uint8_t v___x_3501_; 
v_module_3499_ = lean_ctor_get(v_item_3495_, 0);
v_name_3500_ = lean_ctor_get(v_module_3499_, 0);
v___x_3501_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3500_, v_visited_3496_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_inc(v_requestNo_3494_);
v___x_3502_ = l_Lean_JsonNumber_fromNat(v_requestNo_3494_);
v___x_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
v___x_3504_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0));
lean_inc_ref(v_module_3499_);
lean_inc_ref(v___x_3503_);
v___x_3505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3503_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
lean_ctor_set(v___x_3505_, 2, v_module_3499_);
v___x_3506_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v___x_3505_, v_a_3497_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; 
lean_dec_ref(v___x_3506_);
v___x_3507_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3503_, v_a_3497_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___y_3510_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3507_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = lean_box(0);
lean_inc_ref(v_name_3500_);
v___x_3553_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3500_, v___x_3552_, v_visited_3496_);
v___y_3510_ = v___x_3553_;
goto v___jp_3509_;
}
else
{
v___y_3510_ = v_visited_3496_;
goto v___jp_3509_;
}
v___jp_3509_:
{
lean_object* v_result_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3550_; 
v_result_3511_ = lean_ctor_get(v_a_3508_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_a_3508_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; 
v_unused_3551_ = lean_ctor_get(v_a_3508_, 0);
lean_dec(v_unused_3551_);
v___x_3513_ = v_a_3508_;
v_isShared_3514_ = v_isSharedCheck_3550_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_result_3511_);
lean_dec(v_a_3508_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3550_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3515_ = lean_unsigned_to_nat(1u);
v___x_3516_ = lean_nat_add(v_requestNo_3494_, v___x_3515_);
lean_dec(v_requestNo_3494_);
v___x_3517_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 1, v___x_3517_);
lean_ctor_set(v___x_3513_, 0, v___x_3516_);
v___x_3519_ = v___x_3513_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
size_t v_sz_3520_; size_t v___x_3521_; lean_object* v___x_3522_; 
v_sz_3520_ = lean_array_size(v_result_3511_);
v___x_3521_ = ((size_t)0ULL);
v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___y_3510_, v_result_3511_, v_sz_3520_, v___x_3521_, v___x_3519_, v_a_3497_);
lean_dec(v_result_3511_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3540_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3540_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3540_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v_fst_3527_; lean_object* v_snd_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3539_; 
v_fst_3527_ = lean_ctor_get(v_a_3523_, 0);
v_snd_3528_ = lean_ctor_get(v_a_3523_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_a_3523_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3530_ = v_a_3523_;
v_isShared_3531_ = v_isSharedCheck_3539_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_snd_3528_);
lean_inc(v_fst_3527_);
lean_dec(v_a_3523_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3539_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3532_, 0, v_item_3495_);
lean_ctor_set(v___x_3532_, 1, v_snd_3528_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v_fst_3527_);
lean_ctor_set(v___x_3530_, 0, v___x_3532_);
v___x_3534_ = v___x_3530_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_fst_3527_);
v___x_3534_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3534_);
v___x_3536_ = v___x_3525_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec_ref(v_item_3495_);
v_a_3541_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3522_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3522_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v_visited_3496_);
lean_dec_ref(v_item_3495_);
lean_dec(v_requestNo_3494_);
v_a_3554_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3507_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3507_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec_ref(v___x_3503_);
lean_dec(v_visited_3496_);
lean_dec_ref(v_item_3495_);
lean_dec(v_requestNo_3494_);
v_a_3562_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3506_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3506_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec(v_visited_3496_);
v___x_3570_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v_item_3495_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v_requestNo_3494_);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object* v___x_3574_, lean_object* v_as_3575_, size_t v_sz_3576_, size_t v_i_3577_, lean_object* v_b_3578_, lean_object* v___y_3579_){
_start:
{
uint8_t v___x_3581_; 
v___x_3581_ = lean_usize_dec_lt(v_i_3577_, v_sz_3576_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; 
lean_dec(v___x_3574_);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v_b_3578_);
return v___x_3582_;
}
else
{
lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v_a_3585_; lean_object* v___x_3586_; 
v_fst_3583_ = lean_ctor_get(v_b_3578_, 0);
lean_inc(v_fst_3583_);
v_snd_3584_ = lean_ctor_get(v_b_3578_, 1);
lean_inc(v_snd_3584_);
lean_dec_ref(v_b_3578_);
v_a_3585_ = lean_array_uget_borrowed(v_as_3575_, v_i_3577_);
lean_inc(v___x_3574_);
lean_inc(v_a_3585_);
v___x_3586_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_fst_3583_, v_a_3585_, v___x_3574_, v___y_3579_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v_fst_3588_; lean_object* v_snd_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3600_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref(v___x_3586_);
v_fst_3588_ = lean_ctor_get(v_a_3587_, 0);
v_snd_3589_ = lean_ctor_get(v_a_3587_, 1);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_a_3587_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3591_ = v_a_3587_;
v_isShared_3592_ = v_isSharedCheck_3600_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_snd_3589_);
lean_inc(v_fst_3588_);
lean_dec(v_a_3587_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3600_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3593_ = lean_array_push(v_snd_3584_, v_fst_3588_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 1, v___x_3593_);
lean_ctor_set(v___x_3591_, 0, v_snd_3589_);
v___x_3595_ = v___x_3591_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_snd_3589_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v___x_3593_);
v___x_3595_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
size_t v___x_3596_; size_t v___x_3597_; 
v___x_3596_ = ((size_t)1ULL);
v___x_3597_ = lean_usize_add(v_i_3577_, v___x_3596_);
v_i_3577_ = v___x_3597_;
v_b_3578_ = v___x_3595_;
goto _start;
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
lean_dec(v_snd_3584_);
lean_dec(v___x_3574_);
v_a_3601_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3586_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3586_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object* v___x_3609_, lean_object* v_as_3610_, lean_object* v_sz_3611_, lean_object* v_i_3612_, lean_object* v_b_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
size_t v_sz_boxed_3616_; size_t v_i_boxed_3617_; lean_object* v_res_3618_; 
v_sz_boxed_3616_ = lean_unbox_usize(v_sz_3611_);
lean_dec(v_sz_3611_);
v_i_boxed_3617_ = lean_unbox_usize(v_i_3612_);
lean_dec(v_i_3612_);
v_res_3618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3609_, v_as_3610_, v_sz_boxed_3616_, v_i_boxed_3617_, v_b_3613_, v___y_3614_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v_as_3610_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object* v_requestNo_3619_, lean_object* v_item_3620_, lean_object* v_visited_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_requestNo_3619_, v_item_3620_, v_visited_3621_, v_a_3622_);
lean_dec_ref(v_a_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object* v_v_3625_){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(v_v_3625_);
v___x_3627_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object* v_h_3628_, lean_object* v_r_3629_){
_start:
{
lean_object* v_id_3631_; lean_object* v_method_3632_; lean_object* v_param_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3653_; 
v_id_3631_ = lean_ctor_get(v_r_3629_, 0);
v_method_3632_ = lean_ctor_get(v_r_3629_, 1);
v_param_3633_ = lean_ctor_get(v_r_3629_, 2);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_r_3629_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3635_ = v_r_3629_;
v_isShared_3636_ = v_isSharedCheck_3653_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_param_3633_);
lean_inc(v_method_3632_);
lean_inc(v_id_3631_);
lean_dec(v_r_3629_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3653_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___y_3638_; lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(v_param_3633_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v___x_3644_; 
lean_dec_ref(v___x_3643_);
v___x_3644_ = lean_box(0);
v___y_3638_ = v___x_3644_;
goto v___jp_3637_;
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
v_a_3645_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3643_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3643_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
v___y_3638_ = v___x_3650_;
goto v___jp_3637_;
}
}
}
v___jp_3637_:
{
lean_object* v___x_3640_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 2, v___y_3638_);
v___x_3640_ = v___x_3635_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_id_3631_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_method_3632_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v___y_3638_);
v___x_3640_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_IO_FS_Stream_writeLspMessage(v_h_3628_, v___x_3640_);
return v___x_3641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object* v_h_3654_, lean_object* v_r_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_h_3654_, v_r_3655_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object* v_r_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v___x_3661_; lean_object* v_a_3662_; lean_object* v___x_3663_; 
v___x_3661_ = l_Lean_Lsp_Ipc_stdin(v_a_3659_);
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
v___x_3663_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_a_3662_, v_r_3658_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object* v_r_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v_r_3664_, v_a_3665_);
lean_dec_ref(v_a_3665_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object* v_x_3670_){
_start:
{
if (lean_obj_tag(v_x_3670_) == 0)
{
lean_object* v___x_3671_; 
v___x_3671_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0));
return v___x_3671_;
}
else
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v_x_3670_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3689_; 
v_a_3681_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3683_ = v___x_3672_;
v_isShared_3684_ = v_isSharedCheck_3689_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3672_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3689_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3687_; 
v___x_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_a_3681_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v___x_3685_);
v___x_3687_ = v___x_3683_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object* v_expectedID_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Lean_Lsp_Ipc_stdout(v_a_3691_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3837_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3696_ = v___x_3693_;
v_isShared_3697_ = v_isSharedCheck_3837_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3837_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_IO_FS_Stream_readLspMessage(v_a_3694_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3828_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3828_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3828_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___y_3704_; lean_object* v___y_3705_; 
switch(lean_obj_tag(v_a_3699_))
{
case 2:
{
lean_object* v_id_3711_; lean_object* v_result_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3756_; 
v_id_3711_ = lean_ctor_get(v_a_3699_, 0);
v_result_3712_ = lean_ctor_get(v_a_3699_, 1);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_a_3699_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3714_ = v_a_3699_;
v_isShared_3715_ = v_isSharedCheck_3756_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_result_3712_);
lean_inc(v_id_3711_);
lean_dec(v_a_3699_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3756_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
uint8_t v___x_3716_; 
v___x_3716_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3711_, v_expectedID_3690_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___y_3719_; 
lean_del_object(v___x_3714_);
lean_dec(v_result_3712_);
lean_del_object(v___x_3696_);
v___x_3717_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3690_))
{
case 0:
{
lean_object* v_s_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_s_3730_ = lean_ctor_get(v_expectedID_3690_, 0);
lean_inc_ref(v_s_3730_);
lean_dec_ref(v_expectedID_3690_);
v___x_3731_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3732_ = lean_string_append(v___x_3731_, v_s_3730_);
lean_dec_ref(v_s_3730_);
v___x_3733_ = lean_string_append(v___x_3732_, v___x_3731_);
v___y_3719_ = v___x_3733_;
goto v___jp_3718_;
}
case 1:
{
lean_object* v_n_3734_; lean_object* v___x_3735_; 
v_n_3734_ = lean_ctor_get(v_expectedID_3690_, 0);
lean_inc_ref(v_n_3734_);
lean_dec_ref(v_expectedID_3690_);
v___x_3735_ = l_Lean_JsonNumber_toString(v_n_3734_);
v___y_3719_ = v___x_3735_;
goto v___jp_3718_;
}
default: 
{
lean_object* v___x_3736_; 
v___x_3736_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3719_ = v___x_3736_;
goto v___jp_3718_;
}
}
v___jp_3718_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = lean_string_append(v___x_3717_, v___y_3719_);
lean_dec_ref(v___y_3719_);
v___x_3721_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3722_ = lean_string_append(v___x_3720_, v___x_3721_);
switch(lean_obj_tag(v_id_3711_))
{
case 0:
{
lean_object* v_s_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_s_3723_ = lean_ctor_get(v_id_3711_, 0);
lean_inc_ref(v_s_3723_);
lean_dec_ref(v_id_3711_);
v___x_3724_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3725_ = lean_string_append(v___x_3724_, v_s_3723_);
lean_dec_ref(v_s_3723_);
v___x_3726_ = lean_string_append(v___x_3725_, v___x_3724_);
v___y_3704_ = v___x_3722_;
v___y_3705_ = v___x_3726_;
goto v___jp_3703_;
}
case 1:
{
lean_object* v_n_3727_; lean_object* v___x_3728_; 
v_n_3727_ = lean_ctor_get(v_id_3711_, 0);
lean_inc_ref(v_n_3727_);
lean_dec_ref(v_id_3711_);
v___x_3728_ = l_Lean_JsonNumber_toString(v_n_3727_);
v___y_3704_ = v___x_3722_;
v___y_3705_ = v___x_3728_;
goto v___jp_3703_;
}
default: 
{
lean_object* v___x_3729_; 
v___x_3729_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3704_ = v___x_3722_;
v___y_3705_ = v___x_3729_;
goto v___jp_3703_;
}
}
}
}
else
{
lean_object* v___x_3737_; 
lean_dec(v_id_3711_);
lean_del_object(v___x_3701_);
lean_inc(v_result_3712_);
v___x_3737_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(v_result_3712_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_del_object(v___x_3714_);
lean_dec(v_expectedID_3690_);
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___x_3737_);
v___x_3739_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3740_ = l_Lean_Json_compress(v_result_3712_);
v___x_3741_ = lean_string_append(v___x_3739_, v___x_3740_);
lean_dec_ref(v___x_3740_);
v___x_3742_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3743_ = lean_string_append(v___x_3741_, v___x_3742_);
v___x_3744_ = lean_string_append(v___x_3743_, v_a_3738_);
lean_dec(v_a_3738_);
v___x_3745_ = lean_mk_io_user_error(v___x_3744_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set_tag(v___x_3696_, 1);
lean_ctor_set(v___x_3696_, 0, v___x_3745_);
v___x_3747_ = v___x_3696_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; 
lean_dec(v_result_3712_);
v_a_3749_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3749_);
lean_dec_ref(v___x_3737_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set_tag(v___x_3714_, 0);
lean_ctor_set(v___x_3714_, 1, v_a_3749_);
lean_ctor_set(v___x_3714_, 0, v_expectedID_3690_);
v___x_3751_ = v___x_3714_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_expectedID_3690_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_a_3749_);
v___x_3751_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
lean_object* v___x_3753_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3751_);
v___x_3753_ = v___x_3696_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
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
}
case 3:
{
lean_object* v_id_3757_; uint8_t v_code_3758_; lean_object* v_message_3759_; lean_object* v_data_x3f_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___x_3792_; lean_object* v___y_3794_; 
lean_del_object(v___x_3701_);
lean_dec(v_expectedID_3690_);
v_id_3757_ = lean_ctor_get(v_a_3699_, 0);
lean_inc(v_id_3757_);
v_code_3758_ = lean_ctor_get_uint8(v_a_3699_, sizeof(void*)*3);
v_message_3759_ = lean_ctor_get(v_a_3699_, 1);
lean_inc_ref(v_message_3759_);
v_data_x3f_3760_ = lean_ctor_get(v_a_3699_, 2);
lean_inc(v_data_x3f_3760_);
lean_dec_ref(v_a_3699_);
v___x_3761_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3762_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3792_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3757_))
{
case 0:
{
lean_object* v_s_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
v_s_3810_ = lean_ctor_get(v_id_3757_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_id_3757_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v_id_3757_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_s_3810_);
lean_dec(v_id_3757_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
lean_ctor_set_tag(v___x_3812_, 3);
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_s_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
v___y_3794_ = v___x_3815_;
goto v___jp_3793_;
}
}
}
case 1:
{
lean_object* v_n_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
v_n_3818_ = lean_ctor_get(v_id_3757_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_id_3757_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v_id_3757_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_n_3818_);
lean_dec(v_id_3757_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set_tag(v___x_3820_, 2);
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_n_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
v___y_3794_ = v___x_3823_;
goto v___jp_3793_;
}
}
}
default: 
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_box(0);
v___y_3794_ = v___x_3826_;
goto v___jp_3793_;
}
}
v___jp_3763_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3790_; 
lean_inc(v___y_3767_);
lean_inc_ref(v___y_3764_);
v___x_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___y_3764_);
lean_ctor_set(v___x_3768_, 1, v___y_3767_);
v___x_3769_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3770_, 0, v_message_3759_);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_box(0);
v___x_3773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3768_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3776_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3775_, v_data_x3f_3760_);
lean_dec(v_data_x3f_3760_);
v___x_3777_ = l_List_appendTR___redArg(v___x_3774_, v___x_3776_);
v___x_3778_ = l_Lean_Json_mkObj(v___x_3777_);
lean_dec(v___x_3777_);
lean_inc_ref(v___y_3766_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___y_3766_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
lean_ctor_set(v___x_3780_, 1, v___x_3772_);
v___x_3781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___y_3765_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3762_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = l_Lean_Json_mkObj(v___x_3782_);
lean_dec_ref(v___x_3782_);
v___x_3784_ = l_Lean_Json_compress(v___x_3783_);
v___x_3785_ = lean_string_append(v___x_3761_, v___x_3784_);
lean_dec_ref(v___x_3784_);
v___x_3786_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3787_ = lean_string_append(v___x_3785_, v___x_3786_);
v___x_3788_ = lean_mk_io_user_error(v___x_3787_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set_tag(v___x_3696_, 1);
lean_ctor_set(v___x_3696_, 0, v___x_3788_);
v___x_3790_ = v___x_3696_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
v___jp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3792_);
lean_ctor_set(v___x_3795_, 1, v___y_3794_);
v___x_3796_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3797_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3758_)
{
case 0:
{
lean_object* v___x_3798_; 
v___x_3798_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3798_;
goto v___jp_3763_;
}
case 1:
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3799_;
goto v___jp_3763_;
}
case 2:
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3800_;
goto v___jp_3763_;
}
case 3:
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3801_;
goto v___jp_3763_;
}
case 4:
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3802_;
goto v___jp_3763_;
}
case 5:
{
lean_object* v___x_3803_; 
v___x_3803_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3803_;
goto v___jp_3763_;
}
case 6:
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3804_;
goto v___jp_3763_;
}
case 7:
{
lean_object* v___x_3805_; 
v___x_3805_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3805_;
goto v___jp_3763_;
}
case 8:
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3806_;
goto v___jp_3763_;
}
case 9:
{
lean_object* v___x_3807_; 
v___x_3807_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3807_;
goto v___jp_3763_;
}
case 10:
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3808_;
goto v___jp_3763_;
}
default: 
{
lean_object* v___x_3809_; 
v___x_3809_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3764_ = v___x_3797_;
v___y_3765_ = v___x_3795_;
v___y_3766_ = v___x_3796_;
v___y_3767_ = v___x_3809_;
goto v___jp_3763_;
}
}
}
}
default: 
{
lean_del_object(v___x_3701_);
lean_dec(v_a_3699_);
lean_del_object(v___x_3696_);
goto _start;
}
}
v___jp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3706_ = lean_string_append(v___y_3704_, v___y_3705_);
lean_dec_ref(v___y_3705_);
v___x_3707_ = lean_mk_io_user_error(v___x_3706_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set_tag(v___x_3701_, 1);
lean_ctor_set(v___x_3701_, 0, v___x_3707_);
v___x_3709_ = v___x_3701_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_del_object(v___x_3696_);
lean_dec(v_expectedID_3690_);
v_a_3829_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3698_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3698_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec(v_expectedID_3690_);
v_a_3838_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3693_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3693_);
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
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object* v_expectedID_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v_expectedID_3846_, v_a_3847_);
lean_dec_ref(v_a_3847_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object* v_requestNo_3854_, lean_object* v_uri_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_inc(v_requestNo_3854_);
v___x_3858_ = l_Lean_JsonNumber_fromNat(v_requestNo_3854_);
v___x_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
v___x_3860_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_3859_);
v___x_3861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3859_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
lean_ctor_set(v___x_3861_, 2, v_uri_3855_);
v___x_3862_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_3861_, v_a_3856_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v___x_3863_; 
lean_dec_ref(v___x_3862_);
v___x_3863_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_3859_, v_a_3856_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3922_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3922_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3922_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v_result_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3920_; 
v_result_3868_ = lean_ctor_get(v_a_3864_, 1);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_a_3864_);
if (v_isSharedCheck_3920_ == 0)
{
lean_object* v_unused_3921_; 
v_unused_3921_ = lean_ctor_get(v_a_3864_, 0);
lean_dec(v_unused_3921_);
v___x_3870_ = v_a_3864_;
v_isShared_3871_ = v_isSharedCheck_3920_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_result_3868_);
lean_dec(v_a_3864_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3920_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = lean_unsigned_to_nat(1u);
v___x_3873_ = lean_nat_add(v_requestNo_3854_, v___x_3872_);
lean_dec(v_requestNo_3854_);
if (lean_obj_tag(v_result_3868_) == 1)
{
lean_object* v_val_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3912_; 
lean_del_object(v___x_3866_);
v_val_3874_ = lean_ctor_get(v_result_3868_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_result_3868_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3876_ = v_result_3868_;
v_isShared_3877_ = v_isSharedCheck_3912_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_val_3874_);
lean_dec(v_result_3868_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3912_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
v___x_3878_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v___x_3878_);
lean_ctor_set(v___x_3870_, 0, v_val_3874_);
v___x_3880_ = v___x_3870_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_val_3874_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v___x_3878_);
v___x_3880_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = lean_box(1);
v___x_3882_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v___x_3873_, v___x_3880_, v___x_3881_, v_a_3856_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3902_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3902_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3902_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v_fst_3887_; lean_object* v_snd_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3901_; 
v_fst_3887_ = lean_ctor_get(v_a_3883_, 0);
v_snd_3888_ = lean_ctor_get(v_a_3883_, 1);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_a_3883_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3890_ = v_a_3883_;
v_isShared_3891_ = v_isSharedCheck_3901_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_snd_3888_);
lean_inc(v_fst_3887_);
lean_dec(v_a_3883_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3901_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v_fst_3887_);
v___x_3893_ = v___x_3876_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_fst_3887_);
v___x_3893_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3895_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 0, v___x_3893_);
v___x_3895_ = v___x_3890_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_snd_3888_);
v___x_3895_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3897_; 
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v___x_3895_);
v___x_3897_ = v___x_3885_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_del_object(v___x_3876_);
v_a_3903_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3882_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3882_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec(v_result_3868_);
v___x_3913_ = lean_box(0);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v___x_3873_);
lean_ctor_set(v___x_3870_, 0, v___x_3913_);
v___x_3915_ = v___x_3870_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3873_);
v___x_3915_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 0, v___x_3915_);
v___x_3917_ = v___x_3866_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v_requestNo_3854_);
v_a_3923_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3863_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3863_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v___x_3859_);
lean_dec(v_requestNo_3854_);
v_a_3931_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3862_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3862_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object* v_requestNo_3939_, lean_object* v_uri_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImports(v_requestNo_3939_, v_uri_3940_, v_a_3941_);
lean_dec_ref(v_a_3941_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object* v_v_3944_){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_v_3944_);
v___x_3946_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_v_3947_);
lean_dec_ref(v_v_3947_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object* v_h_3949_, lean_object* v_r_3950_){
_start:
{
lean_object* v_id_3952_; lean_object* v_method_3953_; lean_object* v_param_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3974_; 
v_id_3952_ = lean_ctor_get(v_r_3950_, 0);
v_method_3953_ = lean_ctor_get(v_r_3950_, 1);
v_param_3954_ = lean_ctor_get(v_r_3950_, 2);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_r_3950_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3956_ = v_r_3950_;
v_isShared_3957_ = v_isSharedCheck_3974_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_param_3954_);
lean_inc(v_method_3953_);
lean_inc(v_id_3952_);
lean_dec(v_r_3950_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3974_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___y_3959_; lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_param_3954_);
lean_dec(v_param_3954_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v___x_3965_; 
lean_dec_ref(v___x_3964_);
v___x_3965_ = lean_box(0);
v___y_3959_ = v___x_3965_;
goto v___jp_3958_;
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
v_a_3966_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3964_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3964_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
v___y_3959_ = v___x_3971_;
goto v___jp_3958_;
}
}
}
v___jp_3958_:
{
lean_object* v___x_3961_; 
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 2, v___y_3959_);
v___x_3961_ = v___x_3956_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_id_3952_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_method_3953_);
lean_ctor_set(v_reuseFailAlloc_3963_, 2, v___y_3959_);
v___x_3961_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_IO_FS_Stream_writeLspMessage(v_h_3949_, v___x_3961_);
return v___x_3962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object* v_h_3975_, lean_object* v_r_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_h_3975_, v_r_3976_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object* v_r_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v___x_3982_; lean_object* v_a_3983_; lean_object* v___x_3984_; 
v___x_3982_ = l_Lean_Lsp_Ipc_stdin(v_a_3980_);
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref(v___x_3982_);
v___x_3984_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_a_3983_, v_r_3979_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object* v_r_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v_r_3985_, v_a_3986_);
lean_dec_ref(v_a_3986_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object* v_requestNo_3990_, lean_object* v_item_3991_, lean_object* v_visited_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v_module_3995_; lean_object* v_name_3996_; uint8_t v___x_3997_; 
v_module_3995_ = lean_ctor_get(v_item_3991_, 0);
v_name_3996_ = lean_ctor_get(v_module_3995_, 0);
v___x_3997_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3996_, v_visited_3992_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
lean_inc(v_requestNo_3990_);
v___x_3998_ = l_Lean_JsonNumber_fromNat(v_requestNo_3990_);
v___x_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
v___x_4000_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0));
lean_inc_ref(v_module_3995_);
lean_inc_ref(v___x_3999_);
v___x_4001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3999_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
lean_ctor_set(v___x_4001_, 2, v_module_3995_);
v___x_4002_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v___x_4001_, v_a_3993_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v___x_4003_; 
lean_dec_ref(v___x_4002_);
v___x_4003_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3999_, v_a_3993_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___y_4006_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref(v___x_4003_);
if (v___x_3997_ == 0)
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_box(0);
lean_inc_ref(v_name_3996_);
v___x_4049_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3996_, v___x_4048_, v_visited_3992_);
v___y_4006_ = v___x_4049_;
goto v___jp_4005_;
}
else
{
v___y_4006_ = v_visited_3992_;
goto v___jp_4005_;
}
v___jp_4005_:
{
lean_object* v_result_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4046_; 
v_result_4007_ = lean_ctor_get(v_a_4004_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_a_4004_);
if (v_isSharedCheck_4046_ == 0)
{
lean_object* v_unused_4047_; 
v_unused_4047_ = lean_ctor_get(v_a_4004_, 0);
lean_dec(v_unused_4047_);
v___x_4009_ = v_a_4004_;
v_isShared_4010_ = v_isSharedCheck_4046_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_result_4007_);
lean_dec(v_a_4004_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4046_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4011_ = lean_unsigned_to_nat(1u);
v___x_4012_ = lean_nat_add(v_requestNo_3990_, v___x_4011_);
lean_dec(v_requestNo_3990_);
v___x_4013_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___x_4013_);
lean_ctor_set(v___x_4009_, 0, v___x_4012_);
v___x_4015_ = v___x_4009_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_4013_);
v___x_4015_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
size_t v_sz_4016_; size_t v___x_4017_; lean_object* v___x_4018_; 
v_sz_4016_ = lean_array_size(v_result_4007_);
v___x_4017_ = ((size_t)0ULL);
v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___y_4006_, v_result_4007_, v_sz_4016_, v___x_4017_, v___x_4015_, v_a_3993_);
lean_dec(v_result_4007_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4036_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4036_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4036_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_fst_4023_; lean_object* v_snd_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4035_; 
v_fst_4023_ = lean_ctor_get(v_a_4019_, 0);
v_snd_4024_ = lean_ctor_get(v_a_4019_, 1);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_a_4019_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4026_ = v_a_4019_;
v_isShared_4027_ = v_isSharedCheck_4035_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_snd_4024_);
lean_inc(v_fst_4023_);
lean_dec(v_a_4019_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4035_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4028_, 0, v_item_3991_);
lean_ctor_set(v___x_4028_, 1, v_snd_4024_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v_fst_4023_);
lean_ctor_set(v___x_4026_, 0, v___x_4028_);
v___x_4030_ = v___x_4026_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_fst_4023_);
v___x_4030_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4030_);
v___x_4032_ = v___x_4021_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec_ref(v_item_3991_);
v_a_4037_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4018_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4018_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
lean_dec(v_visited_3992_);
lean_dec_ref(v_item_3991_);
lean_dec(v_requestNo_3990_);
v_a_4050_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4003_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4003_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_dec_ref(v___x_3999_);
lean_dec(v_visited_3992_);
lean_dec_ref(v_item_3991_);
lean_dec(v_requestNo_3990_);
v_a_4058_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4002_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4002_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
lean_dec(v_visited_3992_);
v___x_4066_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4067_, 0, v_item_3991_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
lean_ctor_set(v___x_4068_, 1, v_requestNo_3990_);
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
return v___x_4069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object* v___x_4070_, lean_object* v_as_4071_, size_t v_sz_4072_, size_t v_i_4073_, lean_object* v_b_4074_, lean_object* v___y_4075_){
_start:
{
uint8_t v___x_4077_; 
v___x_4077_ = lean_usize_dec_lt(v_i_4073_, v_sz_4072_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
lean_dec(v___x_4070_);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_b_4074_);
return v___x_4078_;
}
else
{
lean_object* v_fst_4079_; lean_object* v_snd_4080_; lean_object* v_a_4081_; lean_object* v___x_4082_; 
v_fst_4079_ = lean_ctor_get(v_b_4074_, 0);
lean_inc(v_fst_4079_);
v_snd_4080_ = lean_ctor_get(v_b_4074_, 1);
lean_inc(v_snd_4080_);
lean_dec_ref(v_b_4074_);
v_a_4081_ = lean_array_uget_borrowed(v_as_4071_, v_i_4073_);
lean_inc(v___x_4070_);
lean_inc(v_a_4081_);
v___x_4082_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_fst_4079_, v_a_4081_, v___x_4070_, v___y_4075_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v_fst_4084_; lean_object* v_snd_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4096_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref(v___x_4082_);
v_fst_4084_ = lean_ctor_get(v_a_4083_, 0);
v_snd_4085_ = lean_ctor_get(v_a_4083_, 1);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_a_4083_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4087_ = v_a_4083_;
v_isShared_4088_ = v_isSharedCheck_4096_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_snd_4085_);
lean_inc(v_fst_4084_);
lean_dec(v_a_4083_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4096_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4089_; lean_object* v___x_4091_; 
v___x_4089_ = lean_array_push(v_snd_4080_, v_fst_4084_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 1, v___x_4089_);
lean_ctor_set(v___x_4087_, 0, v_snd_4085_);
v___x_4091_ = v___x_4087_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_snd_4085_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
size_t v___x_4092_; size_t v___x_4093_; 
v___x_4092_ = ((size_t)1ULL);
v___x_4093_ = lean_usize_add(v_i_4073_, v___x_4092_);
v_i_4073_ = v___x_4093_;
v_b_4074_ = v___x_4091_;
goto _start;
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_snd_4080_);
lean_dec(v___x_4070_);
v_a_4097_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4082_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4082_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object* v___x_4105_, lean_object* v_as_4106_, lean_object* v_sz_4107_, lean_object* v_i_4108_, lean_object* v_b_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
size_t v_sz_boxed_4112_; size_t v_i_boxed_4113_; lean_object* v_res_4114_; 
v_sz_boxed_4112_ = lean_unbox_usize(v_sz_4107_);
lean_dec(v_sz_4107_);
v_i_boxed_4113_ = lean_unbox_usize(v_i_4108_);
lean_dec(v_i_4108_);
v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_4105_, v_as_4106_, v_sz_boxed_4112_, v_i_boxed_4113_, v_b_4109_, v___y_4110_);
lean_dec_ref(v___y_4110_);
lean_dec_ref(v_as_4106_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object* v_requestNo_4115_, lean_object* v_item_4116_, lean_object* v_visited_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_requestNo_4115_, v_item_4116_, v_visited_4117_, v_a_4118_);
lean_dec_ref(v_a_4118_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object* v_requestNo_4121_, lean_object* v_uri_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_inc(v_requestNo_4121_);
v___x_4125_ = l_Lean_JsonNumber_fromNat(v_requestNo_4121_);
v___x_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
v___x_4127_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_4126_);
v___x_4128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4126_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
lean_ctor_set(v___x_4128_, 2, v_uri_4122_);
v___x_4129_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_4128_, v_a_4123_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v___x_4130_; 
lean_dec_ref(v___x_4129_);
v___x_4130_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_4126_, v_a_4123_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4189_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4133_ = v___x_4130_;
v_isShared_4134_ = v_isSharedCheck_4189_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4130_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4189_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v_result_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4187_; 
v_result_4135_ = lean_ctor_get(v_a_4131_, 1);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_a_4131_);
if (v_isSharedCheck_4187_ == 0)
{
lean_object* v_unused_4188_; 
v_unused_4188_ = lean_ctor_get(v_a_4131_, 0);
lean_dec(v_unused_4188_);
v___x_4137_ = v_a_4131_;
v_isShared_4138_ = v_isSharedCheck_4187_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_result_4135_);
lean_dec(v_a_4131_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4187_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_unsigned_to_nat(1u);
v___x_4140_ = lean_nat_add(v_requestNo_4121_, v___x_4139_);
lean_dec(v_requestNo_4121_);
if (lean_obj_tag(v_result_4135_) == 1)
{
lean_object* v_val_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4179_; 
lean_del_object(v___x_4133_);
v_val_4141_ = lean_ctor_get(v_result_4135_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v_result_4135_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4143_ = v_result_4135_;
v_isShared_4144_ = v_isSharedCheck_4179_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_val_4141_);
lean_dec(v_result_4135_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4179_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4145_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 1, v___x_4145_);
lean_ctor_set(v___x_4137_, 0, v_val_4141_);
v___x_4147_ = v___x_4137_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_val_4141_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_box(1);
v___x_4149_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v___x_4140_, v___x_4147_, v___x_4148_, v_a_4123_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4169_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4152_ = v___x_4149_;
v_isShared_4153_ = v_isSharedCheck_4169_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4149_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4169_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v_fst_4154_; lean_object* v_snd_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4168_; 
v_fst_4154_ = lean_ctor_get(v_a_4150_, 0);
v_snd_4155_ = lean_ctor_get(v_a_4150_, 1);
v_isSharedCheck_4168_ = !lean_is_exclusive(v_a_4150_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4157_ = v_a_4150_;
v_isShared_4158_ = v_isSharedCheck_4168_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_snd_4155_);
lean_inc(v_fst_4154_);
lean_dec(v_a_4150_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4168_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v_fst_4154_);
v___x_4160_ = v___x_4143_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_fst_4154_);
v___x_4160_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
lean_object* v___x_4162_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 0, v___x_4160_);
v___x_4162_ = v___x_4157_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v_snd_4155_);
v___x_4162_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
lean_object* v___x_4164_; 
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v___x_4162_);
v___x_4164_ = v___x_4152_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_del_object(v___x_4143_);
v_a_4170_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4149_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4149_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
}
else
{
lean_object* v___x_4180_; lean_object* v___x_4182_; 
lean_dec(v_result_4135_);
v___x_4180_ = lean_box(0);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 1, v___x_4140_);
lean_ctor_set(v___x_4137_, 0, v___x_4180_);
v___x_4182_ = v___x_4137_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___x_4140_);
v___x_4182_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
lean_object* v___x_4184_; 
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4182_);
v___x_4184_ = v___x_4133_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec(v_requestNo_4121_);
v_a_4190_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4130_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4130_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec_ref(v___x_4126_);
lean_dec(v_requestNo_4121_);
v_a_4198_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4129_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4129_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object* v_requestNo_4206_, lean_object* v_uri_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(v_requestNo_4206_, v_uri_4207_, v_a_4208_);
lean_dec_ref(v_a_4208_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* v_lean_4213_, lean_object* v_args_4214_, lean_object* v_test_4215_){
_start:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; uint8_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4217_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_4218_ = lean_box(0);
v___x_4219_ = ((lean_object*)(l_Lean_Lsp_Ipc_runWith___redArg___closed__0));
v___x_4220_ = 1;
v___x_4221_ = 0;
v___x_4222_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4222_, 0, v___x_4217_);
lean_ctor_set(v___x_4222_, 1, v_lean_4213_);
lean_ctor_set(v___x_4222_, 2, v_args_4214_);
lean_ctor_set(v___x_4222_, 3, v___x_4218_);
lean_ctor_set(v___x_4222_, 4, v___x_4219_);
lean_ctor_set_uint8(v___x_4222_, sizeof(void*)*5, v___x_4220_);
lean_ctor_set_uint8(v___x_4222_, sizeof(void*)*5 + 1, v___x_4221_);
v___x_4223_ = lean_io_process_spawn(v___x_4222_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4225_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4224_);
lean_dec_ref(v___x_4223_);
v___x_4225_ = lean_apply_2(v_test_4215_, v_a_4224_, lean_box(0));
return v___x_4225_;
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref(v_test_4215_);
v_a_4226_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4223_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4223_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object* v_lean_4234_, lean_object* v_args_4235_, lean_object* v_test_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4234_, v_args_4235_, v_test_4236_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* v_00_u03b1_4239_, lean_object* v_lean_4240_, lean_object* v_args_4241_, lean_object* v_test_4242_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4240_, v_args_4241_, v_test_4242_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object* v_00_u03b1_4245_, lean_object* v_lean_4246_, lean_object* v_args_4247_, lean_object* v_test_4248_, lean_object* v_a_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_Lsp_Ipc_runWith(v_00_u03b1_4245_, v_lean_4246_, v_args_4247_, v_test_4248_);
return v_res_4250_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Ipc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Ipc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Ipc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Ipc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Ipc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Ipc(builtin);
}
#ifdef __cplusplus
}
#endif
