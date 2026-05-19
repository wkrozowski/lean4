// Lean compiler output
// Module: Lake.Config.Cache
// Imports: import Init.Control.Do public import Lake.Util.Git public import Lake.Util.Log public import Lake.Util.Version public import Lake.Config.Artifact import Lake.Config.InstallPath import Lake.Build.Actions import Lake.Util.Url import Lake.Util.Proc import Lake.Util.Reservoir import Lake.Util.JsonObject import Lake.Util.IO import Init.System.Platform import Init.Data.String.Lemmas
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_lowerHexUInt64(uint64_t);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* l_Lake_JsonObject_insertJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Lake_Hash_ofJsonNumber_x3f(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* l_Lake_ArtifactDescr_ofFilePath_x3f(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Date_fromJson_x3f(lean_object*);
lean_object* l_Lake_Date_toString(lean_object*);
uint8_t l_Lake_instOrdDate_ord(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_io_remove_file(lean_object*);
lean_object* l_Lake_computeBinFileHash(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* lean_io_create_tempfile();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_io_metadata(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
extern lean_object* l_Lake_Reservoir_lakeHeaders;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_getUrl_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_rewind(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
extern lean_object* l_System_Platform_target;
lean_object* l_Lake_normalizeToolchain(lean_object*);
static const lean_ctor_object l_Lake_CacheMap_schemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2026) << 1) | 1)),((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lake_CacheMap_schemaVersion___closed__0 = (const lean_object*)&l_Lake_CacheMap_schemaVersion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheMap_schemaVersion = (const lean_object*)&l_Lake_CacheMap_schemaVersion___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = ": invalid header on line 1: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = ": unknown schema version '"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "'; may not parse correctly"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ": expected schema version on line 1"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected array of size > 0"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__0_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__0_value)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected array of size > 1"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__2_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__2_value)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": invalid JSON on line "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_CacheMap_parse___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_parse___closed__0;
static const lean_array_object l_Lake_CacheMap_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheMap_parse___closed__1 = (const lean_object*)&l_Lake_CacheMap_parse___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheMap_load___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": failed to open file: "};
static const lean_object* l_Lake_CacheMap_load___closed__0 = (const lean_object*)&l_Lake_CacheMap_load___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_CacheMap_writeFile___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_writeFile___closed__0;
static lean_once_cell_t l_Lake_CacheMap_writeFile___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_writeFile___closed__1;
static lean_once_cell_t l_Lake_CacheMap_writeFile___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheMap_writeFile___closed__2;
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unsupported output; "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "art"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unsupported output: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_CacheMap_collectOutputDescrs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheMap_collectOutputDescrs___closed__0 = (const lean_object*)&l_Lake_CacheMap_collectOutputDescrs___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object*, uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheServiceName_reservoir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reservoir"};
static const lean_object* l_Lake_CacheServiceName_reservoir___closed__0 = (const lean_object*)&l_Lake_CacheServiceName_reservoir___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceName_reservoir = (const lean_object*)&l_Lake_CacheServiceName_reservoir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_CacheServiceName_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceName_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceName_instToString___closed__0 = (const lean_object*)&l_Lake_CacheServiceName_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceName_instToString = (const lean_object*)&l_Lake_CacheServiceName_instToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instFromJson___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceName_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofRepo(lean_object*);
LEAN_EXPORT uint8_t l_Lake_CacheServiceScope_isRepo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_isRepo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_CacheServiceScope_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheServiceScope_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheServiceScope_instToString___closed__0 = (const lean_object*)&l_Lake_CacheServiceScope_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheServiceScope_instToString = (const lean_object*)&l_Lake_CacheServiceScope_instToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_instToJson___closed__0_value;
static const lean_string_object l_Lake_CacheOutput_schemaVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2026-02-25"};
static const lean_object* l_Lake_CacheOutput_schemaVersion___closed__0 = (const lean_object*)&l_Lake_CacheOutput_schemaVersion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheOutput_schemaVersion = (const lean_object*)&l_Lake_CacheOutput_schemaVersion___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedCacheOutput_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedCacheOutput_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedCacheOutput_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCacheOutput_default = (const lean_object*)&l_Lake_instInhabitedCacheOutput_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCacheOutput = (const lean_object*)&l_Lake_instInhabitedCacheOutput_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheOutput_ofData(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object*);
static const lean_string_object l_Lake_CacheOutput_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__0 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__0_value;
static const lean_string_object l_Lake_CacheOutput_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "schemaVersion"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__1 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__1_value;
static const lean_ctor_object l_Lake_CacheOutput_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_CacheOutput_schemaVersion___closed__0_value)}};
static const lean_object* l_Lake_CacheOutput_toJson___closed__2 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__2_value;
static lean_once_cell_t l_Lake_CacheOutput_toJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheOutput_toJson___closed__3;
static const lean_string_object l_Lake_CacheOutput_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "service"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__4 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__4_value;
static const lean_string_object l_Lake_CacheOutput_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "scope"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__5 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__5_value;
static const lean_string_object l_Lake_CacheOutput_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "repo"};
static const lean_object* l_Lake_CacheOutput_toJson___closed__6 = (const lean_object*)&l_Lake_CacheOutput_toJson___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_CacheOutput_toJson(lean_object*);
static const lean_closure_object l_Lake_CacheOutput_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheOutput_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheOutput_instToJson___closed__0 = (const lean_object*)&l_Lake_CacheOutput_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheOutput_instToJson = (const lean_object*)&l_Lake_CacheOutput_instToJson___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheOutput_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "property not found: data"};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Lake_CacheOutput_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__1_value;
static const lean_string_object l_Lake_CacheOutput_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scope: "};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__2 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__2_value;
static const lean_string_object l_Lake_CacheOutput_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repo: "};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__3 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__3_value;
static const lean_string_object l_Lake_CacheOutput_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "service: "};
static const lean_object* l_Lake_CacheOutput_fromJson_x3f___closed__4 = (const lean_object*)&l_Lake_CacheOutput_fromJson_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_CacheOutput_fromJson_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_CacheOutput_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheOutput_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_CacheOutput_instFromJson___closed__0 = (const lean_object*)&l_Lake_CacheOutput_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheOutput_instFromJson = (const lean_object*)&l_Lake_CacheOutput_instFromJson___closed__0_value;
static const lean_string_object l_Lake_instInhabitedCache_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedCache_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCache_default = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedCache = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
static const lean_string_object l_Lake_Cache_artifactDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "artifacts"};
static const lean_object* l_Lake_Cache_artifactDir___closed__0 = (const lean_object*)&l_Lake_Cache_artifactDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object*);
static const lean_string_object l_Lake_Cache_artifactPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_Cache_artifactPath___closed__0 = (const lean_object*)&l_Lake_Cache_artifactPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_getArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "artifact not found in cache: "};
static const lean_object* l_Lake_Cache_getArtifact___closed__0 = (const lean_object*)&l_Lake_Cache_getArtifact___closed__0_value;
static const lean_string_object l_Lake_Cache_getArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to retrieve artifact from cache: "};
static const lean_object* l_Lake_Cache_getArtifact___closed__1 = (const lean_object*)&l_Lake_Cache_getArtifact___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_outputsDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "outputs"};
static const lean_object* l_Lake_Cache_outputsDir___closed__0 = (const lean_object*)&l_Lake_Cache_outputsDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object*);
static const lean_string_object l_Lake_Cache_outputsFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".json"};
static const lean_object* l_Lake_Cache_outputsFile___closed__0 = (const lean_object*)&l_Lake_Cache_outputsFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object*);
static const lean_string_object l_Lake_Cache_readOutputs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ": invalid JSON: "};
static const lean_object* l_Lake_Cache_readOutputs_x3f___closed__0 = (const lean_object*)&l_Lake_Cache_readOutputs_x3f___closed__0_value;
static const lean_string_object l_Lake_Cache_readOutputs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ": read failed: "};
static const lean_object* l_Lake_Cache_readOutputs_x3f___closed__1 = (const lean_object*)&l_Lake_Cache_readOutputs_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Cache_revisionDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "revisions"};
static const lean_object* l_Lake_Cache_revisionDir___closed__0 = (const lean_object*)&l_Lake_Cache_revisionDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object*);
static const lean_string_object l_Lake_Cache_revisionPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ".jsonl"};
static const lean_object* l_Lake_Cache_revisionPath___closed__0 = (const lean_object*)&l_Lake_Cache_revisionPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lake_CachePlatform_none = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_system;
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CachePlatform_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lake_CachePlatform_toString___closed__0 = (const lean_object*)&l_Lake_CachePlatform_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CachePlatform_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CachePlatform_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheToolchain_none = (const lean_object*)&l_Lake_instInhabitedCache_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_CacheToolchain_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheToolchain_instToString___closed__0_value;
static const lean_array_object l_Lake_downloadArtifactCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_downloadArtifactCore___closed__0 = (const lean_object*)&l_Lake_downloadArtifactCore___closed__0_value;
static const lean_string_object l_Lake_downloadArtifactCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ": downloaded artifact hash mismatch, got "};
static const lean_object* l_Lake_downloadArtifactCore___closed__1 = (const lean_object*)&l_Lake_downloadArtifactCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "curl's JSON output contained an invalid JSON response code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "; JSON received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "curl's JSON output did not contain a response code; JSON received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "failed to upload artifact, error "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "; received:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "http_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "http_code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "curl produced invalid JSON output: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "curl"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-s"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-w"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "%{stderr}%{json}\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--aws-sigv4"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "aws:amz:auto:s3"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--user"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-X"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "PUT"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-T"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-H"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Content-Type: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26;
static const lean_array_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "response_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_artifactContentType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "application/vnd.reservoir.artifact"};
static const lean_object* l_Lake_CacheService_artifactContentType___closed__0 = (const lean_object*)&l_Lake_CacheService_artifactContentType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheService_artifactContentType = (const lean_object*)&l_Lake_CacheService_artifactContentType___closed__0_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".art"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_artifactUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "/artifacts/"};
static const lean_object* l_Lake_CacheService_artifactUrl___closed__0 = (const lean_object*)&l_Lake_CacheService_artifactUrl___closed__0_value;
static const lean_string_object l_Lake_CacheService_artifactUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "/packages"};
static const lean_object* l_Lake_CacheService_artifactUrl___closed__1 = (const lean_object*)&l_Lake_CacheService_artifactUrl___closed__1_value;
static const lean_string_object l_Lake_CacheService_artifactUrl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "/repositories"};
static const lean_object* l_Lake_CacheService_artifactUrl___closed__2 = (const lean_object*)&l_Lake_CacheService_artifactUrl___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_downloadArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = ": downloading artifact "};
static const lean_object* l_Lake_CacheService_downloadArtifact___closed__0 = (const lean_object*)&l_Lake_CacheService_downloadArtifact___closed__0_value;
static const lean_string_object l_Lake_CacheService_downloadArtifact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  local path: "};
static const lean_object* l_Lake_CacheService_downloadArtifact___closed__1 = (const lean_object*)&l_Lake_CacheService_downloadArtifact___closed__1_value;
static const lean_string_object l_Lake_CacheService_downloadArtifact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  remote URL: "};
static const lean_object* l_Lake_CacheService_downloadArtifact___closed__2 = (const lean_object*)&l_Lake_CacheService_downloadArtifact___closed__2_value;
static lean_once_cell_t l_Lake_CacheService_downloadArtifact___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_CacheService_downloadArtifact___closed__3;
static lean_once_cell_t l_Lake_CacheService_downloadArtifact___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_CacheService_downloadArtifact___closed__4;
static lean_once_cell_t l_Lake_CacheService_downloadArtifact___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_CacheService_downloadArtifact___closed__5;
static lean_once_cell_t l_Lake_CacheService_downloadArtifact___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_CacheService_downloadArtifact___closed__6;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadArtifact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ": uploading artifact "};
static const lean_object* l_Lake_CacheService_uploadArtifact___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadArtifact___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "urlnum"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "curl JSON: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "\nunexpected response:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "size_download"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "content_type"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "errormsg"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\n  curl error: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": failed to "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " artifact "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " (status code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "download"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "upload"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": downloaded artifact "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ": uploaded artifact "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = ": unidentifiable transfer completed: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "curl produced invalid JSON: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "; received: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "property not found: http_code"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__3_value)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "url = "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-o "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-T "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = ": curl exited with code "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = ": curl produced unexpected output:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " some artifacts"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-Z"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GET"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-L"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--retry"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--config"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Content-Type: application/vnd.reservoir.artifact"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "/artifacts"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(lean_object*);
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "property not found: status"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__3 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__3_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__3_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "status: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "property not found: message"};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__7 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__7_value;
static const lean_ctor_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__7_value)}};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8_value;
static const lean_string_object l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "message: "};
static const lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9 = (const lean_object*)&l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(lean_object*);
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "curl exited with code "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to fetch artifact URLs\n  POST "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\n          \nInvalid curl JSON: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "curl produced unexpected output:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "curl JSON:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nstdout:\n"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n  POST "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "\n  Transfer error: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "failed to fetch artifact URLs"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "failed to fetch artifact URLs (status code: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "\nIncorrect number of results: expected "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", got "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ")\n  POST "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "\nReservoir error: "};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "POST"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-d"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Content-Type: application/json"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17_value;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24;
static lean_once_cell_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_CacheService_downloadArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__0 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__0_value;
static const lean_string_object l_Lake_CacheService_downloadArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "no artifacts to download"};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__1 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__1_value;
static const lean_ctor_object l_Lake_CacheService_downloadArtifacts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheService_downloadArtifacts___closed__2 = (const lean_object*)&l_Lake_CacheService_downloadArtifacts___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no artifacts to upload"};
static const lean_object* l_Lake_CacheService_uploadArtifacts___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__0_value;
static const lean_ctor_object l_Lake_CacheService_uploadArtifacts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_CacheService_uploadArtifacts___closed__1 = (const lean_object*)&l_Lake_CacheService_uploadArtifacts___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_mapContentType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "application/vnd.reservoir.outputs+json-lines"};
static const lean_object* l_Lake_CacheService_mapContentType___closed__0 = (const lean_object*)&l_Lake_CacheService_mapContentType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_CacheService_mapContentType = (const lean_object*)&l_Lake_CacheService_mapContentType___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/tc/"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0_value;
static const lean_string_object l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "/pt/"};
static const lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1 = (const lean_object*)&l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_revisionUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "&toolchain="};
static const lean_object* l_Lake_CacheService_revisionUrl___closed__0 = (const lean_object*)&l_Lake_CacheService_revisionUrl___closed__0_value;
static const lean_string_object l_Lake_CacheService_revisionUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "/build-outputs\?rev="};
static const lean_object* l_Lake_CacheService_revisionUrl___closed__1 = (const lean_object*)&l_Lake_CacheService_revisionUrl___closed__1_value;
static const lean_string_object l_Lake_CacheService_revisionUrl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "&platform="};
static const lean_object* l_Lake_CacheService_revisionUrl___closed__2 = (const lean_object*)&l_Lake_CacheService_revisionUrl___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": output lookup failed"};
static const lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0 = (const lean_object*)&l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0_value;
static const lean_string_object l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ": downloading build outputs for revision "};
static const lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1 = (const lean_object*)&l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1_value;
static const lean_array_object l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2 = (const lean_object*)&l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_CacheService_uploadRevisionOutputs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = ": uploading build outputs for revision "};
static const lean_object* l_Lake_CacheService_uploadRevisionOutputs___closed__0 = (const lean_object*)&l_Lake_CacheService_uploadRevisionOutputs___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(lean_object* v_inputName_10_, lean_object* v_line_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_a_15_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_24_ = lean_string_utf8_byte_size(v_line_11_);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_nat_dec_eq(v___x_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Json_parse(v_line_11_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_28_);
lean_dec_ref(v___x_27_);
v_a_15_ = v_a_28_;
goto v___jp_14_;
}
else
{
lean_object* v_a_29_; lean_object* v___x_30_; 
v_a_29_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_29_);
lean_dec_ref(v___x_27_);
v___x_30_ = l_Lake_Date_fromJson_x3f(v_a_29_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v___x_30_);
v_a_15_ = v_a_31_;
goto v___jp_14_;
}
else
{
lean_object* v_a_32_; lean_object* v___x_45_; uint8_t v___x_46_; 
v_a_32_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_32_);
lean_dec_ref(v___x_30_);
v___x_45_ = ((lean_object*)(l_Lake_CacheMap_schemaVersion));
v___x_46_ = l_Lake_instOrdDate_ord(v_a_32_, v___x_45_);
if (v___x_46_ == 0)
{
goto v___jp_33_;
}
else
{
if (v___x_26_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_a_32_);
lean_dec_ref(v_inputName_10_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v_a_12_);
return v___x_48_;
}
else
{
goto v___jp_33_;
}
}
v___jp_33_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_34_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__1));
v___x_35_ = lean_string_append(v_inputName_10_, v___x_34_);
v___x_36_ = l_Lake_Date_toString(v_a_32_);
v___x_37_ = lean_string_append(v___x_35_, v___x_36_);
lean_dec_ref(v___x_36_);
v___x_38_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__2));
v___x_39_ = lean_string_append(v___x_37_, v___x_38_);
v___x_40_ = 2;
v___x_41_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_41_, 0, v___x_39_);
lean_ctor_set_uint8(v___x_41_, sizeof(void*)*1, v___x_40_);
v___x_42_ = lean_box(0);
v___x_43_ = lean_array_push(v_a_12_, v___x_41_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
return v___x_44_;
}
}
}
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec_ref(v_line_11_);
v___x_49_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__3));
v___x_50_ = lean_string_append(v_inputName_10_, v___x_49_);
v___x_51_ = 3;
v___x_52_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*1, v___x_51_);
v___x_53_ = lean_array_get_size(v_a_12_);
v___x_54_ = lean_array_push(v_a_12_, v___x_52_);
v___x_55_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
return v___x_55_;
}
v___jp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_16_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___closed__0));
v___x_17_ = lean_string_append(v_inputName_10_, v___x_16_);
v___x_18_ = lean_string_append(v___x_17_, v_a_15_);
lean_dec_ref(v_a_15_);
v___x_19_ = 2;
v___x_20_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_20_, 0, v___x_18_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*1, v___x_19_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_array_push(v_a_12_, v___x_20_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_21_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion___boxed(lean_object* v_inputName_56_, lean_object* v_line_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_56_, v_line_57_, v_a_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(uint64_t v_a_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
else
{
lean_object* v_key_64_; lean_object* v_tail_65_; uint64_t v___x_66_; uint8_t v___x_67_; 
v_key_64_ = lean_ctor_get(v_x_62_, 0);
v_tail_65_ = lean_ctor_get(v_x_62_, 2);
v___x_66_ = lean_unbox_uint64(v_key_64_);
v___x_67_ = lean_uint64_dec_eq(v___x_66_, v_a_61_);
if (v___x_67_ == 0)
{
v_x_62_ = v_tail_65_;
goto _start;
}
else
{
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg___boxed(lean_object* v_a_69_, lean_object* v_x_70_){
_start:
{
uint64_t v_a_boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_a_boxed_71_ = lean_unbox_uint64(v_a_69_);
lean_dec_ref(v_a_69_);
v_res_72_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_boxed_71_, v_x_70_);
lean_dec(v_x_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
return v_x_74_;
}
else
{
lean_object* v_key_76_; lean_object* v_value_77_; lean_object* v_tail_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_102_; 
v_key_76_ = lean_ctor_get(v_x_75_, 0);
v_value_77_ = lean_ctor_get(v_x_75_, 1);
v_tail_78_ = lean_ctor_get(v_x_75_, 2);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_102_ == 0)
{
v___x_80_ = v_x_75_;
v_isShared_81_ = v_isSharedCheck_102_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_tail_78_);
lean_inc(v_value_77_);
lean_inc(v_key_76_);
lean_dec(v_x_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_102_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v_fold_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_82_ = lean_array_get_size(v_x_74_);
v___x_83_ = 32ULL;
v___x_84_ = lean_unbox_uint64(v_key_76_);
v___x_85_ = lean_uint64_shift_right(v___x_84_, v___x_83_);
v___x_86_ = lean_unbox_uint64(v_key_76_);
v_fold_87_ = lean_uint64_xor(v___x_86_, v___x_85_);
v___x_88_ = 16ULL;
v___x_89_ = lean_uint64_shift_right(v_fold_87_, v___x_88_);
v___x_90_ = lean_uint64_xor(v_fold_87_, v___x_89_);
v___x_91_ = lean_uint64_to_usize(v___x_90_);
v___x_92_ = lean_usize_of_nat(v___x_82_);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_sub(v___x_92_, v___x_93_);
v___x_95_ = lean_usize_land(v___x_91_, v___x_94_);
v___x_96_ = lean_array_uget_borrowed(v_x_74_, v___x_95_);
lean_inc(v___x_96_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 2, v___x_96_);
v___x_98_ = v___x_80_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_key_76_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_value_77_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v___x_96_);
v___x_98_ = v_reuseFailAlloc_101_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; 
v___x_99_ = lean_array_uset(v_x_74_, v___x_95_, v___x_98_);
v_x_74_ = v___x_99_;
v_x_75_ = v_tail_78_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(lean_object* v_i_103_, lean_object* v_source_104_, lean_object* v_target_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_array_get_size(v_source_104_);
v___x_107_ = lean_nat_dec_lt(v_i_103_, v___x_106_);
if (v___x_107_ == 0)
{
lean_dec_ref(v_source_104_);
lean_dec(v_i_103_);
return v_target_105_;
}
else
{
lean_object* v_es_108_; lean_object* v___x_109_; lean_object* v_source_110_; lean_object* v_target_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_es_108_ = lean_array_fget(v_source_104_, v_i_103_);
v___x_109_ = lean_box(0);
v_source_110_ = lean_array_fset(v_source_104_, v_i_103_, v___x_109_);
v_target_111_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(v_target_105_, v_es_108_);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_add(v_i_103_, v___x_112_);
lean_dec(v_i_103_);
v_i_103_ = v___x_113_;
v_source_104_ = v_source_110_;
v_target_105_ = v_target_111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(lean_object* v_data_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_nbuckets_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_116_ = lean_array_get_size(v_data_115_);
v___x_117_ = lean_unsigned_to_nat(2u);
v_nbuckets_118_ = lean_nat_mul(v___x_116_, v___x_117_);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_box(0);
v___x_121_ = lean_mk_array(v_nbuckets_118_, v___x_120_);
v___x_122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(v___x_119_, v_data_115_, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(uint64_t v_a_123_, lean_object* v_b_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_dec(v_b_124_);
return v_x_125_;
}
else
{
lean_object* v_key_126_; lean_object* v_value_127_; lean_object* v_tail_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_142_; 
v_key_126_ = lean_ctor_get(v_x_125_, 0);
v_value_127_ = lean_ctor_get(v_x_125_, 1);
v_tail_128_ = lean_ctor_get(v_x_125_, 2);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_142_ == 0)
{
v___x_130_ = v_x_125_;
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_tail_128_);
lean_inc(v_value_127_);
lean_inc(v_key_126_);
lean_dec(v_x_125_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
uint64_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unbox_uint64(v_key_126_);
v___x_133_ = lean_uint64_dec_eq(v___x_132_, v_a_123_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(v_a_123_, v_b_124_, v_tail_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 2, v___x_134_);
v___x_136_ = v___x_130_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_key_126_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_value_127_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_dec(v_value_127_);
lean_dec(v_key_126_);
v___x_138_ = lean_box_uint64(v_a_123_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v_b_124_);
lean_ctor_set(v___x_130_, 0, v___x_138_);
v___x_140_ = v___x_130_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_b_124_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_tail_128_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg___boxed(lean_object* v_a_143_, lean_object* v_b_144_, lean_object* v_x_145_){
_start:
{
uint64_t v_a_boxed_146_; lean_object* v_res_147_; 
v_a_boxed_146_ = lean_unbox_uint64(v_a_143_);
lean_dec_ref(v_a_143_);
v_res_147_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(v_a_boxed_146_, v_b_144_, v_x_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(lean_object* v_m_148_, uint64_t v_a_149_, lean_object* v_b_150_){
_start:
{
lean_object* v_size_151_; lean_object* v_buckets_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_195_; 
v_size_151_ = lean_ctor_get(v_m_148_, 0);
v_buckets_152_ = lean_ctor_get(v_m_148_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_m_148_);
if (v_isSharedCheck_195_ == 0)
{
v___x_154_ = v_m_148_;
v_isShared_155_ = v_isSharedCheck_195_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_buckets_152_);
lean_inc(v_size_151_);
lean_dec(v_m_148_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_195_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v_fold_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v_bkt_168_; uint8_t v___x_169_; 
v___x_156_ = lean_array_get_size(v_buckets_152_);
v___x_157_ = 32ULL;
v___x_158_ = lean_uint64_shift_right(v_a_149_, v___x_157_);
v_fold_159_ = lean_uint64_xor(v_a_149_, v___x_158_);
v___x_160_ = 16ULL;
v___x_161_ = lean_uint64_shift_right(v_fold_159_, v___x_160_);
v___x_162_ = lean_uint64_xor(v_fold_159_, v___x_161_);
v___x_163_ = lean_uint64_to_usize(v___x_162_);
v___x_164_ = lean_usize_of_nat(v___x_156_);
v___x_165_ = ((size_t)1ULL);
v___x_166_ = lean_usize_sub(v___x_164_, v___x_165_);
v___x_167_ = lean_usize_land(v___x_163_, v___x_166_);
v_bkt_168_ = lean_array_uget_borrowed(v_buckets_152_, v___x_167_);
v___x_169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_149_, v_bkt_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v_size_x27_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_buckets_x27_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v_size_x27_171_ = lean_nat_add(v_size_151_, v___x_170_);
lean_dec(v_size_151_);
v___x_172_ = lean_box_uint64(v_a_149_);
lean_inc(v_bkt_168_);
v___x_173_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_b_150_);
lean_ctor_set(v___x_173_, 2, v_bkt_168_);
v_buckets_x27_174_ = lean_array_uset(v_buckets_152_, v___x_167_, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(4u);
v___x_176_ = lean_nat_mul(v_size_x27_171_, v___x_175_);
v___x_177_ = lean_unsigned_to_nat(3u);
v___x_178_ = lean_nat_div(v___x_176_, v___x_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_array_get_size(v_buckets_x27_174_);
v___x_180_ = lean_nat_dec_le(v___x_178_, v___x_179_);
lean_dec(v___x_178_);
if (v___x_180_ == 0)
{
lean_object* v_val_181_; lean_object* v___x_183_; 
v_val_181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(v_buckets_x27_174_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v_val_181_);
lean_ctor_set(v___x_154_, 0, v_size_x27_171_);
v___x_183_ = v___x_154_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_size_x27_171_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_val_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_object* v___x_186_; 
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v_buckets_x27_174_);
lean_ctor_set(v___x_154_, 0, v_size_x27_171_);
v___x_186_ = v___x_154_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_size_x27_171_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_buckets_x27_174_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v___x_188_; lean_object* v_buckets_x27_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
lean_inc(v_bkt_168_);
v___x_188_ = lean_box(0);
v_buckets_x27_189_ = lean_array_uset(v_buckets_152_, v___x_167_, v___x_188_);
v___x_190_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(v_a_149_, v_b_150_, v_bkt_168_);
v___x_191_ = lean_array_uset(v_buckets_x27_189_, v___x_167_, v___x_190_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_191_);
v___x_193_ = v___x_154_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_size_151_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg___boxed(lean_object* v_m_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
uint64_t v_a_boxed_199_; lean_object* v_res_200_; 
v_a_boxed_199_ = lean_unbox_uint64(v_a_197_);
lean_dec_ref(v_a_197_);
v_res_200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_m_196_, v_a_boxed_199_, v_b_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(size_t v_sz_201_, size_t v_i_202_, lean_object* v_bs_203_){
_start:
{
uint8_t v___x_204_; 
v___x_204_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v_bs_203_);
return v___x_205_;
}
else
{
lean_object* v_v_206_; lean_object* v___x_207_; lean_object* v_bs_x27_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v___x_211_; 
v_v_206_ = lean_array_uget(v_bs_203_, v_i_202_);
v___x_207_ = lean_unsigned_to_nat(0u);
v_bs_x27_208_ = lean_array_uset(v_bs_203_, v_i_202_, v___x_207_);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_i_202_, v___x_209_);
v___x_211_ = lean_array_uset(v_bs_x27_208_, v_i_202_, v_v_206_);
v_i_202_ = v___x_210_;
v_bs_203_ = v___x_211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0___boxed(lean_object* v_sz_213_, lean_object* v_i_214_, lean_object* v_bs_215_){
_start:
{
size_t v_sz_boxed_216_; size_t v_i_boxed_217_; lean_object* v_res_218_; 
v_sz_boxed_216_ = lean_unbox_usize(v_sz_213_);
lean_dec(v_sz_213_);
v_i_boxed_217_ = lean_unbox_usize(v_i_214_);
lean_dec(v_i_214_);
v_res_218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(v_sz_boxed_216_, v_i_boxed_217_, v_bs_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 4)
{
lean_object* v_elems_222_; size_t v_sz_223_; size_t v___x_224_; lean_object* v___x_225_; 
v_elems_222_ = lean_ctor_get(v_x_221_, 0);
lean_inc_ref(v_elems_222_);
lean_dec_ref(v_x_221_);
v_sz_223_ = lean_array_size(v_elems_222_);
v___x_224_ = ((size_t)0ULL);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0_spec__0(v_sz_223_, v___x_224_, v_elems_222_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_226_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0));
v___x_227_ = lean_unsigned_to_nat(80u);
v___x_228_ = l_Lean_Json_pretty(v_x_221_, v___x_227_);
v___x_229_ = lean_string_append(v___x_226_, v___x_228_);
lean_dec_ref(v___x_228_);
v___x_230_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1));
v___x_231_ = lean_string_append(v___x_229_, v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(lean_object* v_cache_239_, lean_object* v_line_240_, uint8_t v_platformIndependent_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Json_parse(v_line_240_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v_cache_239_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; 
v_a_251_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v___x_242_);
v___x_252_ = l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0(v_a_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec_ref(v_cache_239_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v___x_252_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_array_get_size(v_a_261_);
v___x_264_ = lean_nat_dec_lt(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_a_261_);
lean_dec_ref(v_cache_239_);
v___x_265_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__1));
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_array_fget_borrowed(v_a_261_, v___x_262_);
lean_inc(v___x_266_);
v___x_267_ = l_Lake_Hash_fromJson_x3f(v___x_266_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec(v_a_261_);
lean_dec_ref(v_cache_239_);
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_290_; 
v_a_276_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_290_ == 0)
{
v___x_278_ = v___x_267_;
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_267_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_290_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_dec_lt(v___x_280_, v___x_263_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; 
lean_del_object(v___x_278_);
lean_dec(v_a_276_);
lean_dec(v_a_261_);
lean_dec_ref(v_cache_239_);
v___x_282_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___closed__3));
return v___x_282_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; uint64_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_283_ = lean_array_fget(v_a_261_, v___x_280_);
lean_dec(v_a_261_);
v___x_284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*1, v_platformIndependent_241_);
v___x_285_ = lean_unbox_uint64(v_a_276_);
lean_dec(v_a_276_);
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_cache_239_, v___x_285_, v___x_284_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_286_);
v___x_288_ = v___x_278_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go___boxed(lean_object* v_cache_291_, lean_object* v_line_292_, lean_object* v_platformIndependent_293_){
_start:
{
uint8_t v_platformIndependent_boxed_294_; lean_object* v_res_295_; 
v_platformIndependent_boxed_294_ = lean_unbox(v_platformIndependent_293_);
v_res_295_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_291_, v_line_292_, v_platformIndependent_boxed_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1(lean_object* v_00_u03b2_296_, lean_object* v_m_297_, uint64_t v_a_298_, lean_object* v_b_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_m_297_, v_a_298_, v_b_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___boxed(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
uint64_t v_a_boxed_305_; lean_object* v_res_306_; 
v_a_boxed_305_ = lean_unbox_uint64(v_a_303_);
lean_dec_ref(v_a_303_);
v_res_306_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1(v_00_u03b2_301_, v_m_302_, v_a_boxed_305_, v_b_304_);
return v_res_306_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2(lean_object* v_00_u03b2_307_, uint64_t v_a_308_, lean_object* v_x_309_){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___redArg(v_a_308_, v_x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2___boxed(lean_object* v_00_u03b2_311_, lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
uint64_t v_a_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_a_boxed_314_ = lean_unbox_uint64(v_a_312_);
lean_dec_ref(v_a_312_);
v_res_315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__2(v_00_u03b2_311_, v_a_boxed_314_, v_x_313_);
lean_dec(v_x_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3(lean_object* v_00_u03b2_317_, lean_object* v_data_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3___redArg(v_data_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4(lean_object* v_00_u03b2_320_, uint64_t v_a_321_, lean_object* v_b_322_, lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___redArg(v_a_321_, v_b_322_, v_x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4___boxed(lean_object* v_00_u03b2_325_, lean_object* v_a_326_, lean_object* v_b_327_, lean_object* v_x_328_){
_start:
{
uint64_t v_a_boxed_329_; lean_object* v_res_330_; 
v_a_boxed_329_ = lean_unbox_uint64(v_a_326_);
lean_dec_ref(v_a_326_);
v_res_330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__4(v_00_u03b2_325_, v_a_boxed_329_, v_b_327_, v_x_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_331_, lean_object* v_i_332_, lean_object* v_source_333_, lean_object* v_target_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4___redArg(v_i_332_, v_source_333_, v_target_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1_spec__3_spec__4_spec__5___redArg(v_x_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___lam__0(lean_object* v_toPure_340_, lean_object* v_cache_341_, lean_object* v_____r_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_apply_2(v_toPure_340_, lean_box(0), v_cache_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg(lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inputName_348_, lean_object* v_lineNo_349_, lean_object* v_cache_350_, lean_object* v_line_351_, uint8_t v_platformIndependent_352_){
_start:
{
lean_object* v_toApplicative_353_; lean_object* v_toBind_354_; lean_object* v_toPure_355_; lean_object* v___x_356_; 
v_toApplicative_353_ = lean_ctor_get(v_inst_346_, 0);
lean_inc_ref(v_toApplicative_353_);
v_toBind_354_ = lean_ctor_get(v_inst_346_, 1);
lean_inc(v_toBind_354_);
lean_dec_ref(v_inst_346_);
v_toPure_355_ = lean_ctor_get(v_toApplicative_353_, 1);
lean_inc(v_toPure_355_);
lean_dec_ref(v_toApplicative_353_);
lean_inc_ref(v_cache_350_);
v___x_356_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_350_, v_line_351_, v_platformIndependent_352_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v___x_356_);
v___f_358_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___lam__0), 3, 2);
lean_closure_set(v___f_358_, 0, v_toPure_355_);
lean_closure_set(v___f_358_, 1, v_cache_350_);
v___x_359_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0));
v___x_360_ = lean_string_append(v_inputName_348_, v___x_359_);
v___x_361_ = l_Nat_reprFast(v_lineNo_349_);
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
lean_dec_ref(v___x_361_);
v___x_363_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_364_ = lean_string_append(v___x_362_, v___x_363_);
v___x_365_ = lean_string_append(v___x_364_, v_a_357_);
lean_dec(v_a_357_);
v___x_366_ = 2;
v___x_367_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_366_);
v___x_368_ = lean_apply_1(v_inst_347_, v___x_367_);
v___x_369_ = lean_apply_4(v_toBind_354_, lean_box(0), lean_box(0), v___x_368_, v___f_358_);
return v___x_369_;
}
else
{
lean_object* v_a_370_; lean_object* v___x_371_; 
lean_dec(v_toBind_354_);
lean_dec_ref(v_cache_350_);
lean_dec(v_lineNo_349_);
lean_dec_ref(v_inputName_348_);
lean_dec(v_inst_347_);
v_a_370_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_356_);
v___x_371_ = lean_apply_2(v_toPure_355_, lean_box(0), v_a_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___boxed(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inputName_374_, lean_object* v_lineNo_375_, lean_object* v_cache_376_, lean_object* v_line_377_, lean_object* v_platformIndependent_378_){
_start:
{
uint8_t v_platformIndependent_boxed_379_; lean_object* v_res_380_; 
v_platformIndependent_boxed_379_ = lean_unbox(v_platformIndependent_378_);
v_res_380_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg(v_inst_372_, v_inst_373_, v_inputName_374_, v_lineNo_375_, v_cache_376_, v_line_377_, v_platformIndependent_boxed_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry(lean_object* v_m_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_inputName_384_, lean_object* v_lineNo_385_, lean_object* v_cache_386_, lean_object* v_line_387_, uint8_t v_platformIndependent_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg(v_inst_382_, v_inst_383_, v_inputName_384_, v_lineNo_385_, v_cache_386_, v_line_387_, v_platformIndependent_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___boxed(lean_object* v_m_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inputName_393_, lean_object* v_lineNo_394_, lean_object* v_cache_395_, lean_object* v_line_396_, lean_object* v_platformIndependent_397_){
_start:
{
uint8_t v_platformIndependent_boxed_398_; lean_object* v_res_399_; 
v_platformIndependent_boxed_398_ = lean_unbox(v_platformIndependent_397_);
v_res_399_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry(v_m_390_, v_inst_391_, v_inst_392_, v_inputName_393_, v_lineNo_394_, v_cache_395_, v_line_396_, v_platformIndependent_boxed_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(lean_object* v_inputName_400_, lean_object* v_lineNo_401_, lean_object* v_cache_402_, lean_object* v_line_403_, uint8_t v_platformIndependent_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
lean_inc_ref(v_cache_402_);
v___x_407_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_402_, v_line_403_, v_platformIndependent_404_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_425_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_425_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_425_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_425_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_412_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0));
v___x_413_ = lean_string_append(v_inputName_400_, v___x_412_);
v___x_414_ = l_Nat_reprFast(v_lineNo_401_);
v___x_415_ = lean_string_append(v___x_413_, v___x_414_);
lean_dec_ref(v___x_414_);
v___x_416_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
v___x_418_ = lean_string_append(v___x_417_, v_a_408_);
lean_dec(v_a_408_);
v___x_419_ = 2;
v___x_420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
lean_inc_ref(v___y_405_);
v___x_421_ = lean_apply_2(v___y_405_, v___x_420_, lean_box(0));
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_cache_402_);
v___x_423_ = v___x_410_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_cache_402_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v_cache_402_);
lean_dec(v_lineNo_401_);
lean_dec_ref(v_inputName_400_);
v_a_426_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_407_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_407_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 0);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0___boxed(lean_object* v_inputName_434_, lean_object* v_lineNo_435_, lean_object* v_cache_436_, lean_object* v_line_437_, lean_object* v_platformIndependent_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_platformIndependent_boxed_441_; lean_object* v_res_442_; 
v_platformIndependent_boxed_441_ = lean_unbox(v_platformIndependent_438_);
v_res_442_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_inputName_434_, v_lineNo_435_, v_cache_436_, v_line_437_, v_platformIndependent_boxed_441_, v___y_439_);
lean_dec_ref(v___y_439_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v_contents_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_startInclusive_448_; lean_object* v_endExclusive_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_startInclusive_448_ = lean_ctor_get(v___x_443_, 1);
v_endExclusive_449_ = lean_ctor_get(v___x_443_, 2);
v___x_450_ = lean_nat_sub(v_endExclusive_449_, v_startInclusive_448_);
v___x_451_ = lean_nat_dec_eq(v_a_446_, v___x_450_);
lean_dec(v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint32_t v___x_453_; uint32_t v___x_454_; uint8_t v___x_455_; 
v___x_452_ = lean_nat_add(v___x_444_, v_a_446_);
v___x_453_ = lean_string_utf8_get_fast(v_contents_445_, v___x_452_);
v___x_454_ = 10;
v___x_455_ = lean_uint32_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_a_446_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_string_utf8_next_fast(v_contents_445_, v___x_452_);
lean_dec(v___x_452_);
v___x_458_ = lean_nat_sub(v___x_457_, v___x_444_);
v_a_446_ = v___x_458_;
v_b_447_ = v___x_456_;
goto _start;
}
else
{
lean_object* v___x_460_; 
lean_dec(v___x_452_);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v_a_446_);
return v___x_460_;
}
}
else
{
lean_dec(v_a_446_);
lean_inc(v_b_447_);
return v_b_447_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg___boxed(lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_contents_463_, lean_object* v_a_464_, lean_object* v_b_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_461_, v___x_462_, v_contents_463_, v_a_464_, v_b_465_);
lean_dec(v_b_465_);
lean_dec_ref(v_contents_463_);
lean_dec(v___x_462_);
lean_dec_ref(v___x_461_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(lean_object* v_a_467_, lean_object* v_inputName_468_, uint8_t v_platformIndependent_469_, lean_object* v_i_470_, lean_object* v_cache_471_, lean_object* v_contents_472_, lean_object* v_pos_473_){
_start:
{
lean_object* v___y_476_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_searcher_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_495_ = lean_string_utf8_byte_size(v_contents_472_);
lean_inc(v_pos_473_);
lean_inc_ref(v_contents_472_);
v___x_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_496_, 0, v_contents_472_);
lean_ctor_set(v___x_496_, 1, v_pos_473_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v_searcher_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_box(0);
v___x_499_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_496_, v_pos_473_, v_contents_472_, v_searcher_497_, v___x_498_);
lean_dec_ref(v___x_496_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_nat_sub(v___x_495_, v_pos_473_);
v___y_476_ = v___x_500_;
goto v___jp_475_;
}
else
{
lean_object* v_val_501_; 
v_val_501_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_501_);
lean_dec_ref(v___x_499_);
v___y_476_ = v_val_501_;
goto v___jp_475_;
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v_line_478_; lean_object* v___x_479_; lean_object* v_startInclusive_480_; lean_object* v_endExclusive_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_477_ = lean_nat_add(v_pos_473_, v___y_476_);
lean_dec(v___y_476_);
lean_inc(v___x_477_);
lean_inc(v_pos_473_);
lean_inc_ref(v_contents_472_);
v_line_478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_478_, 0, v_contents_472_);
lean_ctor_set(v_line_478_, 1, v_pos_473_);
lean_ctor_set(v_line_478_, 2, v___x_477_);
v___x_479_ = l_String_Slice_trimAscii(v_line_478_);
v_startInclusive_480_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_startInclusive_480_);
v_endExclusive_481_ = lean_ctor_get(v___x_479_, 2);
lean_inc(v_endExclusive_481_);
lean_dec_ref(v___x_479_);
v___x_482_ = lean_nat_sub(v_endExclusive_481_, v_startInclusive_480_);
lean_dec(v_startInclusive_480_);
lean_dec(v_endExclusive_481_);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_nat_dec_eq(v___x_482_, v___x_483_);
lean_dec(v___x_482_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_string_utf8_extract(v_contents_472_, v_pos_473_, v___x_477_);
lean_dec(v_pos_473_);
lean_inc(v_i_470_);
lean_inc_ref(v_inputName_468_);
v___x_486_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_inputName_468_, v_i_470_, v_cache_471_, v___x_485_, v_platformIndependent_469_, v_a_467_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
v___x_488_ = lean_string_utf8_byte_size(v_contents_472_);
v___x_489_ = lean_nat_dec_eq(v___x_477_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v___x_486_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_i_470_, v___x_490_);
lean_dec(v_i_470_);
v___x_492_ = lean_string_utf8_next_fast(v_contents_472_, v___x_477_);
lean_dec(v___x_477_);
v_i_470_ = v___x_491_;
v_cache_471_ = v_a_487_;
v_pos_473_ = v___x_492_;
goto _start;
}
else
{
lean_dec(v_a_487_);
lean_dec(v___x_477_);
lean_dec_ref(v_contents_472_);
lean_dec(v_i_470_);
lean_dec_ref(v_inputName_468_);
return v___x_486_;
}
}
else
{
lean_dec(v___x_477_);
lean_dec_ref(v_contents_472_);
lean_dec(v_i_470_);
lean_dec_ref(v_inputName_468_);
return v___x_486_;
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v___x_477_);
lean_dec(v_pos_473_);
lean_dec_ref(v_contents_472_);
lean_dec(v_i_470_);
lean_dec_ref(v_inputName_468_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_cache_471_);
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1___boxed(lean_object* v_a_502_, lean_object* v_inputName_503_, lean_object* v_platformIndependent_504_, lean_object* v_i_505_, lean_object* v_cache_506_, lean_object* v_contents_507_, lean_object* v_pos_508_, lean_object* v_a_509_){
_start:
{
uint8_t v_platformIndependent_boxed_510_; lean_object* v_res_511_; 
v_platformIndependent_boxed_510_ = lean_unbox(v_platformIndependent_504_);
v_res_511_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_502_, v_inputName_503_, v_platformIndependent_boxed_510_, v_i_505_, v_cache_506_, v_contents_507_, v_pos_508_);
lean_dec_ref(v_a_502_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v_contents_514_, lean_object* v_a_515_, lean_object* v_b_516_){
_start:
{
lean_object* v_startInclusive_517_; lean_object* v_endExclusive_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_startInclusive_517_ = lean_ctor_get(v___x_512_, 1);
v_endExclusive_518_ = lean_ctor_get(v___x_512_, 2);
v___x_519_ = lean_nat_sub(v_endExclusive_518_, v_startInclusive_517_);
v___x_520_ = lean_nat_dec_eq(v_a_515_, v___x_519_);
lean_dec(v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint32_t v___x_522_; uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_521_ = lean_nat_add(v___x_513_, v_a_515_);
v___x_522_ = lean_string_utf8_get_fast(v_contents_514_, v___x_521_);
v___x_523_ = 10;
v___x_524_ = lean_uint32_dec_eq(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_a_515_);
v___x_525_ = lean_box(0);
v___x_526_ = lean_string_utf8_next_fast(v_contents_514_, v___x_521_);
lean_dec(v___x_521_);
v___x_527_ = lean_nat_sub(v___x_526_, v___x_513_);
v_a_515_ = v___x_527_;
v_b_516_ = v___x_525_;
goto _start;
}
else
{
lean_object* v___x_529_; 
lean_dec(v___x_521_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_a_515_);
return v___x_529_;
}
}
else
{
lean_dec(v_a_515_);
lean_inc(v_b_516_);
return v_b_516_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg___boxed(lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v_contents_532_, lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_530_, v___x_531_, v_contents_532_, v_a_533_, v_b_534_);
lean_dec(v_b_534_);
lean_dec_ref(v_contents_532_);
lean_dec(v___x_531_);
lean_dec_ref(v___x_530_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(lean_object* v_inputName_536_, uint8_t v_platformIndependent_537_, lean_object* v_i_538_, lean_object* v_cache_539_, lean_object* v_contents_540_, lean_object* v_pos_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___y_545_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_searcher_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_564_ = lean_string_utf8_byte_size(v_contents_540_);
lean_inc(v_pos_541_);
lean_inc_ref(v_contents_540_);
v___x_565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_565_, 0, v_contents_540_);
lean_ctor_set(v___x_565_, 1, v_pos_541_);
lean_ctor_set(v___x_565_, 2, v___x_564_);
v_searcher_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_box(0);
v___x_568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_565_, v_pos_541_, v_contents_540_, v_searcher_566_, v___x_567_);
lean_dec_ref(v___x_565_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_nat_sub(v___x_564_, v_pos_541_);
v___y_545_ = v___x_569_;
goto v___jp_544_;
}
else
{
lean_object* v_val_570_; 
v_val_570_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_val_570_);
lean_dec_ref(v___x_568_);
v___y_545_ = v_val_570_;
goto v___jp_544_;
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v_line_547_; lean_object* v___x_548_; lean_object* v_startInclusive_549_; lean_object* v_endExclusive_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_546_ = lean_nat_add(v_pos_541_, v___y_545_);
lean_dec(v___y_545_);
lean_inc(v___x_546_);
lean_inc(v_pos_541_);
lean_inc_ref(v_contents_540_);
v_line_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_547_, 0, v_contents_540_);
lean_ctor_set(v_line_547_, 1, v_pos_541_);
lean_ctor_set(v_line_547_, 2, v___x_546_);
v___x_548_ = l_String_Slice_trimAscii(v_line_547_);
v_startInclusive_549_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_startInclusive_549_);
v_endExclusive_550_ = lean_ctor_get(v___x_548_, 2);
lean_inc(v_endExclusive_550_);
lean_dec_ref(v___x_548_);
v___x_551_ = lean_nat_sub(v_endExclusive_550_, v_startInclusive_549_);
lean_dec(v_startInclusive_549_);
lean_dec(v_endExclusive_550_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_nat_dec_eq(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_string_utf8_extract(v_contents_540_, v_pos_541_, v___x_546_);
lean_dec(v_pos_541_);
lean_inc(v_i_538_);
lean_inc_ref(v_inputName_536_);
v___x_555_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__0(v_inputName_536_, v_i_538_, v_cache_539_, v___x_554_, v_platformIndependent_537_, v_a_542_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
v___x_557_ = lean_string_utf8_byte_size(v_contents_540_);
v___x_558_ = lean_nat_dec_eq(v___x_546_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v___x_555_);
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_add(v_i_538_, v___x_559_);
lean_dec(v_i_538_);
v___x_561_ = lean_string_utf8_next_fast(v_contents_540_, v___x_546_);
lean_dec(v___x_546_);
v___x_562_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_542_, v_inputName_536_, v_platformIndependent_537_, v___x_560_, v_a_556_, v_contents_540_, v___x_561_);
return v___x_562_;
}
else
{
lean_dec(v_a_556_);
lean_dec(v___x_546_);
lean_dec_ref(v_contents_540_);
lean_dec(v_i_538_);
lean_dec_ref(v_inputName_536_);
return v___x_555_;
}
}
else
{
lean_dec(v___x_546_);
lean_dec_ref(v_contents_540_);
lean_dec(v_i_538_);
lean_dec_ref(v_inputName_536_);
return v___x_555_;
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v___x_546_);
lean_dec(v_pos_541_);
lean_dec_ref(v_contents_540_);
lean_dec(v_i_538_);
lean_dec_ref(v_inputName_536_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v_cache_539_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___boxed(lean_object* v_inputName_571_, lean_object* v_platformIndependent_572_, lean_object* v_i_573_, lean_object* v_cache_574_, lean_object* v_contents_575_, lean_object* v_pos_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
uint8_t v_platformIndependent_boxed_579_; lean_object* v_res_580_; 
v_platformIndependent_boxed_579_ = lean_unbox(v_platformIndependent_572_);
v_res_580_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop(v_inputName_571_, v_platformIndependent_boxed_579_, v_i_573_, v_cache_574_, v_contents_575_, v_pos_576_, v_a_577_);
lean_dec_ref(v_a_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(lean_object* v___x_581_, lean_object* v___x_582_, lean_object* v_contents_583_, lean_object* v_inst_584_, lean_object* v_R_585_, lean_object* v_a_586_, lean_object* v_b_587_, lean_object* v_c_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___redArg(v___x_581_, v___x_582_, v_contents_583_, v_a_586_, v_b_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2___boxed(lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v_contents_592_, lean_object* v_inst_593_, lean_object* v_R_594_, lean_object* v_a_595_, lean_object* v_b_596_, lean_object* v_c_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__2(v___x_590_, v___x_591_, v_contents_592_, v_inst_593_, v_R_594_, v_a_595_, v_b_596_, v_c_597_);
lean_dec(v_b_596_);
lean_dec_ref(v_contents_592_);
lean_dec(v___x_591_);
lean_dec_ref(v___x_590_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v_contents_601_, lean_object* v_inst_602_, lean_object* v_R_603_, lean_object* v_a_604_, lean_object* v_b_605_, lean_object* v_c_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___redArg(v___x_599_, v___x_600_, v_contents_601_, v_a_604_, v_b_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1___boxed(lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v_contents_610_, lean_object* v_inst_611_, lean_object* v_R_612_, lean_object* v_a_613_, lean_object* v_b_614_, lean_object* v_c_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1_spec__1(v___x_608_, v___x_609_, v_contents_610_, v_inst_611_, v_R_612_, v_a_613_, v_b_614_, v_c_615_);
lean_dec(v_b_614_);
lean_dec_ref(v_contents_610_);
lean_dec(v___x_609_);
lean_dec_ref(v___x_608_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(lean_object* v_as_617_, size_t v_i_618_, size_t v_stop_619_, lean_object* v_b_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_eq(v_i_618_, v_stop_619_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; size_t v___x_626_; size_t v___x_627_; 
v___x_624_ = lean_array_uget_borrowed(v_as_617_, v_i_618_);
lean_inc_ref(v___y_621_);
lean_inc(v___x_624_);
v___x_625_ = lean_apply_2(v___y_621_, v___x_624_, lean_box(0));
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_add(v_i_618_, v___x_626_);
v_i_618_ = v___x_627_;
v_b_620_ = v___x_625_;
goto _start;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_620_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0___boxed(lean_object* v_as_630_, lean_object* v_i_631_, lean_object* v_stop_632_, lean_object* v_b_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; lean_object* v_res_638_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_632_);
lean_dec(v_stop_632_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_as_630_, v_i_boxed_636_, v_stop_boxed_637_, v_b_633_, v___y_634_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v_as_630_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(lean_object* v___x_639_, lean_object* v_contents_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v_startInclusive_643_; lean_object* v_endExclusive_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_startInclusive_643_ = lean_ctor_get(v___x_639_, 1);
v_endExclusive_644_ = lean_ctor_get(v___x_639_, 2);
v___x_645_ = lean_nat_sub(v_endExclusive_644_, v_startInclusive_643_);
v___x_646_ = lean_nat_dec_eq(v_a_641_, v___x_645_);
lean_dec(v___x_645_);
if (v___x_646_ == 0)
{
uint32_t v___x_647_; uint32_t v___x_648_; uint8_t v___x_649_; 
v___x_647_ = lean_string_utf8_get_fast(v_contents_640_, v_a_641_);
v___x_648_ = 10;
v___x_649_ = lean_uint32_dec_eq(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_box(0);
v___x_651_ = lean_string_utf8_next_fast(v_contents_640_, v_a_641_);
lean_dec(v_a_641_);
v_a_641_ = v___x_651_;
v_b_642_ = v___x_650_;
goto _start;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_653_, 0, v_a_641_);
return v___x_653_;
}
}
else
{
lean_dec(v_a_641_);
lean_inc(v_b_642_);
return v_b_642_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg___boxed(lean_object* v___x_654_, lean_object* v_contents_655_, lean_object* v_a_656_, lean_object* v_b_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_654_, v_contents_655_, v_a_656_, v_b_657_);
lean_dec(v_b_657_);
lean_dec_ref(v_contents_655_);
lean_dec_ref(v___x_654_);
return v_res_658_;
}
}
static lean_object* _init_l_Lake_CacheMap_parse___closed__0(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_box(0);
v___x_660_ = lean_unsigned_to_nat(16u);
v___x_661_ = lean_mk_array(v___x_660_, v___x_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse(lean_object* v_inputName_664_, lean_object* v_contents_665_, uint8_t v_platformIndependent_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___y_687_; lean_object* v___y_688_; lean_object* v___y_698_; lean_object* v_searcher_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_searcher_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_string_utf8_byte_size(v_contents_665_);
lean_inc_ref(v_contents_665_);
v___x_736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_736_, 0, v_contents_665_);
lean_ctor_set(v___x_736_, 1, v_searcher_734_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v___x_737_ = lean_box(0);
v___x_738_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_736_, v_contents_665_, v_searcher_734_, v___x_737_);
lean_dec_ref(v___x_736_);
if (lean_obj_tag(v___x_738_) == 0)
{
v___y_698_ = v___x_735_;
goto v___jp_697_;
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref(v___x_738_);
v___y_698_ = v_val_739_;
goto v___jp_697_;
}
v___jp_669_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(0);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
v___jp_672_:
{
if (v___y_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_676_ = lean_unsigned_to_nat(2u);
v___x_677_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___y_674_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_string_utf8_next_fast(v_contents_665_, v___y_673_);
lean_dec(v___y_673_);
v___x_680_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parse_loop_spec__1(v_a_667_, v_inputName_664_, v_platformIndependent_666_, v___x_676_, v___x_678_, v_contents_665_, v___x_679_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v___y_673_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
v___x_681_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_674_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
v___jp_684_:
{
if (lean_obj_tag(v___y_688_) == 0)
{
lean_dec_ref(v___y_688_);
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
goto v___jp_672_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
v_a_689_ = lean_ctor_get(v___y_688_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___y_688_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___y_688_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___y_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v_line_700_; lean_object* v___x_701_; lean_object* v_str_702_; lean_object* v_startInclusive_703_; lean_object* v_endExclusive_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_699_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_698_);
lean_inc_ref(v_contents_665_);
v_line_700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_line_700_, 0, v_contents_665_);
lean_ctor_set(v_line_700_, 1, v___x_699_);
lean_ctor_set(v_line_700_, 2, v___y_698_);
v___x_701_ = l_String_Slice_trimAscii(v_line_700_);
v_str_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc_ref(v_str_702_);
v_startInclusive_703_ = lean_ctor_get(v___x_701_, 1);
lean_inc(v_startInclusive_703_);
v_endExclusive_704_ = lean_ctor_get(v___x_701_, 2);
lean_inc(v_endExclusive_704_);
lean_dec_ref(v___x_701_);
v___x_705_ = lean_string_utf8_extract(v_str_702_, v_startInclusive_703_, v_endExclusive_704_);
lean_dec(v_endExclusive_704_);
lean_dec(v_startInclusive_703_);
lean_dec_ref(v_str_702_);
v___x_706_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
lean_inc_ref(v_inputName_664_);
v___x_707_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_inputName_664_, v___x_705_, v___x_706_);
v___x_708_ = lean_string_utf8_byte_size(v_contents_665_);
v___x_709_ = lean_nat_dec_eq(v___y_698_, v___x_708_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_a_710_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_a_710_);
lean_dec_ref(v___x_707_);
v___x_711_ = lean_array_get_size(v_a_710_);
v___x_712_ = lean_nat_dec_lt(v___x_699_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec(v_a_710_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_699_;
v___y_675_ = v___x_709_;
goto v___jp_672_;
}
else
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_nat_dec_le(v___x_711_, v___x_711_);
if (v___x_714_ == 0)
{
if (v___x_712_ == 0)
{
lean_dec(v_a_710_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_699_;
v___y_675_ = v___x_709_;
goto v___jp_672_;
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v___x_715_ = ((size_t)0ULL);
v___x_716_ = lean_usize_of_nat(v___x_711_);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_710_, v___x_715_, v___x_716_, v___x_713_, v_a_667_);
lean_dec(v_a_710_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_dec_ref(v___x_717_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_699_;
v___y_675_ = v___x_709_;
goto v___jp_672_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___x_699_;
v___y_687_ = v___x_709_;
v___y_688_ = v___x_717_;
goto v___jp_684_;
}
}
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = ((size_t)0ULL);
v___x_719_ = lean_usize_of_nat(v___x_711_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_710_, v___x_718_, v___x_719_, v___x_713_, v_a_667_);
lean_dec(v_a_710_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_dec_ref(v___x_720_);
v___y_673_ = v___y_698_;
v___y_674_ = v___x_699_;
v___y_675_ = v___x_709_;
goto v___jp_672_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___x_699_;
v___y_687_ = v___x_709_;
v___y_688_ = v___x_720_;
goto v___jp_684_;
}
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_a_721_ = lean_ctor_get(v___x_707_, 1);
lean_inc(v_a_721_);
lean_dec_ref(v___x_707_);
v___x_722_ = lean_array_get_size(v_a_721_);
v___x_723_ = lean_nat_dec_lt(v___x_699_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v_a_721_);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = lean_box(0);
v___x_727_ = lean_nat_dec_le(v___x_722_, v___x_722_);
if (v___x_727_ == 0)
{
if (v___x_723_ == 0)
{
lean_dec(v_a_721_);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((size_t)0ULL);
v___x_729_ = lean_usize_of_nat(v___x_722_);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_721_, v___x_728_, v___x_729_, v___x_726_, v_a_667_);
lean_dec(v_a_721_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_dec_ref(v___x_730_);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___x_699_;
v___y_687_ = v___x_709_;
v___y_688_ = v___x_730_;
goto v___jp_684_;
}
}
}
else
{
size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
v___x_731_ = ((size_t)0ULL);
v___x_732_ = lean_usize_of_nat(v___x_722_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_721_, v___x_731_, v___x_732_, v___x_726_, v_a_667_);
lean_dec(v_a_721_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_dec_ref(v___x_733_);
lean_dec(v___y_698_);
lean_dec_ref(v_contents_665_);
lean_dec_ref(v_inputName_664_);
goto v___jp_669_;
}
else
{
v___y_685_ = v___y_698_;
v___y_686_ = v___x_699_;
v___y_687_ = v___x_709_;
v___y_688_ = v___x_733_;
goto v___jp_684_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_parse___boxed(lean_object* v_inputName_740_, lean_object* v_contents_741_, lean_object* v_platformIndependent_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
uint8_t v_platformIndependent_boxed_745_; lean_object* v_res_746_; 
v_platformIndependent_boxed_745_ = lean_unbox(v_platformIndependent_742_);
v_res_746_ = l_Lake_CacheMap_parse(v_inputName_740_, v_contents_741_, v_platformIndependent_boxed_745_, v_a_743_);
lean_dec_ref(v_a_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(lean_object* v___x_747_, lean_object* v_contents_748_, lean_object* v_inst_749_, lean_object* v_R_750_, lean_object* v_a_751_, lean_object* v_b_752_, lean_object* v_c_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___redArg(v___x_747_, v_contents_748_, v_a_751_, v_b_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1___boxed(lean_object* v___x_755_, lean_object* v_contents_756_, lean_object* v_inst_757_, lean_object* v_R_758_, lean_object* v_a_759_, lean_object* v_b_760_, lean_object* v_c_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CacheMap_parse_spec__1(v___x_755_, v_contents_756_, v_inst_757_, v_R_758_, v_a_759_, v_b_760_, v_c_761_);
lean_dec(v_b_760_);
lean_dec_ref(v_contents_756_);
lean_dec_ref(v___x_755_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(lean_object* v_inputName_763_, lean_object* v_lineNo_764_, lean_object* v_cache_765_, lean_object* v_line_766_, uint8_t v_platformIndependent_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
lean_inc_ref(v_cache_765_);
v___x_770_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go(v_cache_765_, v_line_766_, v_platformIndependent_767_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__0));
v___x_773_ = lean_string_append(v_inputName_763_, v___x_772_);
v___x_774_ = l_Nat_reprFast(v_lineNo_764_);
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
lean_dec_ref(v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v___x_778_ = lean_string_append(v___x_777_, v_a_771_);
lean_dec(v_a_771_);
v___x_779_ = 2;
v___x_780_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*1, v___x_779_);
v___x_781_ = lean_array_push(v___y_768_, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_cache_765_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
return v___x_782_;
}
else
{
lean_object* v_a_783_; lean_object* v___x_784_; 
lean_dec_ref(v_cache_765_);
lean_dec(v_lineNo_764_);
lean_dec_ref(v_inputName_763_);
v_a_783_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_770_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_783_);
lean_ctor_set(v___x_784_, 1, v___y_768_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0___boxed(lean_object* v_inputName_785_, lean_object* v_lineNo_786_, lean_object* v_cache_787_, lean_object* v_line_788_, lean_object* v_platformIndependent_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_platformIndependent_boxed_792_; lean_object* v_res_793_; 
v_platformIndependent_boxed_792_ = lean_unbox(v_platformIndependent_789_);
v_res_793_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(v_inputName_785_, v_lineNo_786_, v_cache_787_, v_line_788_, v_platformIndependent_boxed_792_, v___y_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(lean_object* v_h_794_, lean_object* v_fileName_795_, uint8_t v_platformIndependent_796_, lean_object* v_i_797_, lean_object* v_cache_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = lean_io_prim_handle_get_line(v_h_794_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
v___x_803_ = lean_string_utf8_byte_size(v_a_802_);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_nat_dec_eq(v___x_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_inc(v_i_797_);
lean_inc_ref(v_fileName_795_);
v___x_806_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop_spec__0(v_fileName_795_, v_i_797_, v_cache_798_, v_a_802_, v_platformIndependent_796_, v_a_799_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
v_a_808_ = lean_ctor_get(v___x_806_, 1);
lean_inc(v_a_808_);
lean_dec_ref(v___x_806_);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_i_797_, v___x_809_);
lean_dec(v_i_797_);
v_i_797_ = v___x_810_;
v_cache_798_ = v_a_807_;
v_a_799_ = v_a_808_;
goto _start;
}
else
{
lean_dec(v_i_797_);
lean_dec_ref(v_fileName_795_);
return v___x_806_;
}
}
else
{
lean_object* v___x_812_; 
lean_dec(v_a_802_);
lean_dec(v_i_797_);
lean_dec_ref(v_fileName_795_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v_cache_798_);
lean_ctor_set(v___x_812_, 1, v_a_799_);
return v___x_812_;
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_cache_798_);
lean_dec(v_i_797_);
lean_dec_ref(v_fileName_795_);
v_a_813_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_801_);
v___x_814_ = lean_io_error_to_string(v_a_813_);
v___x_815_ = 3;
v___x_816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v___x_815_);
v___x_817_ = lean_array_get_size(v_a_799_);
v___x_818_ = lean_array_push(v_a_799_, v___x_816_);
v___x_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop___boxed(lean_object* v_h_820_, lean_object* v_fileName_821_, lean_object* v_platformIndependent_822_, lean_object* v_i_823_, lean_object* v_cache_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
uint8_t v_platformIndependent_boxed_827_; lean_object* v_res_828_; 
v_platformIndependent_boxed_827_ = lean_unbox(v_platformIndependent_822_);
v_res_828_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_820_, v_fileName_821_, v_platformIndependent_boxed_827_, v_i_823_, v_cache_824_, v_a_825_);
lean_dec(v_h_820_);
return v_res_828_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_obj_once(&l_Lake_CacheMap_parse___closed__0, &l_Lake_CacheMap_parse___closed__0_once, _init_l_Lake_CacheMap_parse___closed__0);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(lean_object* v_h_832_, lean_object* v_fileName_833_, uint8_t v_platformIndependent_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = lean_io_prim_handle_get_line(v_h_832_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
lean_inc_ref(v_fileName_833_);
v___x_839_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_fileName_833_, v_a_838_, v_a_835_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_a_840_ = lean_ctor_get(v___x_839_, 1);
lean_inc(v_a_840_);
lean_dec_ref(v___x_839_);
v___x_841_ = lean_unsigned_to_nat(2u);
v___x_842_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_843_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_h_832_, v_fileName_833_, v_platformIndependent_834_, v___x_841_, v___x_842_, v_a_840_);
return v___x_843_;
}
else
{
lean_object* v_a_844_; lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v_fileName_833_);
v_a_844_ = lean_ctor_get(v___x_839_, 0);
v_a_845_ = lean_ctor_get(v___x_839_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_839_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_inc(v_a_844_);
lean_dec(v___x_839_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_844_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_a_845_);
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
else
{
lean_object* v_a_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec_ref(v_fileName_833_);
v_a_853_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_837_);
v___x_854_ = lean_io_error_to_string(v_a_853_);
v___x_855_ = 3;
v___x_856_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_855_);
v___x_857_ = lean_array_get_size(v_a_835_);
v___x_858_ = lean_array_push(v_a_835_, v___x_856_);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___boxed(lean_object* v_h_860_, lean_object* v_fileName_861_, lean_object* v_platformIndependent_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v_platformIndependent_boxed_865_; lean_object* v_res_866_; 
v_platformIndependent_boxed_865_ = lean_unbox(v_platformIndependent_862_);
v_res_866_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore(v_h_860_, v_fileName_861_, v_platformIndependent_boxed_865_, v_a_863_);
lean_dec(v_h_860_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load(lean_object* v_file_868_, uint8_t v_platformIndependent_869_, lean_object* v_a_870_){
_start:
{
uint8_t v___x_872_; lean_object* v___x_873_; 
v___x_872_ = 0;
v___x_873_ = lean_io_prim_handle_mk(v_file_868_, v___x_872_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; uint8_t v___x_875_; lean_object* v___x_876_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref(v___x_873_);
v___x_875_ = 0;
v___x_876_ = lean_io_prim_handle_lock(v_a_874_, v___x_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_877_; 
lean_dec_ref(v___x_876_);
v___x_877_ = lean_io_prim_handle_get_line(v_a_874_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
lean_inc_ref(v_file_868_);
v___x_879_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_868_, v_a_878_, v_a_870_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_a_880_ = lean_ctor_get(v___x_879_, 1);
lean_inc(v_a_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = lean_unsigned_to_nat(2u);
v___x_882_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_883_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_874_, v_file_868_, v_platformIndependent_869_, v___x_881_, v___x_882_, v_a_880_);
lean_dec(v_a_874_);
return v___x_883_;
}
else
{
lean_object* v_a_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_a_874_);
lean_dec_ref(v_file_868_);
v_a_884_ = lean_ctor_get(v___x_879_, 0);
v_a_885_ = lean_ctor_get(v___x_879_, 1);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_879_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_inc(v_a_884_);
lean_dec(v___x_879_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_884_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v_a_874_);
lean_dec_ref(v_file_868_);
v_a_893_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_893_);
lean_dec_ref(v___x_877_);
v___x_894_ = lean_io_error_to_string(v_a_893_);
v___x_895_ = 3;
v___x_896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*1, v___x_895_);
v___x_897_ = lean_array_get_size(v_a_870_);
v___x_898_ = lean_array_push(v_a_870_, v___x_896_);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
return v___x_899_;
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec(v_a_874_);
lean_dec_ref(v_file_868_);
v_a_900_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v___x_876_);
v___x_901_ = lean_io_error_to_string(v_a_900_);
v___x_902_ = 3;
v___x_903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*1, v___x_902_);
v___x_904_ = lean_array_get_size(v_a_870_);
v___x_905_ = lean_array_push(v_a_870_, v___x_903_);
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_a_907_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v___x_873_);
v___x_908_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_909_ = lean_string_append(v_file_868_, v___x_908_);
v___x_910_ = lean_io_error_to_string(v_a_907_);
v___x_911_ = lean_string_append(v___x_909_, v___x_910_);
lean_dec_ref(v___x_910_);
v___x_912_ = 3;
v___x_913_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1, v___x_912_);
v___x_914_ = lean_array_get_size(v_a_870_);
v___x_915_ = lean_array_push(v_a_870_, v___x_913_);
v___x_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load___boxed(lean_object* v_file_917_, lean_object* v_platformIndependent_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
uint8_t v_platformIndependent_boxed_921_; lean_object* v_res_922_; 
v_platformIndependent_boxed_921_ = lean_unbox(v_platformIndependent_918_);
v_res_922_ = l_Lake_CacheMap_load(v_file_917_, v_platformIndependent_boxed_921_, v_a_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f(lean_object* v_file_923_, uint8_t v_platformIndependent_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_a_928_; lean_object* v_a_929_; uint8_t v___x_931_; lean_object* v___x_932_; 
v___x_931_ = 0;
v___x_932_ = lean_io_prim_handle_mk(v_file_923_, v___x_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; uint8_t v___x_934_; lean_object* v___x_935_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref(v___x_932_);
v___x_934_ = 0;
v___x_935_ = lean_io_prim_handle_lock(v_a_933_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; 
lean_dec_ref(v___x_935_);
v___x_936_ = lean_io_prim_handle_get_line(v_a_933_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_962_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_962_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_962_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_962_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; 
lean_inc_ref(v_file_923_);
v___x_941_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_923_, v_a_937_, v_a_925_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_a_942_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_a_942_);
lean_dec_ref(v___x_941_);
v___x_943_ = lean_unsigned_to_nat(2u);
v___x_944_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_945_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_933_, v_file_923_, v_platformIndependent_924_, v___x_943_, v___x_944_, v_a_942_);
lean_dec(v_a_933_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_957_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_a_947_ = lean_ctor_get(v___x_945_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_949_ = v___x_945_;
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 1);
lean_ctor_set(v___x_939_, 0, v_a_946_);
v___x_952_ = v___x_939_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_946_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_952_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_a_947_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v_a_959_; 
lean_del_object(v___x_939_);
v_a_958_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_958_);
v_a_959_ = lean_ctor_get(v___x_945_, 1);
lean_inc(v_a_959_);
lean_dec_ref(v___x_945_);
v_a_928_ = v_a_958_;
v_a_929_ = v_a_959_;
goto v___jp_927_;
}
}
else
{
lean_object* v_a_960_; lean_object* v_a_961_; 
lean_del_object(v___x_939_);
lean_dec(v_a_933_);
lean_dec_ref(v_file_923_);
v_a_960_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_960_);
v_a_961_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_a_961_);
lean_dec_ref(v___x_941_);
v_a_928_ = v_a_960_;
v_a_929_ = v_a_961_;
goto v___jp_927_;
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_a_933_);
lean_dec_ref(v_file_923_);
v_a_963_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_963_);
lean_dec_ref(v___x_936_);
v___x_964_ = lean_io_error_to_string(v_a_963_);
v___x_965_ = 3;
v___x_966_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*1, v___x_965_);
v___x_967_ = lean_array_get_size(v_a_925_);
v___x_968_ = lean_array_push(v_a_925_, v___x_966_);
v_a_928_ = v___x_967_;
v_a_929_ = v___x_968_;
goto v___jp_927_;
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_dec(v_a_933_);
lean_dec_ref(v_file_923_);
v_a_969_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_935_);
v___x_970_ = lean_io_error_to_string(v_a_969_);
v___x_971_ = 3;
v___x_972_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*1, v___x_971_);
v___x_973_ = lean_array_get_size(v_a_925_);
v___x_974_ = lean_array_push(v_a_925_, v___x_972_);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
return v___x_975_;
}
}
else
{
lean_object* v_a_976_; 
v_a_976_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_976_);
lean_dec_ref(v___x_932_);
if (lean_obj_tag(v_a_976_) == 11)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec_ref(v_a_976_);
lean_dec_ref(v_file_923_);
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_a_925_);
return v___x_978_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_979_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_980_ = lean_string_append(v_file_923_, v___x_979_);
v___x_981_ = lean_io_error_to_string(v_a_976_);
v___x_982_ = lean_string_append(v___x_980_, v___x_981_);
lean_dec_ref(v___x_981_);
v___x_983_ = 3;
v___x_984_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*1, v___x_983_);
v___x_985_ = lean_array_get_size(v_a_925_);
v___x_986_ = lean_array_push(v_a_925_, v___x_984_);
v___x_987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
return v___x_987_;
}
}
v___jp_927_:
{
lean_object* v___x_930_; 
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v_a_928_);
lean_ctor_set(v___x_930_, 1, v_a_929_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_load_x3f___boxed(lean_object* v_file_988_, lean_object* v_platformIndependent_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
uint8_t v_platformIndependent_boxed_992_; lean_object* v_res_993_; 
v_platformIndependent_boxed_992_ = lean_unbox(v_platformIndependent_989_);
v_res_993_ = l_Lake_CacheMap_load_x3f(v_file_988_, v_platformIndependent_boxed_992_, v_a_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(lean_object* v_h_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v___y_997_){
_start:
{
if (lean_obj_tag(v_x_996_) == 0)
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v_x_995_);
lean_ctor_set(v___x_999_, 1, v___y_997_);
return v___x_999_;
}
else
{
lean_object* v_value_1000_; lean_object* v_key_1001_; lean_object* v_tail_1002_; lean_object* v_out_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1028_; 
v_value_1000_ = lean_ctor_get(v_x_996_, 1);
lean_inc(v_value_1000_);
v_key_1001_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_key_1001_);
v_tail_1002_ = lean_ctor_get(v_x_996_, 2);
lean_inc(v_tail_1002_);
lean_dec_ref(v_x_996_);
v_out_1003_ = lean_ctor_get(v_value_1000_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_value_1000_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1005_ = v_value_1000_;
v_isShared_1006_ = v_isSharedCheck_1028_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_out_1003_);
lean_dec(v_value_1000_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1028_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
uint64_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1007_ = lean_unbox_uint64(v_key_1001_);
lean_dec(v_key_1001_);
v___x_1008_ = l_Lake_lowerHexUInt64(v___x_1007_);
v___x_1009_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = lean_unsigned_to_nat(2u);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1012_ = lean_array_push(v___x_1011_, v___x_1009_);
v___x_1013_ = lean_array_push(v___x_1012_, v_out_1003_);
v___x_1014_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
v___x_1015_ = l_Lean_Json_compress(v___x_1014_);
v___x_1016_ = l_IO_FS_Handle_putStrLn(v_h_994_, v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; 
lean_del_object(v___x_1005_);
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref(v___x_1016_);
v_x_995_ = v_a_1017_;
v_x_996_ = v_tail_1002_;
goto _start;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1023_; 
lean_dec(v_tail_1002_);
v_a_1019_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v___x_1016_);
v___x_1020_ = lean_io_error_to_string(v_a_1019_);
v___x_1021_ = 3;
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1020_);
v___x_1023_ = v___x_1005_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1020_);
v___x_1023_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*1, v___x_1021_);
v___x_1024_ = lean_array_get_size(v___y_997_);
v___x_1025_ = lean_array_push(v___y_997_, v___x_1023_);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0___boxed(lean_object* v_h_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(v_h_1029_, v_x_1030_, v_x_1031_, v___y_1032_);
lean_dec(v_h_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(lean_object* v_h_1035_, lean_object* v_as_1036_, size_t v_i_1037_, size_t v_stop_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_usize_dec_eq(v_i_1037_, v_stop_1038_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_array_uget_borrowed(v_as_1036_, v_i_1037_);
v___x_1044_ = lean_box(0);
lean_inc(v___x_1043_);
v___x_1045_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__0(v_h_1035_, v___x_1044_, v___x_1043_, v___y_1040_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v_a_1047_; size_t v___x_1048_; size_t v___x_1049_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
v_a_1047_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_a_1047_);
lean_dec_ref(v___x_1045_);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1037_, v___x_1048_);
v_i_1037_ = v___x_1049_;
v_b_1039_ = v_a_1046_;
v___y_1040_ = v_a_1047_;
goto _start;
}
else
{
return v___x_1045_;
}
}
else
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_b_1039_);
lean_ctor_set(v___x_1051_, 1, v___y_1040_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1___boxed(lean_object* v_h_1052_, lean_object* v_as_1053_, lean_object* v_i_1054_, lean_object* v_stop_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
size_t v_i_boxed_1059_; size_t v_stop_boxed_1060_; lean_object* v_res_1061_; 
v_i_boxed_1059_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_stop_boxed_1060_ = lean_unbox_usize(v_stop_1055_);
lean_dec(v_stop_1055_);
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1052_, v_as_1053_, v_i_boxed_1059_, v_stop_boxed_1060_, v_b_1056_, v___y_1057_);
lean_dec_ref(v_as_1053_);
lean_dec(v_h_1052_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(lean_object* v_h_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_){
_start:
{
if (lean_obj_tag(v_x_1064_) == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_x_1063_);
lean_ctor_set(v___x_1067_, 1, v___y_1065_);
return v___x_1067_;
}
else
{
lean_object* v_value_1068_; uint8_t v_platformIndependent_1069_; 
v_value_1068_ = lean_ctor_get(v_x_1064_, 1);
lean_inc(v_value_1068_);
v_platformIndependent_1069_ = lean_ctor_get_uint8(v_value_1068_, sizeof(void*)*1);
if (v_platformIndependent_1069_ == 0)
{
lean_object* v_tail_1070_; lean_object* v___x_1071_; 
lean_dec(v_value_1068_);
v_tail_1070_ = lean_ctor_get(v_x_1064_, 2);
lean_inc(v_tail_1070_);
lean_dec_ref(v_x_1064_);
v___x_1071_ = lean_box(0);
v_x_1063_ = v___x_1071_;
v_x_1064_ = v_tail_1070_;
goto _start;
}
else
{
lean_object* v_key_1073_; lean_object* v_tail_1074_; lean_object* v_out_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1100_; 
v_key_1073_ = lean_ctor_get(v_x_1064_, 0);
lean_inc(v_key_1073_);
v_tail_1074_ = lean_ctor_get(v_x_1064_, 2);
lean_inc(v_tail_1074_);
lean_dec_ref(v_x_1064_);
v_out_1075_ = lean_ctor_get(v_value_1068_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_value_1068_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1077_ = v_value_1068_;
v_isShared_1078_ = v_isSharedCheck_1100_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_out_1075_);
lean_dec(v_value_1068_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1100_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
uint64_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1079_ = lean_unbox_uint64(v_key_1073_);
lean_dec(v_key_1073_);
v___x_1080_ = l_Lake_lowerHexUInt64(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
v___x_1082_ = lean_unsigned_to_nat(2u);
v___x_1083_ = lean_mk_empty_array_with_capacity(v___x_1082_);
v___x_1084_ = lean_array_push(v___x_1083_, v___x_1081_);
v___x_1085_ = lean_array_push(v___x_1084_, v_out_1075_);
v___x_1086_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
v___x_1087_ = l_Lean_Json_compress(v___x_1086_);
v___x_1088_ = l_IO_FS_Handle_putStrLn(v_h_1062_, v___x_1087_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; 
lean_del_object(v___x_1077_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref(v___x_1088_);
v_x_1063_ = v_a_1089_;
v_x_1064_ = v_tail_1074_;
goto _start;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1095_; 
lean_dec(v_tail_1074_);
v_a_1091_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v___x_1088_);
v___x_1092_ = lean_io_error_to_string(v_a_1091_);
v___x_1093_ = 3;
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1092_);
v___x_1095_ = v___x_1077_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1092_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*1, v___x_1093_);
v___x_1096_ = lean_array_get_size(v___y_1065_);
v___x_1097_ = lean_array_push(v___y_1065_, v___x_1095_);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
return v___x_1098_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2___boxed(lean_object* v_h_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(v_h_1101_, v_x_1102_, v_x_1103_, v___y_1104_);
lean_dec(v_h_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(lean_object* v_h_1107_, lean_object* v_as_1108_, size_t v_i_1109_, size_t v_stop_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_usize_dec_eq(v_i_1109_, v_stop_1110_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_array_uget_borrowed(v_as_1108_, v_i_1109_);
v___x_1116_ = lean_box(0);
lean_inc(v___x_1115_);
v___x_1117_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__2(v_h_1107_, v___x_1116_, v___x_1115_, v___y_1112_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_a_1119_; size_t v___x_1120_; size_t v___x_1121_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
v_a_1119_ = lean_ctor_get(v___x_1117_, 1);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1117_);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_add(v_i_1109_, v___x_1120_);
v_i_1109_ = v___x_1121_;
v_b_1111_ = v_a_1118_;
v___y_1112_ = v_a_1119_;
goto _start;
}
else
{
return v___x_1117_;
}
}
else
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_b_1111_);
lean_ctor_set(v___x_1123_, 1, v___y_1112_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3___boxed(lean_object* v_h_1124_, lean_object* v_as_1125_, lean_object* v_i_1126_, lean_object* v_stop_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
size_t v_i_boxed_1131_; size_t v_stop_boxed_1132_; lean_object* v_res_1133_; 
v_i_boxed_1131_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_stop_boxed_1132_ = lean_unbox_usize(v_stop_1127_);
lean_dec(v_stop_1127_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1124_, v_as_1125_, v_i_boxed_1131_, v_stop_boxed_1132_, v_b_1128_, v___y_1129_);
lean_dec_ref(v_as_1125_);
lean_dec(v_h_1124_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(lean_object* v_h_1134_, lean_object* v_cache_1135_, uint8_t v_platformIndependent_1136_, lean_object* v_a_1137_){
_start:
{
if (v_platformIndependent_1136_ == 0)
{
lean_object* v_buckets_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1160_; 
v_buckets_1139_ = lean_ctor_get(v_cache_1135_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_cache_1135_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_cache_1135_, 0);
lean_dec(v_unused_1161_);
v___x_1141_ = v_cache_1135_;
v_isShared_1142_ = v_isSharedCheck_1160_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_buckets_1139_);
lean_dec(v_cache_1135_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1160_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_array_get_size(v_buckets_1139_);
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_nat_dec_lt(v___x_1143_, v___x_1144_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1148_; 
lean_dec_ref(v_buckets_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_a_1137_);
lean_ctor_set(v___x_1141_, 0, v___x_1145_);
v___x_1148_ = v___x_1141_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_a_1137_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_nat_dec_le(v___x_1144_, v___x_1144_);
if (v___x_1150_ == 0)
{
if (v___x_1146_ == 0)
{
lean_object* v___x_1152_; 
lean_dec_ref(v_buckets_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_a_1137_);
lean_ctor_set(v___x_1141_, 0, v___x_1145_);
v___x_1152_ = v___x_1141_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_a_1137_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
size_t v___x_1154_; size_t v___x_1155_; lean_object* v___x_1156_; 
lean_del_object(v___x_1141_);
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = lean_usize_of_nat(v___x_1144_);
v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1134_, v_buckets_1139_, v___x_1154_, v___x_1155_, v___x_1145_, v_a_1137_);
lean_dec_ref(v_buckets_1139_);
return v___x_1156_;
}
}
else
{
size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; 
lean_del_object(v___x_1141_);
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = lean_usize_of_nat(v___x_1144_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__1(v_h_1134_, v_buckets_1139_, v___x_1157_, v___x_1158_, v___x_1145_, v_a_1137_);
lean_dec_ref(v_buckets_1139_);
return v___x_1159_;
}
}
}
}
else
{
lean_object* v_buckets_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1183_; 
v_buckets_1162_ = lean_ctor_get(v_cache_1135_, 1);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_cache_1135_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v_cache_1135_, 0);
lean_dec(v_unused_1184_);
v___x_1164_ = v_cache_1135_;
v_isShared_1165_ = v_isSharedCheck_1183_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_buckets_1162_);
lean_dec(v_cache_1135_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1183_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_array_get_size(v_buckets_1162_);
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_nat_dec_lt(v___x_1166_, v___x_1167_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref(v_buckets_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v_a_1137_);
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1171_ = v___x_1164_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_a_1137_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
else
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_nat_dec_le(v___x_1167_, v___x_1167_);
if (v___x_1173_ == 0)
{
if (v___x_1169_ == 0)
{
lean_object* v___x_1175_; 
lean_dec_ref(v_buckets_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v_a_1137_);
lean_ctor_set(v___x_1164_, 0, v___x_1168_);
v___x_1175_ = v___x_1164_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_a_1137_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
lean_del_object(v___x_1164_);
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = lean_usize_of_nat(v___x_1167_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1134_, v_buckets_1162_, v___x_1177_, v___x_1178_, v___x_1168_, v_a_1137_);
lean_dec_ref(v_buckets_1162_);
return v___x_1179_;
}
}
else
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
lean_del_object(v___x_1164_);
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = lean_usize_of_nat(v___x_1167_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries_spec__3(v_h_1134_, v_buckets_1162_, v___x_1180_, v___x_1181_, v___x_1168_, v_a_1137_);
lean_dec_ref(v_buckets_1162_);
return v___x_1182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries___boxed(lean_object* v_h_1185_, lean_object* v_cache_1186_, lean_object* v_platformIndependent_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
uint8_t v_platformIndependent_boxed_1190_; lean_object* v_res_1191_; 
v_platformIndependent_boxed_1190_ = lean_unbox(v_platformIndependent_1187_);
v_res_1191_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_h_1185_, v_cache_1186_, v_platformIndependent_boxed_1190_, v_a_1188_);
lean_dec(v_h_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(lean_object* v_x_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1193_) == 0)
{
return v_x_1192_;
}
else
{
lean_object* v_key_1194_; lean_object* v_value_1195_; lean_object* v_tail_1196_; uint64_t v___x_1197_; lean_object* v___x_1198_; 
v_key_1194_ = lean_ctor_get(v_x_1193_, 0);
lean_inc(v_key_1194_);
v_value_1195_ = lean_ctor_get(v_x_1193_, 1);
lean_inc(v_value_1195_);
v_tail_1196_ = lean_ctor_get(v_x_1193_, 2);
lean_inc(v_tail_1196_);
lean_dec_ref(v_x_1193_);
v___x_1197_ = lean_unbox_uint64(v_key_1194_);
lean_dec(v_key_1194_);
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_x_1192_, v___x_1197_, v_value_1195_);
v_x_1192_ = v___x_1198_;
v_x_1193_ = v_tail_1196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(lean_object* v_as_1200_, size_t v_i_1201_, size_t v_stop_1202_, lean_object* v_b_1203_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_usize_dec_eq(v_i_1201_, v_stop_1202_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; 
v___x_1205_ = lean_array_uget_borrowed(v_as_1200_, v_i_1201_);
lean_inc(v___x_1205_);
v___x_1206_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_updateFile_spec__0(v_b_1203_, v___x_1205_);
v___x_1207_ = ((size_t)1ULL);
v___x_1208_ = lean_usize_add(v_i_1201_, v___x_1207_);
v_i_1201_ = v___x_1208_;
v_b_1203_ = v___x_1206_;
goto _start;
}
else
{
return v_b_1203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1___boxed(lean_object* v_as_1210_, lean_object* v_i_1211_, lean_object* v_stop_1212_, lean_object* v_b_1213_){
_start:
{
size_t v_i_boxed_1214_; size_t v_stop_boxed_1215_; lean_object* v_res_1216_; 
v_i_boxed_1214_ = lean_unbox_usize(v_i_1211_);
lean_dec(v_i_1211_);
v_stop_boxed_1215_ = lean_unbox_usize(v_stop_1212_);
lean_dec(v_stop_1212_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_as_1210_, v_i_boxed_1214_, v_stop_boxed_1215_, v_b_1213_);
lean_dec_ref(v_as_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile(lean_object* v_file_1217_, lean_object* v_cache_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_a_1222_; lean_object* v_a_1223_; lean_object* v___x_1225_; 
lean_inc_ref(v_file_1217_);
v___x_1225_ = l_Lake_createParentDirs(v_file_1217_);
if (lean_obj_tag(v___x_1225_) == 0)
{
uint8_t v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v___x_1225_);
v___x_1226_ = 4;
v___x_1227_ = lean_io_prim_handle_mk(v_file_1217_, v___x_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
uint8_t v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v___x_1227_);
v___x_1228_ = 3;
v___x_1229_ = lean_io_prim_handle_mk(v_file_1217_, v___x_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = 1;
v___x_1232_ = lean_io_prim_handle_lock(v_a_1230_, v___x_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v___x_1232_);
v___x_1233_ = lean_io_prim_handle_get_line(v_a_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___x_1233_);
lean_inc_ref(v_file_1217_);
v___x_1235_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_checkSchemaVersion(v_file_1217_, v_a_1234_, v_a_1219_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_a_1236_);
lean_dec_ref(v___x_1235_);
v___x_1237_ = 0;
v___x_1238_ = lean_unsigned_to_nat(2u);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0, &l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore___closed__0);
v___x_1241_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_loadCore_loop(v_a_1230_, v_file_1217_, v___x_1237_, v___x_1238_, v___x_1240_, v_a_1236_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1270_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_a_1243_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1245_ = v___x_1241_;
v_isShared_1246_ = v_isSharedCheck_1270_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1270_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___y_1248_; lean_object* v_buckets_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_buckets_1260_ = lean_ctor_get(v_cache_1218_, 1);
v___x_1261_ = lean_array_get_size(v_buckets_1260_);
v___x_1262_ = lean_nat_dec_lt(v___x_1239_, v___x_1261_);
if (v___x_1262_ == 0)
{
v___y_1248_ = v_a_1242_;
goto v___jp_1247_;
}
else
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_nat_dec_le(v___x_1261_, v___x_1261_);
if (v___x_1263_ == 0)
{
if (v___x_1262_ == 0)
{
v___y_1248_ = v_a_1242_;
goto v___jp_1247_;
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = lean_usize_of_nat(v___x_1261_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_buckets_1260_, v___x_1264_, v___x_1265_, v_a_1242_);
v___y_1248_ = v___x_1266_;
goto v___jp_1247_;
}
}
else
{
size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = ((size_t)0ULL);
v___x_1268_ = lean_usize_of_nat(v___x_1261_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_updateFile_spec__1(v_buckets_1260_, v___x_1267_, v___x_1268_, v_a_1242_);
v___y_1248_ = v___x_1269_;
goto v___jp_1247_;
}
}
v___jp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_io_prim_handle_rewind(v_a_1230_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1250_; 
lean_dec_ref(v___x_1249_);
lean_del_object(v___x_1245_);
v___x_1250_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_a_1230_, v___y_1248_, v___x_1237_, v_a_1243_);
lean_dec(v_a_1230_);
return v___x_1250_;
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; 
lean_dec_ref(v___y_1248_);
lean_dec(v_a_1230_);
v_a_1251_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1249_);
v___x_1252_ = lean_io_error_to_string(v_a_1251_);
v___x_1253_ = 3;
v___x_1254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*1, v___x_1253_);
v___x_1255_ = lean_array_get_size(v_a_1243_);
v___x_1256_ = lean_array_push(v_a_1243_, v___x_1254_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 1);
lean_ctor_set(v___x_1245_, 1, v___x_1256_);
lean_ctor_set(v___x_1245_, 0, v___x_1255_);
v___x_1258_ = v___x_1245_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v_a_1272_; 
lean_dec(v_a_1230_);
v_a_1271_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1271_);
v_a_1272_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1241_);
v_a_1222_ = v_a_1271_;
v_a_1223_ = v_a_1272_;
goto v___jp_1221_;
}
}
else
{
lean_object* v_a_1273_; lean_object* v_a_1274_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_file_1217_);
v_a_1273_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1273_);
v_a_1274_ = lean_ctor_get(v___x_1235_, 1);
lean_inc(v_a_1274_);
lean_dec_ref(v___x_1235_);
v_a_1222_ = v_a_1273_;
v_a_1223_ = v_a_1274_;
goto v___jp_1221_;
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_file_1217_);
v_a_1275_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v___x_1233_);
v___x_1276_ = lean_io_error_to_string(v_a_1275_);
v___x_1277_ = 3;
v___x_1278_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1, v___x_1277_);
v___x_1279_ = lean_array_get_size(v_a_1219_);
v___x_1280_ = lean_array_push(v_a_1219_, v___x_1278_);
v_a_1222_ = v___x_1279_;
v_a_1223_ = v___x_1280_;
goto v___jp_1221_;
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_a_1230_);
lean_dec_ref(v_file_1217_);
v_a_1281_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1232_);
v___x_1282_ = lean_io_error_to_string(v_a_1281_);
v___x_1283_ = 3;
v___x_1284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1283_);
v___x_1285_ = lean_array_get_size(v_a_1219_);
v___x_1286_ = lean_array_push(v_a_1219_, v___x_1284_);
v___x_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
return v___x_1287_;
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1288_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1288_);
lean_dec_ref(v___x_1229_);
v___x_1289_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1290_ = lean_string_append(v_file_1217_, v___x_1289_);
v___x_1291_ = lean_io_error_to_string(v_a_1288_);
v___x_1292_ = lean_string_append(v___x_1290_, v___x_1291_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = 3;
v___x_1294_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set_uint8(v___x_1294_, sizeof(void*)*1, v___x_1293_);
v___x_1295_ = lean_array_get_size(v_a_1219_);
v___x_1296_ = lean_array_push(v_a_1219_, v___x_1294_);
v___x_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
return v___x_1297_;
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec_ref(v_file_1217_);
v_a_1298_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1227_);
v___x_1299_ = lean_io_error_to_string(v_a_1298_);
v___x_1300_ = 3;
v___x_1301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*1, v___x_1300_);
v___x_1302_ = lean_array_get_size(v_a_1219_);
v___x_1303_ = lean_array_push(v_a_1219_, v___x_1301_);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
return v___x_1304_;
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec_ref(v_file_1217_);
v_a_1305_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1225_);
v___x_1306_ = lean_io_error_to_string(v_a_1305_);
v___x_1307_ = 3;
v___x_1308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set_uint8(v___x_1308_, sizeof(void*)*1, v___x_1307_);
v___x_1309_ = lean_array_get_size(v_a_1219_);
v___x_1310_ = lean_array_push(v_a_1219_, v___x_1308_);
v___x_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
return v___x_1311_;
}
v___jp_1221_:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1222_);
lean_ctor_set(v___x_1224_, 1, v_a_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_updateFile___boxed(lean_object* v_file_1312_, lean_object* v_cache_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lake_CacheMap_updateFile(v_file_1312_, v_cache_1313_, v_a_1314_);
lean_dec_ref(v_cache_1313_);
return v_res_1316_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__0(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lake_CacheMap_schemaVersion));
v___x_1318_ = l_Lake_Date_toString(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__1(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__0, &l_Lake_CacheMap_writeFile___closed__0_once, _init_l_Lake_CacheMap_writeFile___closed__0);
v___x_1320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
static lean_object* _init_l_Lake_CacheMap_writeFile___closed__2(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__1, &l_Lake_CacheMap_writeFile___closed__1_once, _init_l_Lake_CacheMap_writeFile___closed__1);
v___x_1322_ = l_Lean_Json_compress(v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile(lean_object* v_file_1323_, lean_object* v_cache_1324_, uint8_t v_platformIndependent_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1328_; 
lean_inc_ref(v_file_1323_);
v___x_1328_ = l_Lake_createParentDirs(v_file_1323_);
if (lean_obj_tag(v___x_1328_) == 0)
{
uint8_t v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v___x_1328_);
v___x_1329_ = 1;
v___x_1330_ = lean_io_prim_handle_mk(v_file_1323_, v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; 
lean_dec_ref(v_file_1323_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref(v___x_1330_);
v___x_1332_ = 1;
v___x_1333_ = lean_io_prim_handle_lock(v_a_1331_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref(v___x_1333_);
v___x_1334_ = lean_obj_once(&l_Lake_CacheMap_writeFile___closed__2, &l_Lake_CacheMap_writeFile___closed__2_once, _init_l_Lake_CacheMap_writeFile___closed__2);
v___x_1335_ = l_IO_FS_Handle_putStrLn(v_a_1331_, v___x_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref(v___x_1335_);
v___x_1336_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_writeCacheEntries(v_a_1331_, v_cache_1324_, v_platformIndependent_1325_, v_a_1326_);
lean_dec(v_a_1331_);
return v___x_1336_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_a_1331_);
lean_dec_ref(v_cache_1324_);
v_a_1337_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1335_);
v___x_1338_ = lean_io_error_to_string(v_a_1337_);
v___x_1339_ = 3;
v___x_1340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*1, v___x_1339_);
v___x_1341_ = lean_array_get_size(v_a_1326_);
v___x_1342_ = lean_array_push(v_a_1326_, v___x_1340_);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
return v___x_1343_;
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_a_1331_);
lean_dec_ref(v_cache_1324_);
v_a_1344_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1344_);
lean_dec_ref(v___x_1333_);
v___x_1345_ = lean_io_error_to_string(v_a_1344_);
v___x_1346_ = 3;
v___x_1347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*1, v___x_1346_);
v___x_1348_ = lean_array_get_size(v_a_1326_);
v___x_1349_ = lean_array_push(v_a_1326_, v___x_1347_);
v___x_1350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
return v___x_1350_;
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v_cache_1324_);
v_a_1351_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1330_);
v___x_1352_ = ((lean_object*)(l_Lake_CacheMap_load___closed__0));
v___x_1353_ = lean_string_append(v_file_1323_, v___x_1352_);
v___x_1354_ = lean_io_error_to_string(v_a_1351_);
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = 3;
v___x_1357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*1, v___x_1356_);
v___x_1358_ = lean_array_get_size(v_a_1326_);
v___x_1359_ = lean_array_push(v_a_1326_, v___x_1357_);
v___x_1360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
return v___x_1360_;
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec_ref(v_cache_1324_);
lean_dec_ref(v_file_1323_);
v_a_1361_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1328_);
v___x_1362_ = lean_io_error_to_string(v_a_1361_);
v___x_1363_ = 3;
v___x_1364_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*1, v___x_1363_);
v___x_1365_ = lean_array_get_size(v_a_1326_);
v___x_1366_ = lean_array_push(v_a_1326_, v___x_1364_);
v___x_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_writeFile___boxed(lean_object* v_file_1368_, lean_object* v_cache_1369_, lean_object* v_platformIndependent_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
uint8_t v_platformIndependent_boxed_1373_; lean_object* v_res_1374_; 
v_platformIndependent_boxed_1373_ = lean_unbox(v_platformIndependent_1370_);
v_res_1374_ = l_Lake_CacheMap_writeFile(v_file_1368_, v_cache_1369_, v_platformIndependent_boxed_1373_, v_a_1371_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(uint64_t v_a_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_box(0);
return v___x_1377_;
}
else
{
lean_object* v_key_1378_; lean_object* v_value_1379_; lean_object* v_tail_1380_; uint64_t v___x_1381_; uint8_t v___x_1382_; 
v_key_1378_ = lean_ctor_get(v_x_1376_, 0);
v_value_1379_ = lean_ctor_get(v_x_1376_, 1);
v_tail_1380_ = lean_ctor_get(v_x_1376_, 2);
v___x_1381_ = lean_unbox_uint64(v_key_1378_);
v___x_1382_ = lean_uint64_dec_eq(v___x_1381_, v_a_1375_);
if (v___x_1382_ == 0)
{
v_x_1376_ = v_tail_1380_;
goto _start;
}
else
{
lean_object* v___x_1384_; 
lean_inc(v_value_1379_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_value_1379_);
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_1385_, lean_object* v_x_1386_){
_start:
{
uint64_t v_a_boxed_1387_; lean_object* v_res_1388_; 
v_a_boxed_1387_ = lean_unbox_uint64(v_a_1385_);
lean_dec_ref(v_a_1385_);
v_res_1388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_boxed_1387_, v_x_1386_);
lean_dec(v_x_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(lean_object* v_m_1389_, uint64_t v_a_1390_){
_start:
{
lean_object* v_buckets_1391_; lean_object* v___x_1392_; uint64_t v___x_1393_; uint64_t v___x_1394_; uint64_t v_fold_1395_; uint64_t v___x_1396_; uint64_t v___x_1397_; uint64_t v___x_1398_; size_t v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_buckets_1391_ = lean_ctor_get(v_m_1389_, 1);
v___x_1392_ = lean_array_get_size(v_buckets_1391_);
v___x_1393_ = 32ULL;
v___x_1394_ = lean_uint64_shift_right(v_a_1390_, v___x_1393_);
v_fold_1395_ = lean_uint64_xor(v_a_1390_, v___x_1394_);
v___x_1396_ = 16ULL;
v___x_1397_ = lean_uint64_shift_right(v_fold_1395_, v___x_1396_);
v___x_1398_ = lean_uint64_xor(v_fold_1395_, v___x_1397_);
v___x_1399_ = lean_uint64_to_usize(v___x_1398_);
v___x_1400_ = lean_usize_of_nat(v___x_1392_);
v___x_1401_ = ((size_t)1ULL);
v___x_1402_ = lean_usize_sub(v___x_1400_, v___x_1401_);
v___x_1403_ = lean_usize_land(v___x_1399_, v___x_1402_);
v___x_1404_ = lean_array_uget_borrowed(v_buckets_1391_, v___x_1403_);
v___x_1405_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1390_, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg___boxed(lean_object* v_m_1406_, lean_object* v_a_1407_){
_start:
{
uint64_t v_a_boxed_1408_; lean_object* v_res_1409_; 
v_a_boxed_1408_ = lean_unbox_uint64(v_a_1407_);
lean_dec_ref(v_a_1407_);
v_res_1409_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1406_, v_a_boxed_1408_);
lean_dec_ref(v_m_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f(uint64_t v_inputHash_1410_, lean_object* v_cache_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_cache_1411_, v_inputHash_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_box(0);
return v___x_1413_;
}
else
{
lean_object* v_val_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_val_1414_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1412_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_val_1414_);
lean_dec(v___x_1412_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_out_1418_; lean_object* v___x_1420_; 
v_out_1418_ = lean_ctor_get(v_val_1414_, 0);
lean_inc(v_out_1418_);
lean_dec(v_val_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v_out_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_out_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_get_x3f___boxed(lean_object* v_inputHash_1423_, lean_object* v_cache_1424_){
_start:
{
uint64_t v_inputHash_boxed_1425_; lean_object* v_res_1426_; 
v_inputHash_boxed_1425_ = lean_unbox_uint64(v_inputHash_1423_);
lean_dec_ref(v_inputHash_1423_);
v_res_1426_ = l_Lake_CacheMap_get_x3f(v_inputHash_boxed_1425_, v_cache_1424_);
lean_dec_ref(v_cache_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, uint64_t v_a_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___redArg(v_m_1428_, v_a_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0___boxed(lean_object* v_00_u03b2_1431_, lean_object* v_m_1432_, lean_object* v_a_1433_){
_start:
{
uint64_t v_a_boxed_1434_; lean_object* v_res_1435_; 
v_a_boxed_1434_ = lean_unbox_uint64(v_a_1433_);
lean_dec_ref(v_a_1433_);
v_res_1435_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0(v_00_u03b2_1431_, v_m_1432_, v_a_boxed_1434_);
lean_dec_ref(v_m_1432_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1436_, uint64_t v_a_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___redArg(v_a_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1440_, lean_object* v_a_1441_, lean_object* v_x_1442_){
_start:
{
uint64_t v_a_boxed_1443_; lean_object* v_res_1444_; 
v_a_boxed_1443_ = lean_unbox_uint64(v_a_1441_);
lean_dec_ref(v_a_1441_);
v_res_1444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lake_CacheMap_get_x3f_spec__0_spec__0(v_00_u03b2_1440_, v_a_boxed_1443_, v_x_1442_);
lean_dec(v_x_1442_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(uint64_t v_inputHash_1445_, lean_object* v_out_1446_, lean_object* v_cache_1447_, uint8_t v_platformIndependent_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1449_, 0, v_out_1446_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*1, v_platformIndependent_1448_);
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__1___redArg(v_cache_1447_, v_inputHash_1445_, v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore___boxed(lean_object* v_inputHash_1451_, lean_object* v_out_1452_, lean_object* v_cache_1453_, lean_object* v_platformIndependent_1454_){
_start:
{
uint64_t v_inputHash_boxed_1455_; uint8_t v_platformIndependent_boxed_1456_; lean_object* v_res_1457_; 
v_inputHash_boxed_1455_ = lean_unbox_uint64(v_inputHash_1451_);
lean_dec_ref(v_inputHash_1451_);
v_platformIndependent_boxed_1456_ = lean_unbox(v_platformIndependent_1454_);
v_res_1457_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_boxed_1455_, v_out_1452_, v_cache_1453_, v_platformIndependent_boxed_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg(lean_object* v_inst_1458_, uint64_t v_inputHash_1459_, lean_object* v_val_1460_, lean_object* v_cache_1461_, uint8_t v_platformIndependent_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_apply_1(v_inst_1458_, v_val_1460_);
v___x_1464_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1459_, v___x_1463_, v_cache_1461_, v_platformIndependent_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___redArg___boxed(lean_object* v_inst_1465_, lean_object* v_inputHash_1466_, lean_object* v_val_1467_, lean_object* v_cache_1468_, lean_object* v_platformIndependent_1469_){
_start:
{
uint64_t v_inputHash_boxed_1470_; uint8_t v_platformIndependent_boxed_1471_; lean_object* v_res_1472_; 
v_inputHash_boxed_1470_ = lean_unbox_uint64(v_inputHash_1466_);
lean_dec_ref(v_inputHash_1466_);
v_platformIndependent_boxed_1471_ = lean_unbox(v_platformIndependent_1469_);
v_res_1472_ = l_Lake_CacheMap_insert___redArg(v_inst_1465_, v_inputHash_boxed_1470_, v_val_1467_, v_cache_1468_, v_platformIndependent_boxed_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert(lean_object* v_00_u03b1_1473_, lean_object* v_inst_1474_, uint64_t v_inputHash_1475_, lean_object* v_val_1476_, lean_object* v_cache_1477_, uint8_t v_platformIndependent_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_apply_1(v_inst_1474_, v_val_1476_);
v___x_1480_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1475_, v___x_1479_, v_cache_1477_, v_platformIndependent_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_insert___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_inst_1482_, lean_object* v_inputHash_1483_, lean_object* v_val_1484_, lean_object* v_cache_1485_, lean_object* v_platformIndependent_1486_){
_start:
{
uint64_t v_inputHash_boxed_1487_; uint8_t v_platformIndependent_boxed_1488_; lean_object* v_res_1489_; 
v_inputHash_boxed_1487_ = lean_unbox_uint64(v_inputHash_1483_);
lean_dec_ref(v_inputHash_1483_);
v_platformIndependent_boxed_1488_ = lean_unbox(v_platformIndependent_1486_);
v_res_1489_ = l_Lake_CacheMap_insert(v_00_u03b1_1481_, v_inst_1482_, v_inputHash_boxed_1487_, v_val_1484_, v_cache_1485_, v_platformIndependent_boxed_1488_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(lean_object* v_init_1493_, lean_object* v_x_1494_, lean_object* v___y_1495_){
_start:
{
if (lean_obj_tag(v_x_1494_) == 0)
{
lean_object* v_v_1497_; lean_object* v_l_1498_; lean_object* v_r_1499_; lean_object* v___x_1500_; 
v_v_1497_ = lean_ctor_get(v_x_1494_, 2);
lean_inc(v_v_1497_);
v_l_1498_ = lean_ctor_get(v_x_1494_, 3);
lean_inc(v_l_1498_);
v_r_1499_ = lean_ctor_get(v_x_1494_, 4);
lean_inc(v_r_1499_);
lean_dec_ref(v_x_1494_);
v___x_1500_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1493_, v_l_1498_, v___y_1495_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v_a_1502_; lean_object* v___x_1503_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
v_a_1502_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_a_1502_);
lean_dec_ref(v___x_1500_);
v___x_1503_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_a_1501_, v_v_1497_, v_a_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v_a_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
v_a_1505_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1503_);
v_init_1493_ = v_a_1504_;
v_x_1494_ = v_r_1499_;
v___y_1495_ = v_a_1505_;
goto _start;
}
else
{
lean_dec(v_r_1499_);
return v___x_1503_;
}
}
else
{
lean_dec(v_r_1499_);
lean_dec(v_v_1497_);
return v___x_1500_;
}
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_init_1493_);
lean_ctor_set(v___x_1507_, 1, v___y_1495_);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(lean_object* v_as_1508_, lean_object* v_o_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___y_1513_; 
switch(lean_obj_tag(v_o_1509_))
{
case 0:
{
v___y_1513_ = v_a_1510_;
goto v___jp_1512_;
}
case 1:
{
lean_object* v___x_1515_; 
lean_dec_ref(v_o_1509_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_as_1508_);
lean_ctor_set(v___x_1515_, 1, v_a_1510_);
return v___x_1515_;
}
case 2:
{
lean_object* v_n_1516_; lean_object* v___x_1517_; 
v_n_1516_ = lean_ctor_get(v_o_1509_, 0);
lean_inc_ref(v_n_1516_);
lean_dec_ref(v_o_1509_);
v___x_1517_ = l_Lake_Hash_ofJsonNumber_x3f(v_n_1516_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__0));
v___x_1520_ = lean_string_append(v___x_1519_, v_a_1518_);
lean_dec(v_a_1518_);
v___x_1521_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry___redArg___closed__1));
v___x_1522_ = lean_string_append(v___x_1520_, v___x_1521_);
v___x_1523_ = l_Lean_JsonNumber_toString(v_n_1516_);
v___x_1524_ = lean_string_append(v___x_1522_, v___x_1523_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = 3;
v___x_1526_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*1, v___x_1525_);
v___x_1527_ = lean_array_push(v_a_1510_, v___x_1526_);
v___y_1513_ = v___x_1527_;
goto v___jp_1512_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint64_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec_ref(v_n_1516_);
v_a_1528_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1517_);
v___x_1529_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__1));
v___x_1530_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
v___x_1531_ = lean_unbox_uint64(v_a_1528_);
lean_dec(v_a_1528_);
lean_ctor_set_uint64(v___x_1530_, sizeof(void*)*1, v___x_1531_);
v___x_1532_ = lean_array_push(v_as_1508_, v___x_1530_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v_a_1510_);
return v___x_1533_;
}
}
case 3:
{
lean_object* v_s_1534_; lean_object* v___x_1535_; 
v_s_1534_ = lean_ctor_get(v_o_1509_, 0);
lean_inc_ref(v_s_1534_);
lean_dec_ref(v_o_1509_);
v___x_1535_ = l_Lake_ArtifactDescr_ofFilePath_x3f(v_s_1534_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___closed__2));
v___x_1538_ = lean_string_append(v___x_1537_, v_a_1536_);
lean_dec(v_a_1536_);
v___x_1539_ = 3;
v___x_1540_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*1, v___x_1539_);
v___x_1541_ = lean_array_push(v_a_1510_, v___x_1540_);
v___y_1513_ = v___x_1541_;
goto v___jp_1512_;
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_a_1542_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1535_);
v___x_1543_ = lean_array_push(v_as_1508_, v_a_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_a_1510_);
return v___x_1544_;
}
}
case 4:
{
lean_object* v_elems_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_elems_1545_ = lean_ctor_get(v_o_1509_, 0);
lean_inc_ref(v_elems_1545_);
lean_dec_ref(v_o_1509_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_array_get_size(v_elems_1545_);
v___x_1548_ = lean_nat_dec_lt(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec_ref(v_elems_1545_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_as_1508_);
lean_ctor_set(v___x_1549_, 1, v_a_1510_);
return v___x_1549_;
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_nat_dec_le(v___x_1547_, v___x_1547_);
if (v___x_1550_ == 0)
{
if (v___x_1548_ == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref(v_elems_1545_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_as_1508_);
lean_ctor_set(v___x_1551_, 1, v_a_1510_);
return v___x_1551_;
}
else
{
size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = lean_usize_of_nat(v___x_1547_);
v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1545_, v___x_1552_, v___x_1553_, v_as_1508_, v_a_1510_);
lean_dec_ref(v_elems_1545_);
return v___x_1554_;
}
}
else
{
size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = lean_usize_of_nat(v___x_1547_);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_elems_1545_, v___x_1555_, v___x_1556_, v_as_1508_, v_a_1510_);
lean_dec_ref(v_elems_1545_);
return v___x_1557_;
}
}
}
default: 
{
lean_object* v_kvPairs_1558_; lean_object* v___x_1559_; 
v_kvPairs_1558_ = lean_ctor_get(v_o_1509_, 0);
lean_inc(v_kvPairs_1558_);
lean_dec_ref(v_o_1509_);
v___x_1559_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_as_1508_, v_kvPairs_1558_, v_a_1510_);
return v___x_1559_;
}
}
v___jp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_as_1508_);
lean_ctor_set(v___x_1514_, 1, v___y_1513_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(lean_object* v_as_1560_, size_t v_i_1561_, size_t v_stop_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_){
_start:
{
uint8_t v___x_1566_; 
v___x_1566_ = lean_usize_dec_eq(v_i_1561_, v_stop_1562_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_array_uget_borrowed(v_as_1560_, v_i_1561_);
lean_inc(v___x_1567_);
v___x_1568_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_b_1563_, v___x_1567_, v___y_1564_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_a_1570_; size_t v___x_1571_; size_t v___x_1572_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
v_a_1570_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1568_);
v___x_1571_ = ((size_t)1ULL);
v___x_1572_ = lean_usize_add(v_i_1561_, v___x_1571_);
v_i_1561_ = v___x_1572_;
v_b_1563_ = v_a_1569_;
v___y_1564_ = v_a_1570_;
goto _start;
}
else
{
return v___x_1568_;
}
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_b_1563_);
lean_ctor_set(v___x_1574_, 1, v___y_1564_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0___boxed(lean_object* v_as_1575_, lean_object* v_i_1576_, lean_object* v_stop_1577_, lean_object* v_b_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
size_t v_i_boxed_1581_; size_t v_stop_boxed_1582_; lean_object* v_res_1583_; 
v_i_boxed_1581_ = lean_unbox_usize(v_i_1576_);
lean_dec(v_i_1576_);
v_stop_boxed_1582_ = lean_unbox_usize(v_stop_1577_);
lean_dec(v_stop_1577_);
v_res_1583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__0(v_as_1575_, v_i_boxed_1581_, v_stop_boxed_1582_, v_b_1578_, v___y_1579_);
lean_dec_ref(v_as_1575_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1___boxed(lean_object* v_init_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go_spec__1(v_init_1584_, v_x_1585_, v___y_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go___boxed(lean_object* v_as_1589_, lean_object* v_o_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_as_1589_, v_o_1590_, v_a_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(lean_object* v_x_1594_, lean_object* v_x_1595_, lean_object* v___y_1596_){
_start:
{
if (lean_obj_tag(v_x_1595_) == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_x_1594_);
lean_ctor_set(v___x_1598_, 1, v___y_1596_);
return v___x_1598_;
}
else
{
lean_object* v_value_1599_; lean_object* v_tail_1600_; lean_object* v_out_1601_; lean_object* v___x_1602_; 
v_value_1599_ = lean_ctor_get(v_x_1595_, 1);
lean_inc(v_value_1599_);
v_tail_1600_ = lean_ctor_get(v_x_1595_, 2);
lean_inc(v_tail_1600_);
lean_dec_ref(v_x_1595_);
v_out_1601_ = lean_ctor_get(v_value_1599_, 0);
lean_inc(v_out_1601_);
lean_dec(v_value_1599_);
v___x_1602_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_collectOutputDescrs_go(v_x_1594_, v_out_1601_, v___y_1596_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v_a_1604_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
v_a_1604_ = lean_ctor_get(v___x_1602_, 1);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1602_);
v_x_1594_ = v_a_1603_;
v_x_1595_ = v_tail_1600_;
v___y_1596_ = v_a_1604_;
goto _start;
}
else
{
lean_dec(v_tail_1600_);
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0___boxed(lean_object* v_x_1606_, lean_object* v_x_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_x_1606_, v_x_1607_, v___y_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(lean_object* v_as_1611_, size_t v_i_1612_, size_t v_stop_1613_, lean_object* v_b_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_1617_; 
v___x_1617_ = lean_usize_dec_eq(v_i_1612_, v_stop_1613_);
if (v___x_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_array_uget_borrowed(v_as_1611_, v_i_1612_);
lean_inc(v___x_1618_);
v___x_1619_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_CacheMap_collectOutputDescrs_spec__0(v_b_1614_, v___x_1618_, v___y_1615_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v_a_1621_; size_t v___x_1622_; size_t v___x_1623_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
v_a_1621_ = lean_ctor_get(v___x_1619_, 1);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1619_);
v___x_1622_ = ((size_t)1ULL);
v___x_1623_ = lean_usize_add(v_i_1612_, v___x_1622_);
v_i_1612_ = v___x_1623_;
v_b_1614_ = v_a_1620_;
v___y_1615_ = v_a_1621_;
goto _start;
}
else
{
return v___x_1619_;
}
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_b_1614_);
lean_ctor_set(v___x_1625_, 1, v___y_1615_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1___boxed(lean_object* v_as_1626_, lean_object* v_i_1627_, lean_object* v_stop_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
size_t v_i_boxed_1632_; size_t v_stop_boxed_1633_; lean_object* v_res_1634_; 
v_i_boxed_1632_ = lean_unbox_usize(v_i_1627_);
lean_dec(v_i_1627_);
v_stop_boxed_1633_ = lean_unbox_usize(v_stop_1628_);
lean_dec(v_stop_1628_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_as_1626_, v_i_boxed_1632_, v_stop_boxed_1633_, v_b_1629_, v___y_1630_);
lean_dec_ref(v_as_1626_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs(lean_object* v_map_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_buckets_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1669_; 
v_buckets_1640_ = lean_ctor_get(v_map_1637_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_map_1637_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v_map_1637_, 0);
lean_dec(v_unused_1670_);
v___x_1642_ = v_map_1637_;
v_isShared_1643_ = v_isSharedCheck_1669_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_buckets_1640_);
lean_dec(v_map_1637_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1669_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___y_1648_; lean_object* v_a_1649_; lean_object* v___y_1656_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = ((lean_object*)(l_Lake_CacheMap_collectOutputDescrs___closed__0));
v___x_1646_ = lean_array_get_size(v_a_1638_);
v___x_1658_ = lean_array_get_size(v_buckets_1640_);
v___x_1659_ = lean_nat_dec_lt(v___x_1644_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref(v_buckets_1640_);
lean_inc_ref(v_a_1638_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1645_);
lean_ctor_set(v___x_1660_, 1, v_a_1638_);
v___y_1648_ = v___x_1660_;
v_a_1649_ = v_a_1638_;
goto v___jp_1647_;
}
else
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_nat_dec_le(v___x_1658_, v___x_1658_);
if (v___x_1661_ == 0)
{
if (v___x_1659_ == 0)
{
lean_object* v___x_1662_; 
lean_dec_ref(v_buckets_1640_);
lean_inc_ref(v_a_1638_);
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1645_);
lean_ctor_set(v___x_1662_, 1, v_a_1638_);
v___y_1648_ = v___x_1662_;
v_a_1649_ = v_a_1638_;
goto v___jp_1647_;
}
else
{
size_t v___x_1663_; size_t v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = ((size_t)0ULL);
v___x_1664_ = lean_usize_of_nat(v___x_1658_);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1640_, v___x_1663_, v___x_1664_, v___x_1645_, v_a_1638_);
lean_dec_ref(v_buckets_1640_);
v___y_1656_ = v___x_1665_;
goto v___jp_1655_;
}
}
else
{
size_t v___x_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = lean_usize_of_nat(v___x_1658_);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_collectOutputDescrs_spec__1(v_buckets_1640_, v___x_1666_, v___x_1667_, v___x_1645_, v_a_1638_);
lean_dec_ref(v_buckets_1640_);
v___y_1656_ = v___x_1668_;
goto v___jp_1655_;
}
}
v___jp_1647_:
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = lean_array_get_size(v_a_1649_);
v___x_1651_ = lean_nat_dec_eq(v___x_1646_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v___y_1648_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 1);
lean_ctor_set(v___x_1642_, 1, v_a_1649_);
lean_ctor_set(v___x_1642_, 0, v___x_1646_);
v___x_1653_ = v___x_1642_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_a_1649_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
else
{
lean_dec_ref(v_a_1649_);
lean_del_object(v___x_1642_);
return v___y_1648_;
}
}
v___jp_1655_:
{
if (lean_obj_tag(v___y_1656_) == 0)
{
lean_object* v_a_1657_; 
v_a_1657_ = lean_ctor_get(v___y_1656_, 1);
lean_inc(v_a_1657_);
v___y_1648_ = v___y_1656_;
v_a_1649_ = v_a_1657_;
goto v___jp_1647_;
}
else
{
lean_del_object(v___x_1642_);
return v___y_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheMap_collectOutputDescrs___boxed(lean_object* v_map_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lake_CacheMap_collectOutputDescrs(v_map_1671_, v_a_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk(lean_object* v_init_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_st_mk_ref(v_init_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_mk___boxed(lean_object* v_init_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lake_CacheRef_mk(v_init_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f(uint64_t v_inputHash_1681_, lean_object* v_cache_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_st_ref_take(v_cache_1682_);
v___x_1685_ = l_Lake_CacheMap_get_x3f(v_inputHash_1681_, v___x_1684_);
v___x_1686_ = lean_st_ref_set(v_cache_1682_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_get_x3f___boxed(lean_object* v_inputHash_1687_, lean_object* v_cache_1688_, lean_object* v_a_1689_){
_start:
{
uint64_t v_inputHash_boxed_1690_; lean_object* v_res_1691_; 
v_inputHash_boxed_1690_ = lean_unbox_uint64(v_inputHash_1687_);
lean_dec_ref(v_inputHash_1687_);
v_res_1691_ = l_Lake_CacheRef_get_x3f(v_inputHash_boxed_1690_, v_cache_1688_);
lean_dec(v_cache_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg(lean_object* v_inst_1692_, uint64_t v_inputHash_1693_, lean_object* v_val_1694_, lean_object* v_cache_1695_, uint8_t v_platformIndependent_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1698_ = lean_st_ref_take(v_cache_1695_);
v___x_1699_ = lean_apply_1(v_inst_1692_, v_val_1694_);
v___x_1700_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1693_, v___x_1699_, v___x_1698_, v_platformIndependent_1696_);
v___x_1701_ = lean_st_ref_set(v_cache_1695_, v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___redArg___boxed(lean_object* v_inst_1702_, lean_object* v_inputHash_1703_, lean_object* v_val_1704_, lean_object* v_cache_1705_, lean_object* v_platformIndependent_1706_, lean_object* v_a_1707_){
_start:
{
uint64_t v_inputHash_boxed_1708_; uint8_t v_platformIndependent_boxed_1709_; lean_object* v_res_1710_; 
v_inputHash_boxed_1708_ = lean_unbox_uint64(v_inputHash_1703_);
lean_dec_ref(v_inputHash_1703_);
v_platformIndependent_boxed_1709_ = lean_unbox(v_platformIndependent_1706_);
v_res_1710_ = l_Lake_CacheRef_insert___redArg(v_inst_1702_, v_inputHash_boxed_1708_, v_val_1704_, v_cache_1705_, v_platformIndependent_boxed_1709_);
lean_dec(v_cache_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert(lean_object* v_00_u03b1_1711_, lean_object* v_inst_1712_, uint64_t v_inputHash_1713_, lean_object* v_val_1714_, lean_object* v_cache_1715_, uint8_t v_platformIndependent_1716_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = lean_st_ref_take(v_cache_1715_);
v___x_1719_ = lean_apply_1(v_inst_1712_, v_val_1714_);
v___x_1720_ = l___private_Lake_Config_Cache_0__Lake_CacheMap_insertCore(v_inputHash_1713_, v___x_1719_, v___x_1718_, v_platformIndependent_1716_);
v___x_1721_ = lean_st_ref_set(v_cache_1715_, v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheRef_insert___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_inst_1723_, lean_object* v_inputHash_1724_, lean_object* v_val_1725_, lean_object* v_cache_1726_, lean_object* v_platformIndependent_1727_, lean_object* v_a_1728_){
_start:
{
uint64_t v_inputHash_boxed_1729_; uint8_t v_platformIndependent_boxed_1730_; lean_object* v_res_1731_; 
v_inputHash_boxed_1729_ = lean_unbox_uint64(v_inputHash_1724_);
lean_dec_ref(v_inputHash_1724_);
v_platformIndependent_boxed_1730_ = lean_unbox(v_platformIndependent_1727_);
v_res_1731_ = l_Lake_CacheRef_insert(v_00_u03b1_1722_, v_inst_1723_, v_inputHash_boxed_1729_, v_val_1725_, v_cache_1726_, v_platformIndependent_boxed_1730_);
lean_dec(v_cache_1726_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString(lean_object* v_s_1734_){
_start:
{
lean_inc_ref(v_s_1734_);
return v_s_1734_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_ofString___boxed(lean_object* v_s_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lake_CacheServiceName_ofString(v_s_1735_);
lean_dec_ref(v_s_1735_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString(lean_object* v_self_1737_){
_start:
{
lean_inc_ref(v_self_1737_);
return v_self_1737_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceName_toString___boxed(lean_object* v_self_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lake_CacheServiceName_toString(v_self_1738_);
lean_dec_ref(v_self_1738_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_fromJson_x3f(lean_object* v_j_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Json_getStr_x3f(v_j_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1743_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1743_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceName_toJson(lean_object* v_self_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1763_, 0, v_self_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(lean_object* v_x_1766_){
_start:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_unsigned_to_nat(1u);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx___boxed(lean_object* v_x_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorIdx(v_x_1769_);
lean_dec_ref(v_x_1769_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(lean_object* v_t_1771_, lean_object* v_k_1772_){
_start:
{
lean_object* v_s_1773_; lean_object* v___x_1774_; 
v_s_1773_ = lean_ctor_get(v_t_1771_, 0);
lean_inc_ref(v_s_1773_);
lean_dec_ref(v_t_1771_);
v___x_1774_ = lean_apply_1(v_k_1772_, v_s_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(lean_object* v_motive_1775_, lean_object* v_ctorIdx_1776_, lean_object* v_t_1777_, lean_object* v_h_1778_, lean_object* v_k_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1777_, v_k_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___boxed(lean_object* v_motive_1781_, lean_object* v_ctorIdx_1782_, lean_object* v_t_1783_, lean_object* v_h_1784_, lean_object* v_k_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim(v_motive_1781_, v_ctorIdx_1782_, v_t_1783_, v_h_1784_, v_k_1785_);
lean_dec(v_ctorIdx_1782_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim___redArg(lean_object* v_t_1787_, lean_object* v_str_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1787_, v_str_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_str_elim(lean_object* v_motive_1790_, lean_object* v_t_1791_, lean_object* v_h_1792_, lean_object* v_str_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1791_, v_str_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim___redArg(lean_object* v_t_1795_, lean_object* v_repo_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1795_, v_repo_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_repo_elim(lean_object* v_motive_1798_, lean_object* v_t_1799_, lean_object* v_h_1800_, lean_object* v_repo_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScopeImpl_ctorElim___redArg(v_t_1799_, v_repo_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofString(lean_object* v_s_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_s_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_ofRepo(lean_object* v_fullName_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_fullName_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheServiceScope_isRepo(lean_object* v_self_1807_){
_start:
{
if (lean_obj_tag(v_self_1807_) == 1)
{
uint8_t v___x_1808_; 
v___x_1808_ = 1;
return v___x_1808_;
}
else
{
uint8_t v___x_1809_; 
v___x_1809_ = 0;
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_isRepo___boxed(lean_object* v_self_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Lake_CacheServiceScope_isRepo(v_self_1810_);
lean_dec_ref(v_self_1810_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString(lean_object* v_self_1813_){
_start:
{
lean_object* v_s_1814_; 
v_s_1814_ = lean_ctor_get(v_self_1813_, 0);
lean_inc_ref(v_s_1814_);
return v_s_1814_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheServiceScope_toString___boxed(lean_object* v_self_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lake_CacheServiceScope_toString(v_self_1815_);
lean_dec_ref(v_self_1815_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(lean_object* v_self_1819_){
_start:
{
lean_object* v_s_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_s_1820_ = lean_ctor_get(v_self_1819_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_self_1819_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v_self_1819_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_s_1820_);
lean_dec(v_self_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 3);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_s_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_ofData(lean_object* v_data_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1839_, 0, v_data_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
lean_ctor_set(v___x_1839_, 2, v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_box(0);
return v___x_1841_;
}
else
{
lean_object* v_val_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_val_1842_ = lean_ctor_get(v_x_1840_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_x_1840_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v_x_1840_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_val_1842_);
lean_dec(v_x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 3);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_val_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
static lean_object* _init_l_Lake_CacheOutput_toJson___closed__3(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1854_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__2));
v___x_1855_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1856_ = lean_box(1);
v___x_1857_ = l_Lake_JsonObject_insertJson(v___x_1856_, v___x_1855_, v___x_1854_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_toJson(lean_object* v_out_1861_){
_start:
{
lean_object* v_data_1862_; lean_object* v_service_x3f_1863_; lean_object* v_scope_x3f_1864_; lean_object* v_obj_1866_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v_obj_1873_; 
v_data_1862_ = lean_ctor_get(v_out_1861_, 0);
lean_inc(v_data_1862_);
v_service_x3f_1863_ = lean_ctor_get(v_out_1861_, 1);
lean_inc(v_service_x3f_1863_);
v_scope_x3f_1864_ = lean_ctor_get(v_out_1861_, 2);
lean_inc(v_scope_x3f_1864_);
lean_dec_ref(v_out_1861_);
v___x_1870_ = lean_obj_once(&l_Lake_CacheOutput_toJson___closed__3, &l_Lake_CacheOutput_toJson___closed__3_once, _init_l_Lake_CacheOutput_toJson___closed__3);
v___x_1871_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_1872_ = l_Option_toJson___at___00Lake_CacheOutput_toJson_spec__0(v_service_x3f_1863_);
v_obj_1873_ = l_Lake_JsonObject_insertJson(v___x_1870_, v___x_1871_, v___x_1872_);
if (lean_obj_tag(v_scope_x3f_1864_) == 1)
{
lean_object* v_val_1874_; lean_object* v___y_1876_; uint8_t v___x_1879_; 
v_val_1874_ = lean_ctor_get(v_scope_x3f_1864_, 0);
lean_inc(v_val_1874_);
lean_dec_ref(v_scope_x3f_1864_);
v___x_1879_ = l_Lake_CacheServiceScope_isRepo(v_val_1874_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___y_1876_ = v___x_1880_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___y_1876_ = v___x_1881_;
goto v___jp_1875_;
}
v___jp_1875_:
{
lean_object* v___x_1877_; lean_object* v_obj_1878_; 
v___x_1877_ = l___private_Lake_Config_Cache_0__Lake_CacheServiceScope_toJson(v_val_1874_);
lean_inc_ref(v___y_1876_);
v_obj_1878_ = l_Lake_JsonObject_insertJson(v_obj_1873_, v___y_1876_, v___x_1877_);
v_obj_1866_ = v_obj_1878_;
goto v___jp_1865_;
}
}
else
{
lean_dec(v_scope_x3f_1864_);
v_obj_1866_ = v_obj_1873_;
goto v___jp_1865_;
}
v___jp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1868_ = l_Lake_JsonObject_insertJson(v_obj_1866_, v___x_1867_, v_data_1862_);
v___x_1869_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(lean_object* v_x_1886_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1887_;
}
else
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_Json_getStr_x3f(v_x_1886_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1905_; 
v_a_1897_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1899_ = v___x_1888_;
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1888_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v_a_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1___closed__0));
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Json_getStr_x3f(v_x_1906_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
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
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1925_; 
v_a_1917_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1919_ = v___x_1908_;
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1908_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1925_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_a_1917_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
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
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(lean_object* v_k_1926_, lean_object* v_t_1927_){
_start:
{
if (lean_obj_tag(v_t_1927_) == 0)
{
lean_object* v_k_1928_; lean_object* v_l_1929_; lean_object* v_r_1930_; uint8_t v___x_1931_; 
v_k_1928_ = lean_ctor_get(v_t_1927_, 1);
v_l_1929_ = lean_ctor_get(v_t_1927_, 3);
v_r_1930_ = lean_ctor_get(v_t_1927_, 4);
v___x_1931_ = lean_string_dec_lt(v_k_1926_, v_k_1928_);
if (v___x_1931_ == 0)
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_string_dec_eq(v_k_1926_, v_k_1928_);
if (v___x_1932_ == 0)
{
v_t_1927_ = v_r_1930_;
goto _start;
}
else
{
return v___x_1932_;
}
}
else
{
v_t_1927_ = v_l_1929_;
goto _start;
}
}
else
{
uint8_t v___x_1935_; 
v___x_1935_ = 0;
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg___boxed(lean_object* v_k_1936_, lean_object* v_t_1937_){
_start:
{
uint8_t v_res_1938_; lean_object* v_r_1939_; 
v_res_1938_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_1936_, v_t_1937_);
lean_dec(v_t_1937_);
lean_dec_ref(v_k_1936_);
v_r_1939_ = lean_box(v_res_1938_);
return v_r_1939_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheOutput_fromJson_x3f(lean_object* v_json_1946_){
_start:
{
if (lean_obj_tag(v_json_1946_) == 5)
{
lean_object* v_kvPairs_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v_kvPairs_1951_ = lean_ctor_get(v_json_1946_, 0);
v___x_1952_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__1));
v___x_1953_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v___x_1952_, v_kvPairs_1951_);
if (v___x_1953_ == 0)
{
goto v___jp_1947_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_inc(v_kvPairs_1951_);
lean_dec_ref(v_json_1946_);
v___x_1954_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_1955_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1951_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v___x_1956_; 
lean_dec(v_kvPairs_1951_);
v___x_1956_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__1));
return v___x_1956_;
}
else
{
lean_object* v_val_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2075_; 
v_val_1957_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_1959_ = v___x_1955_;
v_isShared_1960_ = v_isSharedCheck_2075_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_val_1957_);
lean_dec(v___x_1955_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2075_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___y_1962_; lean_object* v_a_1963_; lean_object* v___y_1969_; lean_object* v___y_1972_; lean_object* v_a_2012_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__4));
v___x_2052_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1951_, v___x_2051_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_box(0);
v_a_2012_ = v___x_2053_;
goto v___jp_2011_;
}
else
{
lean_object* v_val_2054_; lean_object* v___x_2055_; 
v_val_2054_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_val_2054_);
lean_dec_ref(v___x_2052_);
v___x_2055_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__2(v_val_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2065_; 
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
lean_dec(v_kvPairs_1951_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2065_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2065_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2060_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__4));
v___x_2061_ = lean_string_append(v___x_2060_, v_a_2056_);
lean_dec(v_a_2056_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2061_);
v___x_2063_ = v___x_2058_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
lean_dec(v_kvPairs_1951_);
v_a_2066_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2055_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2055_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 0);
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2055_);
v_a_2012_ = v_a_2074_;
goto v___jp_2011_;
}
}
}
v___jp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1964_, 0, v_val_1957_);
lean_ctor_set(v___x_1964_, 1, v___y_1962_);
lean_ctor_set(v___x_1964_, 2, v_a_1963_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1964_);
v___x_1966_ = v___x_1959_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
v___jp_1968_:
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_box(0);
v___y_1962_ = v___y_1969_;
v_a_1963_ = v___x_1970_;
goto v___jp_1961_;
}
v___jp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__5));
v___x_1974_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1951_, v___x_1973_);
lean_dec(v_kvPairs_1951_);
if (lean_obj_tag(v___x_1974_) == 0)
{
v___y_1969_ = v___y_1972_;
goto v___jp_1968_;
}
else
{
lean_object* v_val_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2010_; 
v_val_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2010_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_val_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2010_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_1975_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1989_; 
lean_del_object(v___x_1977_);
lean_dec(v___y_1972_);
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1989_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1989_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1984_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__2));
v___x_1985_ = lean_string_append(v___x_1984_, v_a_1980_);
lean_dec(v_a_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1985_);
v___x_1987_ = v___x_1982_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_del_object(v___x_1977_);
lean_dec(v___y_1972_);
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
v_a_1990_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1979_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1979_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 0);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
lean_object* v_a_1998_; 
v_a_1998_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1979_);
if (lean_obj_tag(v_a_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2009_; 
v_val_1999_ = lean_ctor_get(v_a_1998_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2001_ = v_a_1998_;
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v_a_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 0);
lean_ctor_set(v___x_1977_, 0, v_val_1999_);
v___x_2004_ = v___x_1977_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_val_1999_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
v___y_1962_ = v___y_1972_;
v_a_1963_ = v___x_2006_;
goto v___jp_1961_;
}
}
}
}
else
{
lean_dec(v_a_1998_);
lean_del_object(v___x_1977_);
v___y_1969_ = v___y_1972_;
goto v___jp_1968_;
}
}
}
}
}
}
v___jp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__6));
v___x_2014_ = l_Lake_JsonObject_getJson_x3f(v_kvPairs_1951_, v___x_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
v___y_1972_ = v_a_2012_;
goto v___jp_1971_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2050_; 
v_val_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2050_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2050_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Option_fromJson_x3f___at___00Lake_CacheOutput_fromJson_x3f_spec__1(v_val_2015_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2029_; 
lean_del_object(v___x_2017_);
lean_dec(v_a_2012_);
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
lean_dec(v_kvPairs_1951_);
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2024_ = ((lean_object*)(l_Lake_CacheOutput_fromJson_x3f___closed__3));
v___x_2025_ = lean_string_append(v___x_2024_, v_a_2020_);
lean_dec(v_a_2020_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2025_);
v___x_2027_ = v___x_2022_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_del_object(v___x_2017_);
lean_dec(v_a_2012_);
lean_del_object(v___x_1959_);
lean_dec(v_val_1957_);
lean_dec(v_kvPairs_1951_);
v_a_2030_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2019_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2019_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 0);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2019_);
if (lean_obj_tag(v_a_2038_) == 1)
{
lean_object* v_val_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_kvPairs_1951_);
v_val_2039_ = lean_ctor_get(v_a_2038_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2041_ = v_a_2038_;
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_val_2039_);
lean_dec(v_a_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2049_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v_val_2039_);
v___x_2044_ = v___x_2017_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_val_2039_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2044_);
v___x_2046_ = v___x_2041_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
v___y_1962_ = v_a_2012_;
v_a_1963_ = v___x_2046_;
goto v___jp_1961_;
}
}
}
}
else
{
lean_dec(v_a_2038_);
lean_del_object(v___x_2017_);
v___y_1972_ = v_a_2012_;
goto v___jp_1971_;
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
goto v___jp_1947_;
}
v___jp_1947_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1949_, 0, v_json_1946_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
lean_ctor_set(v___x_1949_, 2, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(lean_object* v_00_u03b2_2076_, lean_object* v_k_2077_, lean_object* v_t_2078_){
_start:
{
uint8_t v___x_2079_; 
v___x_2079_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___redArg(v_k_2077_, v_t_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0___boxed(lean_object* v_00_u03b2_2080_, lean_object* v_k_2081_, lean_object* v_t_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lake_CacheOutput_fromJson_x3f_spec__0(v_00_u03b2_2080_, v_k_2081_, v_t_2082_);
lean_dec(v_t_2082_);
lean_dec_ref(v_k_2081_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactDir(lean_object* v_cache_2091_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2093_ = l_System_FilePath_join(v_cache_2091_, v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath(lean_object* v_cache_2095_, uint64_t v_contentHash_2096_, lean_object* v_ext_2097_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2098_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2099_ = l_System_FilePath_join(v_cache_2095_, v___x_2098_);
v___x_2100_ = lean_string_utf8_byte_size(v_ext_2097_);
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_nat_dec_eq(v___x_2100_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2103_ = l_Lake_lowerHexUInt64(v_contentHash_2096_);
v___x_2104_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2105_ = lean_string_append(v___x_2103_, v___x_2104_);
v___x_2106_ = lean_string_append(v___x_2105_, v_ext_2097_);
v___x_2107_ = l_System_FilePath_join(v___x_2099_, v___x_2106_);
return v___x_2107_;
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = l_Lake_lowerHexUInt64(v_contentHash_2096_);
v___x_2109_ = l_System_FilePath_join(v___x_2099_, v___x_2108_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_artifactPath___boxed(lean_object* v_cache_2110_, lean_object* v_contentHash_2111_, lean_object* v_ext_2112_){
_start:
{
uint64_t v_contentHash_boxed_2113_; lean_object* v_res_2114_; 
v_contentHash_boxed_2113_ = lean_unbox_uint64(v_contentHash_2111_);
lean_dec_ref(v_contentHash_2111_);
v_res_2114_ = l_Lake_Cache_artifactPath(v_cache_2110_, v_contentHash_boxed_2113_, v_ext_2112_);
lean_dec_ref(v_ext_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f(lean_object* v_cache_2115_, lean_object* v_descr_2116_){
_start:
{
uint64_t v_hash_2118_; lean_object* v_ext_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___y_2123_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_hash_2118_ = lean_ctor_get_uint64(v_descr_2116_, sizeof(void*)*1);
v_ext_2119_ = lean_ctor_get(v_descr_2116_, 0);
v___x_2120_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2121_ = l_System_FilePath_join(v_cache_2115_, v___x_2120_);
v___x_2137_ = lean_string_utf8_byte_size(v_ext_2119_);
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = lean_nat_dec_eq(v___x_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = l_Lake_lowerHexUInt64(v_hash_2118_);
v___x_2141_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2142_ = lean_string_append(v___x_2140_, v___x_2141_);
v___x_2143_ = lean_string_append(v___x_2142_, v_ext_2119_);
v___y_2123_ = v___x_2143_;
goto v___jp_2122_;
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lake_lowerHexUInt64(v_hash_2118_);
v___y_2123_ = v___x_2144_;
goto v___jp_2122_;
}
v___jp_2122_:
{
lean_object* v_path_2124_; lean_object* v___x_2125_; 
v_path_2124_ = l_System_FilePath_join(v___x_2121_, v___y_2123_);
v___x_2125_ = lean_io_metadata(v_path_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2135_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2135_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2135_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_modified_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v_modified_2130_ = lean_ctor_get(v_a_2126_, 1);
lean_inc_ref(v_modified_2130_);
lean_dec(v_a_2126_);
lean_inc_ref(v_path_2124_);
v___x_2131_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2131_, 0, v_descr_2116_);
lean_ctor_set(v___x_2131_, 1, v_path_2124_);
lean_ctor_set(v___x_2131_, 2, v_path_2124_);
lean_ctor_set(v___x_2131_, 3, v_modified_2130_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2131_);
v___x_2133_ = v___x_2128_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
else
{
lean_object* v___x_2136_; 
lean_dec_ref(v___x_2125_);
lean_dec_ref(v_path_2124_);
lean_dec_ref(v_descr_2116_);
v___x_2136_ = lean_box(0);
return v___x_2136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object* v_cache_2145_, lean_object* v_descr_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lake_Cache_getArtifact_x3f(v_cache_2145_, v_descr_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact(lean_object* v_cache_2151_, lean_object* v_descr_2152_){
_start:
{
uint64_t v_hash_2154_; lean_object* v_ext_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___y_2159_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v_hash_2154_ = lean_ctor_get_uint64(v_descr_2152_, sizeof(void*)*1);
v_ext_2155_ = lean_ctor_get(v_descr_2152_, 0);
v___x_2156_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_2157_ = l_System_FilePath_join(v_cache_2151_, v___x_2156_);
v___x_2188_ = lean_string_utf8_byte_size(v_ext_2155_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_nat_dec_eq(v___x_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2191_ = l_Lake_lowerHexUInt64(v_hash_2154_);
v___x_2192_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_2193_ = lean_string_append(v___x_2191_, v___x_2192_);
v___x_2194_ = lean_string_append(v___x_2193_, v_ext_2155_);
v___y_2159_ = v___x_2194_;
goto v___jp_2158_;
}
else
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lake_lowerHexUInt64(v_hash_2154_);
v___y_2159_ = v___x_2195_;
goto v___jp_2158_;
}
v___jp_2158_:
{
lean_object* v_path_2160_; lean_object* v___x_2161_; 
v_path_2160_ = l_System_FilePath_join(v___x_2157_, v___y_2159_);
v___x_2161_ = lean_io_metadata(v_path_2160_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2171_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2171_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v_modified_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v_modified_2166_ = lean_ctor_get(v_a_2162_, 1);
lean_inc_ref(v_modified_2166_);
lean_dec(v_a_2162_);
lean_inc_ref(v_path_2160_);
v___x_2167_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2167_, 0, v_descr_2152_);
lean_ctor_set(v___x_2167_, 1, v_path_2160_);
lean_ctor_set(v___x_2167_, 2, v_path_2160_);
lean_ctor_set(v___x_2167_, 3, v_modified_2166_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2167_);
v___x_2169_ = v___x_2164_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_descr_2152_);
v_a_2172_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2174_ = v___x_2161_;
v_isShared_2175_ = v_isSharedCheck_2187_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2161_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2187_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
if (lean_obj_tag(v_a_2172_) == 11)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
lean_dec_ref(v_a_2172_);
v___x_2176_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__0));
v___x_2177_ = lean_string_append(v___x_2176_, v_path_2160_);
lean_dec_ref(v_path_2160_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2177_);
v___x_2179_ = v___x_2174_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec_ref(v_path_2160_);
v___x_2181_ = ((lean_object*)(l_Lake_Cache_getArtifact___closed__1));
v___x_2182_ = lean_io_error_to_string(v_a_2172_);
v___x_2183_ = lean_string_append(v___x_2181_, v___x_2182_);
lean_dec_ref(v___x_2182_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2183_);
v___x_2185_ = v___x_2174_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_getArtifact___boxed(lean_object* v_cache_2196_, lean_object* v_descr_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lake_Cache_getArtifact(v_cache_2196_, v_descr_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsDir(lean_object* v_cache_2201_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2203_ = l_System_FilePath_join(v_cache_2201_, v___x_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile(lean_object* v_cache_2205_, lean_object* v_scope_2206_, uint64_t v_inputHash_2207_){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2208_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2209_ = l_System_FilePath_join(v_cache_2205_, v___x_2208_);
v___x_2210_ = l_System_FilePath_join(v___x_2209_, v_scope_2206_);
v___x_2211_ = l_Lake_lowerHexUInt64(v_inputHash_2207_);
v___x_2212_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2213_ = lean_string_append(v___x_2211_, v___x_2212_);
v___x_2214_ = l_System_FilePath_join(v___x_2210_, v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_outputsFile___boxed(lean_object* v_cache_2215_, lean_object* v_scope_2216_, lean_object* v_inputHash_2217_){
_start:
{
uint64_t v_inputHash_boxed_2218_; lean_object* v_res_2219_; 
v_inputHash_boxed_2218_ = lean_unbox_uint64(v_inputHash_2217_);
lean_dec_ref(v_inputHash_2217_);
v_res_2219_ = l_Lake_Cache_outputsFile(v_cache_2215_, v_scope_2216_, v_inputHash_boxed_2218_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(lean_object* v_cache_2220_, lean_object* v_scope_2221_, uint64_t v_inputHash_2222_, lean_object* v_out_2223_, lean_object* v_service_x3f_2224_, lean_object* v_remoteScope_x3f_2225_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v_file_2233_; lean_object* v___x_2234_; 
v___x_2227_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2228_ = l_System_FilePath_join(v_cache_2220_, v___x_2227_);
v___x_2229_ = l_System_FilePath_join(v___x_2228_, v_scope_2221_);
v___x_2230_ = l_Lake_lowerHexUInt64(v_inputHash_2222_);
v___x_2231_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2232_ = lean_string_append(v___x_2230_, v___x_2231_);
v_file_2233_ = l_System_FilePath_join(v___x_2229_, v___x_2232_);
lean_inc_ref(v_file_2233_);
v___x_2234_ = l_Lake_createParentDirs(v_file_2233_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref(v___x_2234_);
v___x_2235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2235_, 0, v_out_2223_);
lean_ctor_set(v___x_2235_, 1, v_service_x3f_2224_);
lean_ctor_set(v___x_2235_, 2, v_remoteScope_x3f_2225_);
v___x_2236_ = l_Lake_CacheOutput_toJson(v___x_2235_);
v___x_2237_ = lean_unsigned_to_nat(80u);
v___x_2238_ = l_Lean_Json_pretty(v___x_2236_, v___x_2237_);
v___x_2239_ = l_IO_FS_writeFile(v_file_2233_, v___x_2238_);
lean_dec_ref(v___x_2238_);
lean_dec_ref(v_file_2233_);
return v___x_2239_;
}
else
{
lean_dec_ref(v_file_2233_);
lean_dec(v_remoteScope_x3f_2225_);
lean_dec(v_service_x3f_2224_);
lean_dec(v_out_2223_);
return v___x_2234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore___boxed(lean_object* v_cache_2240_, lean_object* v_scope_2241_, lean_object* v_inputHash_2242_, lean_object* v_out_2243_, lean_object* v_service_x3f_2244_, lean_object* v_remoteScope_x3f_2245_, lean_object* v_a_2246_){
_start:
{
uint64_t v_inputHash_boxed_2247_; lean_object* v_res_2248_; 
v_inputHash_boxed_2247_ = lean_unbox_uint64(v_inputHash_2242_);
lean_dec_ref(v_inputHash_2242_);
v_res_2248_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2240_, v_scope_2241_, v_inputHash_boxed_2247_, v_out_2243_, v_service_x3f_2244_, v_remoteScope_x3f_2245_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg(lean_object* v_inst_2249_, lean_object* v_cache_2250_, lean_object* v_scope_2251_, uint64_t v_inputHash_2252_, lean_object* v_outputs_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_apply_1(v_inst_2249_, v_outputs_2253_);
v___x_2256_ = lean_box(0);
v___x_2257_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2250_, v_scope_2251_, v_inputHash_2252_, v___x_2255_, v___x_2256_, v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___redArg___boxed(lean_object* v_inst_2258_, lean_object* v_cache_2259_, lean_object* v_scope_2260_, lean_object* v_inputHash_2261_, lean_object* v_outputs_2262_, lean_object* v_a_2263_){
_start:
{
uint64_t v_inputHash_boxed_2264_; lean_object* v_res_2265_; 
v_inputHash_boxed_2264_ = lean_unbox_uint64(v_inputHash_2261_);
lean_dec_ref(v_inputHash_2261_);
v_res_2265_ = l_Lake_Cache_writeOutputs___redArg(v_inst_2258_, v_cache_2259_, v_scope_2260_, v_inputHash_boxed_2264_, v_outputs_2262_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs(lean_object* v_00_u03b1_2266_, lean_object* v_inst_2267_, lean_object* v_cache_2268_, lean_object* v_scope_2269_, uint64_t v_inputHash_2270_, lean_object* v_outputs_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2273_ = lean_apply_1(v_inst_2267_, v_outputs_2271_);
v___x_2274_ = lean_box(0);
v___x_2275_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2268_, v_scope_2269_, v_inputHash_2270_, v___x_2273_, v___x_2274_, v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeOutputs___boxed(lean_object* v_00_u03b1_2276_, lean_object* v_inst_2277_, lean_object* v_cache_2278_, lean_object* v_scope_2279_, lean_object* v_inputHash_2280_, lean_object* v_outputs_2281_, lean_object* v_a_2282_){
_start:
{
uint64_t v_inputHash_boxed_2283_; lean_object* v_res_2284_; 
v_inputHash_boxed_2283_ = lean_unbox_uint64(v_inputHash_2280_);
lean_dec_ref(v_inputHash_2280_);
v_res_2284_ = l_Lake_Cache_writeOutputs(v_00_u03b1_2276_, v_inst_2277_, v_cache_2278_, v_scope_2279_, v_inputHash_boxed_2283_, v_outputs_2281_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(lean_object* v_cache_2285_, lean_object* v_scope_2286_, lean_object* v_service_x3f_2287_, lean_object* v_remoteScope_x3f_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_){
_start:
{
if (lean_obj_tag(v_x_2290_) == 0)
{
lean_object* v___x_2292_; 
lean_dec(v_remoteScope_x3f_2288_);
lean_dec(v_service_x3f_2287_);
lean_dec_ref(v_scope_2286_);
lean_dec_ref(v_cache_2285_);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_x_2289_);
return v___x_2292_;
}
else
{
lean_object* v_value_2293_; lean_object* v_key_2294_; lean_object* v_tail_2295_; lean_object* v_out_2296_; uint64_t v___x_2297_; lean_object* v___x_2298_; 
v_value_2293_ = lean_ctor_get(v_x_2290_, 1);
lean_inc(v_value_2293_);
v_key_2294_ = lean_ctor_get(v_x_2290_, 0);
lean_inc(v_key_2294_);
v_tail_2295_ = lean_ctor_get(v_x_2290_, 2);
lean_inc(v_tail_2295_);
lean_dec_ref(v_x_2290_);
v_out_2296_ = lean_ctor_get(v_value_2293_, 0);
lean_inc(v_out_2296_);
lean_dec(v_value_2293_);
v___x_2297_ = lean_unbox_uint64(v_key_2294_);
lean_dec(v_key_2294_);
lean_inc(v_remoteScope_x3f_2288_);
lean_inc(v_service_x3f_2287_);
lean_inc_ref(v_scope_2286_);
lean_inc_ref(v_cache_2285_);
v___x_2298_ = l___private_Lake_Config_Cache_0__Lake_Cache_writeOutputsCore(v_cache_2285_, v_scope_2286_, v___x_2297_, v_out_2296_, v_service_x3f_2287_, v_remoteScope_x3f_2288_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2298_);
v_x_2289_ = v_a_2299_;
v_x_2290_ = v_tail_2295_;
goto _start;
}
else
{
lean_dec(v_tail_2295_);
lean_dec(v_remoteScope_x3f_2288_);
lean_dec(v_service_x3f_2287_);
lean_dec_ref(v_scope_2286_);
lean_dec_ref(v_cache_2285_);
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0___boxed(lean_object* v_cache_2301_, lean_object* v_scope_2302_, lean_object* v_service_x3f_2303_, lean_object* v_remoteScope_x3f_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2301_, v_scope_2302_, v_service_x3f_2303_, v_remoteScope_x3f_2304_, v_x_2305_, v_x_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(lean_object* v_cache_2309_, lean_object* v_scope_2310_, lean_object* v_service_x3f_2311_, lean_object* v_remoteScope_x3f_2312_, lean_object* v_as_2313_, size_t v_i_2314_, size_t v_stop_2315_, lean_object* v_b_2316_){
_start:
{
uint8_t v___x_2318_; 
v___x_2318_ = lean_usize_dec_eq(v_i_2314_, v_stop_2315_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = lean_array_uget_borrowed(v_as_2313_, v_i_2314_);
v___x_2320_ = lean_box(0);
lean_inc(v___x_2319_);
lean_inc(v_remoteScope_x3f_2312_);
lean_inc(v_service_x3f_2311_);
lean_inc_ref(v_scope_2310_);
lean_inc_ref(v_cache_2309_);
v___x_2321_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Cache_writeMap_spec__0(v_cache_2309_, v_scope_2310_, v_service_x3f_2311_, v_remoteScope_x3f_2312_, v___x_2320_, v___x_2319_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; size_t v___x_2323_; size_t v___x_2324_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2314_, v___x_2323_);
v_i_2314_ = v___x_2324_;
v_b_2316_ = v_a_2322_;
goto _start;
}
else
{
lean_dec(v_remoteScope_x3f_2312_);
lean_dec(v_service_x3f_2311_);
lean_dec_ref(v_scope_2310_);
lean_dec_ref(v_cache_2309_);
return v___x_2321_;
}
}
else
{
lean_object* v___x_2326_; 
lean_dec(v_remoteScope_x3f_2312_);
lean_dec(v_service_x3f_2311_);
lean_dec_ref(v_scope_2310_);
lean_dec_ref(v_cache_2309_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v_b_2316_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1___boxed(lean_object* v_cache_2327_, lean_object* v_scope_2328_, lean_object* v_service_x3f_2329_, lean_object* v_remoteScope_x3f_2330_, lean_object* v_as_2331_, lean_object* v_i_2332_, lean_object* v_stop_2333_, lean_object* v_b_2334_, lean_object* v___y_2335_){
_start:
{
size_t v_i_boxed_2336_; size_t v_stop_boxed_2337_; lean_object* v_res_2338_; 
v_i_boxed_2336_ = lean_unbox_usize(v_i_2332_);
lean_dec(v_i_2332_);
v_stop_boxed_2337_ = lean_unbox_usize(v_stop_2333_);
lean_dec(v_stop_2333_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2327_, v_scope_2328_, v_service_x3f_2329_, v_remoteScope_x3f_2330_, v_as_2331_, v_i_boxed_2336_, v_stop_boxed_2337_, v_b_2334_);
lean_dec_ref(v_as_2331_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap(lean_object* v_cache_2339_, lean_object* v_scope_2340_, lean_object* v_map_2341_, lean_object* v_service_x3f_2342_, lean_object* v_remoteScope_x3f_2343_){
_start:
{
lean_object* v_buckets_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_buckets_2345_ = lean_ctor_get(v_map_2341_, 1);
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_array_get_size(v_buckets_2345_);
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; 
lean_dec(v_remoteScope_x3f_2343_);
lean_dec(v_service_x3f_2342_);
lean_dec_ref(v_scope_2340_);
lean_dec_ref(v_cache_2339_);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
return v___x_2350_;
}
else
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_nat_dec_le(v___x_2347_, v___x_2347_);
if (v___x_2351_ == 0)
{
if (v___x_2349_ == 0)
{
lean_object* v___x_2352_; 
lean_dec(v_remoteScope_x3f_2343_);
lean_dec(v_service_x3f_2342_);
lean_dec_ref(v_scope_2340_);
lean_dec_ref(v_cache_2339_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2348_);
return v___x_2352_;
}
else
{
size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = ((size_t)0ULL);
v___x_2354_ = lean_usize_of_nat(v___x_2347_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2339_, v_scope_2340_, v_service_x3f_2342_, v_remoteScope_x3f_2343_, v_buckets_2345_, v___x_2353_, v___x_2354_, v___x_2348_);
return v___x_2355_;
}
}
else
{
size_t v___x_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((size_t)0ULL);
v___x_2357_ = lean_usize_of_nat(v___x_2347_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Cache_writeMap_spec__1(v_cache_2339_, v_scope_2340_, v_service_x3f_2342_, v_remoteScope_x3f_2343_, v_buckets_2345_, v___x_2356_, v___x_2357_, v___x_2348_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_writeMap___boxed(lean_object* v_cache_2359_, lean_object* v_scope_2360_, lean_object* v_map_2361_, lean_object* v_service_x3f_2362_, lean_object* v_remoteScope_x3f_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lake_Cache_writeMap(v_cache_2359_, v_scope_2360_, v_map_2361_, v_service_x3f_2362_, v_remoteScope_x3f_2363_);
lean_dec_ref(v_map_2361_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(lean_object* v_x_2368_){
_start:
{
if (lean_obj_tag(v_x_2368_) == 0)
{
lean_object* v___x_2369_; 
v___x_2369_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0___closed__0));
return v___x_2369_;
}
else
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lake_CacheOutput_fromJson_x3f(v_x_2368_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2387_; 
v_a_2379_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2381_ = v___x_2370_;
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2370_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2387_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_a_2379_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f(lean_object* v_cache_2390_, lean_object* v_scope_2391_, uint64_t v_inputHash_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v_path_2401_; lean_object* v___x_2402_; 
v___x_2395_ = ((lean_object*)(l_Lake_Cache_outputsDir___closed__0));
v___x_2396_ = l_System_FilePath_join(v_cache_2390_, v___x_2395_);
v___x_2397_ = l_System_FilePath_join(v___x_2396_, v_scope_2391_);
v___x_2398_ = l_Lake_lowerHexUInt64(v_inputHash_2392_);
v___x_2399_ = ((lean_object*)(l_Lake_Cache_outputsFile___closed__0));
v___x_2400_ = lean_string_append(v___x_2398_, v___x_2399_);
v_path_2401_ = l_System_FilePath_join(v___x_2397_, v___x_2400_);
v___x_2402_ = l_IO_FS_readFile(v_path_2401_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v_a_2405_; lean_object* v___x_2414_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___x_2402_);
v___x_2414_ = l_Lean_Json_parse(v_a_2403_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref(v___x_2414_);
v_a_2405_ = v_a_2415_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2417_; 
v_a_2416_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2416_);
lean_dec_ref(v___x_2414_);
v___x_2417_ = l_Option_fromJson_x3f___at___00Lake_Cache_readOutputs_x3f_spec__0(v_a_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref(v___x_2417_);
v_a_2405_ = v_a_2418_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
lean_dec_ref(v_path_2401_);
v_a_2419_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2417_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v_a_2419_);
lean_ctor_set(v___x_2420_, 1, v_a_2393_);
return v___x_2420_;
}
}
v___jp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2406_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__0));
v___x_2407_ = lean_string_append(v_path_2401_, v___x_2406_);
v___x_2408_ = lean_string_append(v___x_2407_, v_a_2405_);
lean_dec_ref(v_a_2405_);
v___x_2409_ = 2;
v___x_2410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*1, v___x_2409_);
v___x_2411_ = lean_array_push(v_a_2393_, v___x_2410_);
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v___x_2411_);
return v___x_2413_;
}
}
else
{
lean_object* v_a_2421_; 
v_a_2421_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2402_);
if (lean_obj_tag(v_a_2421_) == 11)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec_ref(v_a_2421_);
lean_dec_ref(v_path_2401_);
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
lean_ctor_set(v___x_2423_, 1, v_a_2393_);
return v___x_2423_;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2424_ = ((lean_object*)(l_Lake_Cache_readOutputs_x3f___closed__1));
v___x_2425_ = lean_string_append(v_path_2401_, v___x_2424_);
v___x_2426_ = lean_io_error_to_string(v_a_2421_);
v___x_2427_ = lean_string_append(v___x_2425_, v___x_2426_);
lean_dec_ref(v___x_2426_);
v___x_2428_ = 3;
v___x_2429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set_uint8(v___x_2429_, sizeof(void*)*1, v___x_2428_);
v___x_2430_ = lean_array_get_size(v_a_2393_);
v___x_2431_ = lean_array_push(v_a_2393_, v___x_2429_);
v___x_2432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2430_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
return v___x_2432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_readOutputs_x3f___boxed(lean_object* v_cache_2433_, lean_object* v_scope_2434_, lean_object* v_inputHash_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
uint64_t v_inputHash_boxed_2438_; lean_object* v_res_2439_; 
v_inputHash_boxed_2438_ = lean_unbox_uint64(v_inputHash_2435_);
lean_dec_ref(v_inputHash_2435_);
v_res_2439_ = l_Lake_Cache_readOutputs_x3f(v_cache_2433_, v_scope_2434_, v_inputHash_boxed_2438_, v_a_2436_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionDir(lean_object* v_cache_2441_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2443_ = l_System_FilePath_join(v_cache_2441_, v___x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lake_Cache_revisionPath(lean_object* v_cache_2445_, lean_object* v_scope_2446_, lean_object* v_rev_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2448_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_2449_ = l_System_FilePath_join(v_cache_2445_, v___x_2448_);
v___x_2450_ = l_System_FilePath_join(v___x_2449_, v_scope_2446_);
v___x_2451_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_2452_ = lean_string_append(v_rev_2447_, v___x_2451_);
v___x_2453_ = l_System_FilePath_join(v___x_2450_, v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT uint8_t l_Lake_CachePlatform_isNone(lean_object* v_self_2455_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2456_ = lean_string_utf8_byte_size(v_self_2455_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_nat_dec_eq(v___x_2456_, v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_isNone___boxed(lean_object* v_self_2459_){
_start:
{
uint8_t v_res_2460_; lean_object* v_r_2461_; 
v_res_2460_ = l_Lake_CachePlatform_isNone(v_self_2459_);
lean_dec_ref(v_self_2459_);
v_r_2461_ = lean_box(v_res_2460_);
return v_r_2461_;
}
}
static lean_object* _init_l_Lake_CachePlatform_system(void){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_System_Platform_target;
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString(lean_object* v_s_2463_){
_start:
{
lean_inc_ref(v_s_2463_);
return v_s_2463_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_ofString___boxed(lean_object* v_s_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lake_CachePlatform_ofString(v_s_2464_);
lean_dec_ref(v_s_2464_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(lean_object* v___x_2466_, lean_object* v___x_2467_, lean_object* v_a_2468_, lean_object* v_b_2469_){
_start:
{
lean_object* v_startInclusive_2470_; lean_object* v_endExclusive_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v_startInclusive_2470_ = lean_ctor_get(v___x_2466_, 1);
v_endExclusive_2471_ = lean_ctor_get(v___x_2466_, 2);
v___x_2472_ = lean_nat_sub(v_endExclusive_2471_, v_startInclusive_2470_);
v___x_2473_ = lean_nat_dec_eq(v_a_2468_, v___x_2472_);
lean_dec(v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_string_utf8_next_fast(v___x_2467_, v_a_2468_);
lean_dec(v_a_2468_);
v___x_2475_ = lean_unsigned_to_nat(1u);
v___x_2476_ = lean_nat_add(v_b_2469_, v___x_2475_);
lean_dec(v_b_2469_);
v_a_2468_ = v___x_2474_;
v_b_2469_ = v___x_2476_;
goto _start;
}
else
{
lean_dec(v_a_2468_);
return v_b_2469_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg___boxed(lean_object* v___x_2478_, lean_object* v___x_2479_, lean_object* v_a_2480_, lean_object* v_b_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2478_, v___x_2479_, v_a_2480_, v_b_2481_);
lean_dec_ref(v___x_2479_);
lean_dec_ref(v___x_2478_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_length(lean_object* v_self_2483_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2484_ = lean_unsigned_to_nat(0u);
v___x_2485_ = lean_string_utf8_byte_size(v_self_2483_);
lean_inc_ref(v_self_2483_);
v___x_2486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2486_, 0, v_self_2483_);
lean_ctor_set(v___x_2486_, 1, v___x_2484_);
lean_ctor_set(v___x_2486_, 2, v___x_2485_);
v___x_2487_ = l_String_Slice_positions(v___x_2486_);
v___x_2488_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2486_, v_self_2483_, v___x_2487_, v___x_2484_);
lean_dec_ref(v_self_2483_);
lean_dec_ref(v___x_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(lean_object* v___x_2489_, lean_object* v___x_2490_, lean_object* v_inst_2491_, lean_object* v_R_2492_, lean_object* v_a_2493_, lean_object* v_b_2494_, lean_object* v_c_2495_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2489_, v___x_2490_, v_a_2493_, v_b_2494_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___boxed(lean_object* v___x_2497_, lean_object* v___x_2498_, lean_object* v_inst_2499_, lean_object* v_R_2500_, lean_object* v_a_2501_, lean_object* v_b_2502_, lean_object* v_c_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0(v___x_2497_, v___x_2498_, v_inst_2499_, v_R_2500_, v_a_2501_, v_b_2502_, v_c_2503_);
lean_dec_ref(v___x_2498_);
lean_dec_ref(v___x_2497_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString(lean_object* v_self_2506_){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2507_ = lean_string_utf8_byte_size(v_self_2506_);
v___x_2508_ = lean_unsigned_to_nat(0u);
v___x_2509_ = lean_nat_dec_eq(v___x_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_inc_ref(v_self_2506_);
return v_self_2506_;
}
else
{
lean_object* v___x_2510_; 
v___x_2510_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2510_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CachePlatform_toString___boxed(lean_object* v_self_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lake_CachePlatform_toString(v_self_2511_);
lean_dec_ref(v_self_2511_);
return v_res_2512_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheToolchain_isNone(lean_object* v_self_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2517_ = lean_string_utf8_byte_size(v_self_2516_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_nat_dec_eq(v___x_2517_, v___x_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_isNone___boxed(lean_object* v_self_2520_){
_start:
{
uint8_t v_res_2521_; lean_object* v_r_2522_; 
v_res_2521_ = l_Lake_CacheToolchain_isNone(v_self_2520_);
lean_dec_ref(v_self_2520_);
v_r_2522_ = lean_box(v_res_2521_);
return v_r_2522_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofString(lean_object* v_s_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lake_normalizeToolchain(v_s_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain(lean_object* v_s_2525_){
_start:
{
lean_inc_ref(v_s_2525_);
return v_s_2525_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_ofElanToolchain___boxed(lean_object* v_s_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lake_CacheToolchain_ofElanToolchain(v_s_2526_);
lean_dec_ref(v_s_2526_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_length(lean_object* v_self_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_string_utf8_byte_size(v_self_2528_);
lean_inc_ref(v_self_2528_);
v___x_2531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2531_, 0, v_self_2528_);
lean_ctor_set(v___x_2531_, 1, v___x_2529_);
lean_ctor_set(v___x_2531_, 2, v___x_2530_);
v___x_2532_ = l_String_Slice_positions(v___x_2531_);
v___x_2533_ = l_WellFounded_opaqueFix_u2083___at___00Lake_CachePlatform_length_spec__0___redArg(v___x_2531_, v_self_2528_, v___x_2532_, v___x_2529_);
lean_dec_ref(v_self_2528_);
lean_dec_ref(v___x_2531_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString(lean_object* v_self_2534_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_string_utf8_byte_size(v_self_2534_);
v___x_2536_ = lean_unsigned_to_nat(0u);
v___x_2537_ = lean_nat_dec_eq(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_inc_ref(v_self_2534_);
return v_self_2534_;
}
else
{
lean_object* v___x_2538_; 
v___x_2538_ = ((lean_object*)(l_Lake_CachePlatform_toString___closed__0));
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheToolchain_toString___boxed(lean_object* v_self_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lake_CacheToolchain_toString(v_self_2539_);
lean_dec_ref(v_self_2539_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore(uint64_t v_hash_2546_, lean_object* v_url_2547_, lean_object* v_path_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__0));
lean_inc_ref(v_path_2548_);
v___x_2552_ = l_Lake_download(v_url_2547_, v_path_2548_, v___x_2551_, v_a_2549_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2595_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; 
v_unused_2596_ = lean_ctor_get(v___x_2552_, 0);
lean_dec(v_unused_2596_);
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2595_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2595_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lake_computeBinFileHash(v_path_2548_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; uint64_t v___x_2559_; uint8_t v___x_2560_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = lean_unbox_uint64(v_a_2558_);
v___x_2560_ = lean_uint64_dec_eq(v___x_2559_, v_hash_2546_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; uint64_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2561_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__1));
lean_inc_ref(v_path_2548_);
v___x_2562_ = lean_string_append(v_path_2548_, v___x_2561_);
v___x_2563_ = lean_unbox_uint64(v_a_2558_);
lean_dec(v_a_2558_);
v___x_2564_ = l_Lake_lowerHexUInt64(v___x_2563_);
v___x_2565_ = lean_string_append(v___x_2562_, v___x_2564_);
lean_dec_ref(v___x_2564_);
v___x_2566_ = 3;
v___x_2567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set_uint8(v___x_2567_, sizeof(void*)*1, v___x_2566_);
lean_inc(v_a_2553_);
v___x_2568_ = lean_array_push(v_a_2553_, v___x_2567_);
v___x_2569_ = lean_io_remove_file(v_path_2548_);
lean_dec_ref(v_path_2548_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
lean_dec_ref(v___x_2569_);
v___x_2570_ = lean_array_get_size(v_a_2553_);
lean_dec(v_a_2553_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 1);
lean_ctor_set(v___x_2555_, 1, v___x_2568_);
lean_ctor_set(v___x_2555_, 0, v___x_2570_);
v___x_2572_ = v___x_2555_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v___x_2568_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
lean_dec(v_a_2553_);
v_a_2574_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2574_);
lean_dec_ref(v___x_2569_);
v___x_2575_ = lean_io_error_to_string(v_a_2574_);
v___x_2576_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*1, v___x_2566_);
v___x_2577_ = lean_array_get_size(v___x_2568_);
v___x_2578_ = lean_array_push(v___x_2568_, v___x_2576_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 1);
lean_ctor_set(v___x_2555_, 1, v___x_2578_);
lean_ctor_set(v___x_2555_, 0, v___x_2577_);
v___x_2580_ = v___x_2555_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
lean_dec(v_a_2558_);
lean_dec_ref(v_path_2548_);
v___x_2582_ = lean_box(0);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2582_);
v___x_2584_ = v___x_2555_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_a_2553_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_dec_ref(v_path_2548_);
v_a_2586_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2586_);
lean_dec_ref(v___x_2557_);
v___x_2587_ = lean_io_error_to_string(v_a_2586_);
v___x_2588_ = 3;
v___x_2589_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*1, v___x_2588_);
v___x_2590_ = lean_array_get_size(v_a_2553_);
v___x_2591_ = lean_array_push(v_a_2553_, v___x_2589_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 1);
lean_ctor_set(v___x_2555_, 1, v___x_2591_);
lean_ctor_set(v___x_2555_, 0, v___x_2590_);
v___x_2593_ = v___x_2555_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v___x_2591_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_dec_ref(v_path_2548_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_downloadArtifactCore___boxed(lean_object* v_hash_2597_, lean_object* v_url_2598_, lean_object* v_path_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
uint64_t v_hash_boxed_2602_; lean_object* v_res_2603_; 
v_hash_boxed_2602_ = lean_unbox_uint64(v_hash_2597_);
lean_dec_ref(v_hash_2597_);
v_res_2603_ = l_Lake_downloadArtifactCore(v_hash_boxed_2602_, v_url_2598_, v_path_2599_, v_a_2600_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(lean_object* v_x_2606_){
_start:
{
if (lean_obj_tag(v_x_2606_) == 0)
{
lean_object* v___x_2607_; 
v___x_2607_ = ((lean_object*)(l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0___closed__0));
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_Json_getNat_x3f(v_x_2606_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2625_; 
v_a_2617_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2619_ = v___x_2608_;
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2608_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_a_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2623_ = v___x_2619_;
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
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_2649_ = lean_unsigned_to_nat(14u);
v___x_2650_ = lean_mk_empty_array_with_capacity(v___x_2649_);
v___x_2651_ = lean_array_push(v___x_2650_, v___x_2648_);
return v___x_2651_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_2653_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__21);
v___x_2654_ = lean_array_push(v___x_2653_, v___x_2652_);
return v___x_2654_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_2656_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__22);
v___x_2657_ = lean_array_push(v___x_2656_, v___x_2655_);
return v___x_2657_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24(void){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_2659_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__23);
v___x_2660_ = lean_array_push(v___x_2659_, v___x_2658_);
return v___x_2660_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_2662_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__24);
v___x_2663_ = lean_array_push(v___x_2662_, v___x_2661_);
return v___x_2663_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_2665_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__25);
v___x_2666_ = lean_array_push(v___x_2665_, v___x_2664_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3(lean_object* v_file_2670_, lean_object* v_contentType_2671_, lean_object* v_url_2672_, lean_object* v_key_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v___y_2677_; lean_object* v_a_2678_; lean_object* v_stderr_2691_; lean_object* v___y_2700_; lean_object* v___y_2703_; lean_object* v_a_2704_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v_stderr_2743_; lean_object* v_a_2744_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2758_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_2759_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_2760_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_2761_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_2762_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_2763_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_2764_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_2765_ = lean_string_append(v___x_2764_, v_contentType_2671_);
v___x_2766_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_2767_ = lean_array_push(v___x_2766_, v_key_2673_);
v___x_2768_ = lean_array_push(v___x_2767_, v___x_2760_);
v___x_2769_ = lean_array_push(v___x_2768_, v___x_2761_);
v___x_2770_ = lean_array_push(v___x_2769_, v___x_2762_);
v___x_2771_ = lean_array_push(v___x_2770_, v_file_2670_);
v___x_2772_ = lean_array_push(v___x_2771_, v_url_2672_);
v___x_2773_ = lean_array_push(v___x_2772_, v___x_2763_);
v___x_2774_ = lean_array_push(v___x_2773_, v___x_2765_);
v___x_2775_ = lean_box(0);
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_2778_ = 1;
v___x_2779_ = 0;
v___x_2780_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2780_, 0, v___x_2758_);
lean_ctor_set(v___x_2780_, 1, v___x_2759_);
lean_ctor_set(v___x_2780_, 2, v___x_2774_);
lean_ctor_set(v___x_2780_, 3, v___x_2775_);
lean_ctor_set(v___x_2780_, 4, v___x_2777_);
lean_ctor_set_uint8(v___x_2780_, sizeof(void*)*5, v___x_2778_);
lean_ctor_set_uint8(v___x_2780_, sizeof(void*)*5 + 1, v___x_2779_);
v___x_2781_ = l_Lake_captureProc_x27(v___x_2780_, v___x_2777_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v_a_2783_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
v_a_2783_ = lean_ctor_get(v___x_2781_, 1);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2781_);
v___x_2797_ = lean_array_get_size(v_a_2783_);
v___x_2798_ = lean_nat_dec_lt(v___x_2776_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_dec(v_a_2783_);
goto v___jp_2784_;
}
else
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = lean_box(0);
v___x_2800_ = lean_nat_dec_le(v___x_2797_, v___x_2797_);
if (v___x_2800_ == 0)
{
if (v___x_2798_ == 0)
{
lean_dec(v_a_2783_);
goto v___jp_2784_;
}
else
{
size_t v___x_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = ((size_t)0ULL);
v___x_2802_ = lean_usize_of_nat(v___x_2797_);
v___x_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2783_, v___x_2801_, v___x_2802_, v___x_2799_, v_a_2674_);
lean_dec(v_a_2783_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_dec_ref(v___x_2803_);
goto v___jp_2784_;
}
else
{
lean_dec(v_a_2782_);
return v___x_2803_;
}
}
}
else
{
size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = lean_usize_of_nat(v___x_2797_);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2783_, v___x_2804_, v___x_2805_, v___x_2799_, v_a_2674_);
lean_dec(v_a_2783_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec_ref(v___x_2806_);
goto v___jp_2784_;
}
else
{
lean_dec(v_a_2782_);
return v___x_2806_;
}
}
}
v___jp_2784_:
{
lean_object* v_stderr_2785_; lean_object* v___x_2786_; 
v_stderr_2785_ = lean_ctor_get(v_a_2782_, 1);
lean_inc_ref(v_stderr_2785_);
v___x_2786_ = l_Lean_Json_parse(v_stderr_2785_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; 
lean_inc_ref(v_stderr_2785_);
lean_dec(v_a_2782_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v_stderr_2743_ = v_stderr_2785_;
v_a_2744_ = v_a_2787_;
goto v___jp_2742_;
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v___x_2786_);
v___x_2789_ = l_Lean_Json_getObj_x3f(v_a_2788_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; 
lean_inc_ref(v_stderr_2785_);
lean_dec(v_a_2782_);
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref(v___x_2789_);
v_stderr_2743_ = v_stderr_2785_;
v_a_2744_ = v_a_2790_;
goto v___jp_2742_;
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2791_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2791_);
lean_dec_ref(v___x_2789_);
v___x_2792_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_2793_ = l_Lake_JsonObject_getJson_x3f(v_a_2791_, v___x_2792_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_inc_ref(v_stderr_2785_);
lean_dec(v_a_2791_);
lean_dec(v_a_2782_);
v_stderr_2691_ = v_stderr_2785_;
goto v___jp_2690_;
}
else
{
lean_object* v_val_2794_; lean_object* v___x_2795_; 
v_val_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_val_2794_);
lean_dec_ref(v___x_2793_);
v___x_2795_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2794_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref(v___x_2795_);
v___y_2731_ = v_a_2782_;
v___y_2732_ = v_a_2791_;
goto v___jp_2730_;
}
else
{
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref(v___x_2795_);
v___y_2731_ = v_a_2782_;
v___y_2732_ = v_a_2791_;
goto v___jp_2730_;
}
else
{
lean_object* v_a_2796_; 
lean_dec(v_a_2791_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref(v___x_2795_);
v___y_2703_ = v_a_2782_;
v_a_2704_ = v_a_2796_;
goto v___jp_2702_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v_a_2807_ = lean_ctor_get(v___x_2781_, 1);
lean_inc(v_a_2807_);
lean_dec_ref(v___x_2781_);
v___x_2808_ = lean_array_get_size(v_a_2807_);
v___x_2809_ = lean_nat_dec_lt(v___x_2776_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
lean_dec(v_a_2807_);
v___x_2810_ = lean_box(0);
v___x_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = lean_box(0);
v___x_2813_ = lean_nat_dec_le(v___x_2808_, v___x_2808_);
if (v___x_2813_ == 0)
{
if (v___x_2809_ == 0)
{
lean_dec(v_a_2807_);
goto v___jp_2755_;
}
else
{
size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = ((size_t)0ULL);
v___x_2815_ = lean_usize_of_nat(v___x_2808_);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2807_, v___x_2814_, v___x_2815_, v___x_2812_, v_a_2674_);
lean_dec(v_a_2807_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_dec_ref(v___x_2816_);
goto v___jp_2755_;
}
else
{
return v___x_2816_;
}
}
}
else
{
size_t v___x_2817_; size_t v___x_2818_; lean_object* v___x_2819_; 
v___x_2817_ = ((size_t)0ULL);
v___x_2818_ = lean_usize_of_nat(v___x_2808_);
v___x_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_2807_, v___x_2817_, v___x_2818_, v___x_2812_, v_a_2674_);
lean_dec(v_a_2807_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_dec_ref(v___x_2819_);
goto v___jp_2755_;
}
else
{
return v___x_2819_;
}
}
}
}
v___jp_2676_:
{
lean_object* v_stderr_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v_stderr_2679_ = lean_ctor_get(v___y_2677_, 1);
lean_inc_ref(v_stderr_2679_);
lean_dec_ref(v___y_2677_);
v___x_2680_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_2681_ = lean_string_append(v___x_2680_, v_a_2678_);
lean_dec_ref(v_a_2678_);
v___x_2682_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_2683_ = lean_string_append(v___x_2681_, v___x_2682_);
v___x_2684_ = lean_string_append(v___x_2683_, v_stderr_2679_);
lean_dec_ref(v_stderr_2679_);
v___x_2685_ = 3;
v___x_2686_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set_uint8(v___x_2686_, sizeof(void*)*1, v___x_2685_);
lean_inc_ref(v_a_2674_);
v___x_2687_ = lean_apply_2(v_a_2674_, v___x_2686_, lean_box(0));
v___x_2688_ = lean_box(0);
v___x_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
v___jp_2690_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2692_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_2693_ = lean_string_append(v___x_2692_, v_stderr_2691_);
lean_dec_ref(v_stderr_2691_);
v___x_2694_ = 3;
v___x_2695_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set_uint8(v___x_2695_, sizeof(void*)*1, v___x_2694_);
lean_inc_ref(v_a_2674_);
v___x_2696_ = lean_apply_2(v_a_2674_, v___x_2695_, lean_box(0));
v___x_2697_ = lean_box(0);
v___x_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
v___jp_2699_:
{
lean_object* v_stderr_2701_; 
v_stderr_2701_ = lean_ctor_get(v___y_2700_, 1);
lean_inc_ref(v_stderr_2701_);
lean_dec_ref(v___y_2700_);
v_stderr_2691_ = v_stderr_2701_;
goto v___jp_2690_;
}
v___jp_2702_:
{
if (lean_obj_tag(v_a_2704_) == 0)
{
v___y_2700_ = v___y_2703_;
goto v___jp_2699_;
}
else
{
lean_object* v_val_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2729_; 
v_val_2705_ = lean_ctor_get(v_a_2704_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_a_2704_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2707_ = v_a_2704_;
v_isShared_2708_ = v_isSharedCheck_2729_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_val_2705_);
lean_dec(v_a_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2729_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = lean_unsigned_to_nat(200u);
v___x_2710_ = lean_nat_dec_eq(v_val_2705_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v_stdout_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v_stdout_2711_ = lean_ctor_get(v___y_2703_, 0);
lean_inc_ref(v_stdout_2711_);
lean_dec_ref(v___y_2703_);
v___x_2712_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_2713_ = l_Nat_reprFast(v_val_2705_);
v___x_2714_ = lean_string_append(v___x_2712_, v___x_2713_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2716_ = lean_string_append(v___x_2714_, v___x_2715_);
v___x_2717_ = lean_string_append(v___x_2716_, v_stdout_2711_);
lean_dec_ref(v_stdout_2711_);
v___x_2718_ = 3;
v___x_2719_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*1, v___x_2718_);
lean_inc_ref(v_a_2674_);
v___x_2720_ = lean_apply_2(v_a_2674_, v___x_2719_, lean_box(0));
v___x_2721_ = lean_box(0);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2721_);
v___x_2723_ = v___x_2707_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_dec(v_val_2705_);
lean_dec_ref(v___y_2703_);
v___x_2725_ = lean_box(0);
if (v_isShared_2708_ == 0)
{
lean_ctor_set_tag(v___x_2707_, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2725_);
v___x_2727_ = v___x_2707_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
v___jp_2730_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_2734_ = l_Lake_JsonObject_getJson_x3f(v___y_2732_, v___x_2733_);
lean_dec(v___y_2732_);
if (lean_obj_tag(v___x_2734_) == 0)
{
v___y_2700_ = v___y_2731_;
goto v___jp_2699_;
}
else
{
lean_object* v_val_2735_; lean_object* v___x_2736_; 
v_val_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_val_2735_);
lean_dec_ref(v___x_2734_);
v___x_2736_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref(v___x_2736_);
v___x_2738_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_2739_ = lean_string_append(v___x_2738_, v_a_2737_);
lean_dec(v_a_2737_);
v___y_2677_ = v___y_2731_;
v_a_2678_ = v___x_2739_;
goto v___jp_2676_;
}
else
{
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2740_; 
v_a_2740_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2740_);
lean_dec_ref(v___x_2736_);
v___y_2677_ = v___y_2731_;
v_a_2678_ = v_a_2740_;
goto v___jp_2676_;
}
else
{
lean_object* v_a_2741_; 
v_a_2741_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2736_);
v___y_2703_ = v___y_2731_;
v_a_2704_ = v_a_2741_;
goto v___jp_2702_;
}
}
}
}
v___jp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2745_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_2746_ = lean_string_append(v___x_2745_, v_a_2744_);
lean_dec_ref(v_a_2744_);
v___x_2747_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_2748_ = lean_string_append(v___x_2746_, v___x_2747_);
v___x_2749_ = lean_string_append(v___x_2748_, v_stderr_2743_);
lean_dec_ref(v_stderr_2743_);
v___x_2750_ = 3;
v___x_2751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*1, v___x_2750_);
lean_inc_ref(v_a_2674_);
v___x_2752_ = lean_apply_2(v_a_2674_, v___x_2751_, lean_box(0));
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
return v___x_2754_;
}
v___jp_2755_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = lean_box(0);
v___x_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
return v___x_2757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___boxed(lean_object* v_file_2820_, lean_object* v_contentType_2821_, lean_object* v_url_2822_, lean_object* v_key_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l___private_Lake_Config_Cache_0__Lake_uploadS3(v_file_2820_, v_contentType_2821_, v_url_2822_, v_key_2823_, v_a_2824_);
lean_dec_ref(v_a_2824_);
lean_dec_ref(v_contentType_2821_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f(lean_object* v_service_2827_){
_start:
{
lean_object* v_name_x3f_2828_; 
v_name_x3f_2828_ = lean_ctor_get(v_service_2827_, 0);
lean_inc(v_name_x3f_2828_);
return v_name_x3f_2828_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_name_x3f___boxed(lean_object* v_service_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lake_CacheService_name_x3f(v_service_2829_);
lean_dec_ref(v_service_2829_);
return v_res_2830_;
}
}
LEAN_EXPORT uint8_t l_Lake_CacheService_isReservoir(lean_object* v_service_2831_){
_start:
{
uint8_t v_isReservoir_2832_; 
v_isReservoir_2832_ = lean_ctor_get_uint8(v_service_2831_, sizeof(void*)*5);
return v_isReservoir_2832_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_isReservoir___boxed(lean_object* v_service_2833_){
_start:
{
uint8_t v_res_2834_; lean_object* v_r_2835_; 
v_res_2834_ = l_Lake_CacheService_isReservoir(v_service_2833_);
lean_dec_ref(v_service_2833_);
v_r_2835_ = lean_box(v_res_2834_);
return v_r_2835_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_reservoirService(lean_object* v_apiEndpoint_2836_, lean_object* v_name_x3f_2837_){
_start:
{
lean_object* v___x_2838_; uint8_t v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2839_ = 1;
v___x_2840_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2840_, 0, v_name_x3f_2837_);
lean_ctor_set(v___x_2840_, 1, v___x_2838_);
lean_ctor_set(v___x_2840_, 2, v___x_2838_);
lean_ctor_set(v___x_2840_, 3, v___x_2838_);
lean_ctor_set(v___x_2840_, 4, v_apiEndpoint_2836_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*5, v___x_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadService(lean_object* v_key_2841_, lean_object* v_artifactEndpoint_2842_, lean_object* v_revisionEndpoint_2843_){
_start:
{
lean_object* v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2844_ = lean_box(0);
v___x_2845_ = 0;
v___x_2846_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2847_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2847_, 0, v___x_2844_);
lean_ctor_set(v___x_2847_, 1, v_key_2841_);
lean_ctor_set(v___x_2847_, 2, v_artifactEndpoint_2842_);
lean_ctor_set(v___x_2847_, 3, v_revisionEndpoint_2843_);
lean_ctor_set(v___x_2847_, 4, v___x_2846_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*5, v___x_2845_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadService(lean_object* v_artifactEndpoint_2848_, lean_object* v_revisionEndpoint_2849_, lean_object* v_name_x3f_2850_){
_start:
{
lean_object* v___x_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2852_ = 0;
v___x_2853_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2853_, 0, v_name_x3f_2850_);
lean_ctor_set(v___x_2853_, 1, v___x_2851_);
lean_ctor_set(v___x_2853_, 2, v_artifactEndpoint_2848_);
lean_ctor_set(v___x_2853_, 3, v_revisionEndpoint_2849_);
lean_ctor_set(v___x_2853_, 4, v___x_2851_);
lean_ctor_set_uint8(v___x_2853_, sizeof(void*)*5, v___x_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtsService(lean_object* v_artifactEndpoint_2854_, lean_object* v_name_x3f_2855_){
_start:
{
lean_object* v___x_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_2857_ = 0;
v___x_2858_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2858_, 0, v_name_x3f_2855_);
lean_ctor_set(v___x_2858_, 1, v___x_2856_);
lean_ctor_set(v___x_2858_, 2, v_artifactEndpoint_2854_);
lean_ctor_set(v___x_2858_, 3, v___x_2856_);
lean_ctor_set(v___x_2858_, 4, v___x_2856_);
lean_ctor_set_uint8(v___x_2858_, sizeof(void*)*5, v___x_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_withKey(lean_object* v_service_2859_, lean_object* v_key_2860_){
_start:
{
lean_object* v_name_x3f_2861_; lean_object* v_artifactEndpoint_2862_; lean_object* v_revisionEndpoint_2863_; uint8_t v_isReservoir_2864_; lean_object* v_apiEndpoint_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_name_x3f_2861_ = lean_ctor_get(v_service_2859_, 0);
v_artifactEndpoint_2862_ = lean_ctor_get(v_service_2859_, 2);
v_revisionEndpoint_2863_ = lean_ctor_get(v_service_2859_, 3);
v_isReservoir_2864_ = lean_ctor_get_uint8(v_service_2859_, sizeof(void*)*5);
v_apiEndpoint_2865_ = lean_ctor_get(v_service_2859_, 4);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_service_2859_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v_service_2859_, 1);
lean_dec(v_unused_2873_);
v___x_2867_ = v_service_2859_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_apiEndpoint_2865_);
lean_inc(v_revisionEndpoint_2863_);
lean_inc(v_artifactEndpoint_2862_);
lean_inc(v_name_x3f_2861_);
lean_dec(v_service_2859_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v_key_2860_);
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_name_x3f_2861_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_key_2860_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_artifactEndpoint_2862_);
lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_revisionEndpoint_2863_);
lean_ctor_set(v_reuseFailAlloc_2871_, 4, v_apiEndpoint_2865_);
lean_ctor_set_uint8(v_reuseFailAlloc_2871_, sizeof(void*)*5, v_isReservoir_2864_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(lean_object* v_s_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___closed__0));
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0___boxed(lean_object* v_s_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v_s_2880_);
lean_dec_ref(v_s_2880_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(lean_object* v_scope_2882_, lean_object* v___x_2883_, lean_object* v___x_2884_, lean_object* v_a_2885_, lean_object* v_b_2886_){
_start:
{
if (lean_obj_tag(v_a_2885_) == 0)
{
lean_object* v_currPos_2887_; lean_object* v_searcher_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2922_; 
v_currPos_2887_ = lean_ctor_get(v_a_2885_, 0);
v_searcher_2888_ = lean_ctor_get(v_a_2885_, 1);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_a_2885_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2890_ = v_a_2885_;
v_isShared_2891_ = v_isSharedCheck_2922_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_searcher_2888_);
lean_inc(v_currPos_2887_);
lean_dec(v_a_2885_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2922_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v_startInclusive_2892_; lean_object* v_endExclusive_2893_; uint32_t v___x_2894_; lean_object* v_it_2896_; lean_object* v_startInclusive_2897_; lean_object* v_endExclusive_2898_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v_startInclusive_2892_ = lean_ctor_get(v___x_2883_, 1);
v_endExclusive_2893_ = lean_ctor_get(v___x_2883_, 2);
v___x_2894_ = 47;
v___x_2903_ = lean_nat_sub(v_endExclusive_2893_, v_startInclusive_2892_);
v___x_2904_ = lean_nat_dec_eq(v_searcher_2888_, v___x_2903_);
lean_dec(v___x_2903_);
if (v___x_2904_ == 0)
{
uint32_t v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = lean_string_utf8_get_fast(v_scope_2882_, v_searcher_2888_);
v___x_2906_ = lean_uint32_dec_eq(v___x_2905_, v___x_2894_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = lean_string_utf8_next_fast(v_scope_2882_, v_searcher_2888_);
lean_dec(v_searcher_2888_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 1, v___x_2907_);
v___x_2909_ = v___x_2890_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_currPos_2887_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
v_a_2885_ = v___x_2909_;
goto _start;
}
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v_slice_2915_; lean_object* v_nextIt_2917_; 
v___x_2912_ = lean_string_utf8_next_fast(v_scope_2882_, v_searcher_2888_);
v___x_2913_ = lean_nat_sub(v___x_2912_, v_searcher_2888_);
v___x_2914_ = lean_nat_add(v_searcher_2888_, v___x_2913_);
lean_dec(v___x_2913_);
v_slice_2915_ = l_String_Slice_subslice_x21(v___x_2883_, v_currPos_2887_, v_searcher_2888_);
lean_inc(v___x_2914_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 1, v___x_2914_);
lean_ctor_set(v___x_2890_, 0, v___x_2914_);
v_nextIt_2917_ = v___x_2890_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2914_);
v_nextIt_2917_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v_startInclusive_2918_; lean_object* v_endExclusive_2919_; 
v_startInclusive_2918_ = lean_ctor_get(v_slice_2915_, 0);
lean_inc(v_startInclusive_2918_);
v_endExclusive_2919_ = lean_ctor_get(v_slice_2915_, 1);
lean_inc(v_endExclusive_2919_);
lean_dec_ref(v_slice_2915_);
v_it_2896_ = v_nextIt_2917_;
v_startInclusive_2897_ = v_startInclusive_2918_;
v_endExclusive_2898_ = v_endExclusive_2919_;
goto v___jp_2895_;
}
}
}
else
{
lean_object* v___x_2921_; 
lean_del_object(v___x_2890_);
lean_dec(v_searcher_2888_);
v___x_2921_ = lean_box(1);
lean_inc(v___x_2884_);
v_it_2896_ = v___x_2921_;
v_startInclusive_2897_ = v_currPos_2887_;
v_endExclusive_2898_ = v___x_2884_;
goto v___jp_2895_;
}
v___jp_2895_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = lean_string_utf8_extract(v_scope_2882_, v_startInclusive_2897_, v_endExclusive_2898_);
lean_dec(v_endExclusive_2898_);
lean_dec(v_startInclusive_2897_);
v___x_2900_ = lean_string_push(v_b_2886_, v___x_2894_);
v___x_2901_ = l_Lake_uriEncode(v___x_2899_, v___x_2900_);
v_a_2885_ = v_it_2896_;
v_b_2886_ = v___x_2901_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2884_);
return v_b_2886_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg___boxed(lean_object* v_scope_2923_, lean_object* v___x_2924_, lean_object* v___x_2925_, lean_object* v_a_2926_, lean_object* v_b_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2923_, v___x_2924_, v___x_2925_, v_a_2926_, v_b_2927_);
lean_dec_ref(v___x_2924_);
lean_dec_ref(v_scope_2923_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(lean_object* v_endpoint_2929_, lean_object* v_scope_2930_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2931_ = lean_unsigned_to_nat(0u);
v___x_2932_ = lean_string_utf8_byte_size(v_scope_2930_);
lean_inc_ref(v_scope_2930_);
v___x_2933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2933_, 0, v_scope_2930_);
lean_ctor_set(v___x_2933_, 1, v___x_2931_);
lean_ctor_set(v___x_2933_, 2, v___x_2932_);
v___x_2934_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__0(v___x_2933_);
v___x_2935_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2930_, v___x_2933_, v___x_2932_, v___x_2934_, v_endpoint_2929_);
lean_dec_ref(v___x_2933_);
lean_dec_ref(v_scope_2930_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(lean_object* v_scope_2936_, lean_object* v___x_2937_, lean_object* v___x_2938_, lean_object* v_inst_2939_, lean_object* v_R_2940_, lean_object* v_a_2941_, lean_object* v_b_2942_, lean_object* v_c_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___redArg(v_scope_2936_, v___x_2937_, v___x_2938_, v_a_2941_, v_b_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1___boxed(lean_object* v_scope_2945_, lean_object* v___x_2946_, lean_object* v___x_2947_, lean_object* v_inst_2948_, lean_object* v_R_2949_, lean_object* v_a_2950_, lean_object* v_b_2951_, lean_object* v_c_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Config_Cache_0__Lake_CacheService_appendScope_spec__1(v_scope_2945_, v___x_2946_, v___x_2947_, v_inst_2948_, v_R_2949_, v_a_2950_, v_b_2951_, v_c_2952_);
lean_dec_ref(v___x_2946_);
lean_dec_ref(v_scope_2945_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(lean_object* v_service_2954_, lean_object* v_scope_2955_){
_start:
{
lean_object* v_artifactEndpoint_2956_; lean_object* v___x_2957_; 
v_artifactEndpoint_2956_ = lean_ctor_get(v_service_2954_, 2);
lean_inc_ref(v_artifactEndpoint_2956_);
lean_dec_ref(v_service_2954_);
v___x_2957_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_artifactEndpoint_2956_, v_scope_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(uint64_t v_contentHash_2960_, lean_object* v_service_2961_, lean_object* v_scope_2962_){
_start:
{
lean_object* v___y_2964_; lean_object* v_s_2971_; lean_object* v___x_2972_; 
v_s_2971_ = lean_ctor_get(v_scope_2962_, 0);
lean_inc_ref(v_s_2971_);
lean_dec_ref(v_scope_2962_);
v___x_2972_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___lam__0(v_service_2961_, v_s_2971_);
v___y_2964_ = v___x_2972_;
goto v___jp_2963_;
v___jp_2963_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2965_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_2966_ = lean_string_append(v___y_2964_, v___x_2965_);
v___x_2967_ = l_Lake_lowerHexUInt64(v_contentHash_2960_);
v___x_2968_ = lean_string_append(v___x_2966_, v___x_2967_);
lean_dec_ref(v___x_2967_);
v___x_2969_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2970_ = lean_string_append(v___x_2968_, v___x_2969_);
return v___x_2970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___boxed(lean_object* v_contentHash_2973_, lean_object* v_service_2974_, lean_object* v_scope_2975_){
_start:
{
uint64_t v_contentHash_boxed_2976_; lean_object* v_res_2977_; 
v_contentHash_boxed_2976_ = lean_unbox_uint64(v_contentHash_2973_);
lean_dec_ref(v_contentHash_2973_);
v_res_2977_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_boxed_2976_, v_service_2974_, v_scope_2975_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl(uint64_t v_contentHash_2981_, lean_object* v_service_2982_, lean_object* v_scope_2983_){
_start:
{
lean_object* v___y_2985_; uint8_t v_isReservoir_2992_; 
v_isReservoir_2992_ = lean_ctor_get_uint8(v_service_2982_, sizeof(void*)*5);
if (v_isReservoir_2992_ == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_2981_, v_service_2982_, v_scope_2983_);
return v___x_2993_;
}
else
{
if (lean_obj_tag(v_scope_2983_) == 0)
{
lean_object* v_apiEndpoint_2994_; lean_object* v_s_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_apiEndpoint_2994_ = lean_ctor_get(v_service_2982_, 4);
lean_inc_ref(v_apiEndpoint_2994_);
lean_dec_ref(v_service_2982_);
v_s_2995_ = lean_ctor_get(v_scope_2983_, 0);
lean_inc_ref(v_s_2995_);
lean_dec_ref(v_scope_2983_);
v___x_2996_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_2997_ = lean_string_append(v_apiEndpoint_2994_, v___x_2996_);
v___x_2998_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_2997_, v_s_2995_);
v___y_2985_ = v___x_2998_;
goto v___jp_2984_;
}
else
{
lean_object* v_apiEndpoint_2999_; lean_object* v_s_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_apiEndpoint_2999_ = lean_ctor_get(v_service_2982_, 4);
lean_inc_ref(v_apiEndpoint_2999_);
lean_dec_ref(v_service_2982_);
v_s_3000_ = lean_ctor_get(v_scope_2983_, 0);
lean_inc_ref(v_s_3000_);
lean_dec_ref(v_scope_2983_);
v___x_3001_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_3002_ = lean_string_append(v_apiEndpoint_2999_, v___x_3001_);
v___x_3003_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_3002_, v_s_3000_);
v___y_2985_ = v___x_3003_;
goto v___jp_2984_;
}
}
v___jp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2986_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__0));
v___x_2987_ = lean_string_append(v___y_2985_, v___x_2986_);
v___x_2988_ = l_Lake_lowerHexUInt64(v_contentHash_2981_);
v___x_2989_ = lean_string_append(v___x_2987_, v___x_2988_);
lean_dec_ref(v___x_2988_);
v___x_2990_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__1));
v___x_2991_ = lean_string_append(v___x_2989_, v___x_2990_);
return v___x_2991_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_artifactUrl___boxed(lean_object* v_contentHash_3004_, lean_object* v_service_3005_, lean_object* v_scope_3006_){
_start:
{
uint64_t v_contentHash_boxed_3007_; lean_object* v_res_3008_; 
v_contentHash_boxed_3007_ = lean_unbox_uint64(v_contentHash_3004_);
lean_dec_ref(v_contentHash_3004_);
v_res_3008_ = l_Lake_CacheService_artifactUrl(v_contentHash_boxed_3007_, v_service_3005_, v_scope_3006_);
return v_res_3008_;
}
}
static lean_object* _init_l_Lake_CacheService_downloadArtifact___closed__3(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3013_ = lean_array_get_size(v___x_3012_);
return v___x_3013_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__4(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v___x_3014_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = lean_nat_dec_lt(v___x_3015_, v___x_3014_);
return v___x_3016_;
}
}
static uint8_t _init_l_Lake_CacheService_downloadArtifact___closed__5(void){
_start:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3017_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3018_ = lean_nat_dec_le(v___x_3017_, v___x_3017_);
return v___x_3018_;
}
}
static size_t _init_l_Lake_CacheService_downloadArtifact___closed__6(void){
_start:
{
lean_object* v___x_3019_; size_t v___x_3020_; 
v___x_3019_ = lean_obj_once(&l_Lake_CacheService_downloadArtifact___closed__3, &l_Lake_CacheService_downloadArtifact___closed__3_once, _init_l_Lake_CacheService_downloadArtifact___closed__3);
v___x_3020_ = lean_usize_of_nat(v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact(lean_object* v_descr_3021_, lean_object* v_cache_3022_, lean_object* v_service_3023_, lean_object* v_scope_3024_, uint8_t v_force_3025_, lean_object* v_a_3026_){
_start:
{
uint64_t v_hash_3031_; lean_object* v_ext_3032_; lean_object* v_url_3033_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3097_; lean_object* v___y_3100_; uint8_t v_a_3101_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___y_3107_; lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v_hash_3031_ = lean_ctor_get_uint64(v_descr_3021_, sizeof(void*)*1);
v_ext_3032_ = lean_ctor_get(v_descr_3021_, 0);
lean_inc_ref(v_scope_3024_);
v_url_3033_ = l_Lake_CacheService_artifactUrl(v_hash_3031_, v_service_3023_, v_scope_3024_);
v___x_3104_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_3105_ = l_System_FilePath_join(v_cache_3022_, v___x_3104_);
v___x_3120_ = lean_string_utf8_byte_size(v_ext_3032_);
v___x_3121_ = lean_unsigned_to_nat(0u);
v___x_3122_ = lean_nat_dec_eq(v___x_3120_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3123_ = l_Lake_lowerHexUInt64(v_hash_3031_);
v___x_3124_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_3125_ = lean_string_append(v___x_3123_, v___x_3124_);
v___x_3126_ = lean_string_append(v___x_3125_, v_ext_3032_);
v___y_3107_ = v___x_3126_;
goto v___jp_3106_;
}
else
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lake_lowerHexUInt64(v_hash_3031_);
v___y_3107_ = v___x_3127_;
goto v___jp_3106_;
}
v___jp_3028_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_box(0);
v___x_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
return v___x_3030_;
}
v___jp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3037_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__0));
v___x_3038_ = lean_string_append(v___y_3036_, v___x_3037_);
v___x_3039_ = l_Lake_lowerHexUInt64(v_hash_3031_);
v___x_3040_ = lean_string_append(v___x_3038_, v___x_3039_);
lean_dec_ref(v___x_3039_);
v___x_3041_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3042_ = lean_string_append(v___x_3040_, v___x_3041_);
v___x_3043_ = lean_string_append(v___x_3042_, v___y_3035_);
v___x_3044_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3045_ = lean_string_append(v___x_3043_, v___x_3044_);
v___x_3046_ = lean_string_append(v___x_3045_, v_url_3033_);
v___x_3047_ = 1;
v___x_3048_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set_uint8(v___x_3048_, sizeof(void*)*1, v___x_3047_);
lean_inc_ref(v_a_3026_);
v___x_3049_ = lean_apply_2(v_a_3026_, v___x_3048_, lean_box(0));
v___x_3050_ = lean_unsigned_to_nat(0u);
v___x_3051_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3052_ = l_Lake_downloadArtifactCore(v_hash_3031_, v_url_3033_, v___y_3035_, v___x_3051_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v_a_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
v_a_3054_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_a_3054_);
lean_dec_ref(v___x_3052_);
v___x_3055_ = lean_array_get_size(v_a_3054_);
v___x_3056_ = lean_nat_dec_lt(v___x_3050_, v___x_3055_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
lean_dec(v_a_3054_);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_a_3053_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = lean_box(0);
v___x_3059_ = lean_nat_dec_le(v___x_3055_, v___x_3055_);
if (v___x_3059_ == 0)
{
if (v___x_3056_ == 0)
{
lean_object* v___x_3060_; 
lean_dec(v_a_3054_);
v___x_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3060_, 0, v_a_3053_);
return v___x_3060_;
}
else
{
size_t v___x_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((size_t)0ULL);
v___x_3062_ = lean_usize_of_nat(v___x_3055_);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3054_, v___x_3061_, v___x_3062_, v___x_3058_, v_a_3026_);
lean_dec(v_a_3054_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v___x_3063_, 0);
lean_dec(v_unused_3071_);
v___x_3065_ = v___x_3063_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v___x_3063_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v_a_3053_);
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3053_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
else
{
lean_dec(v_a_3053_);
return v___x_3063_;
}
}
}
else
{
size_t v___x_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = ((size_t)0ULL);
v___x_3073_ = lean_usize_of_nat(v___x_3055_);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3054_, v___x_3072_, v___x_3073_, v___x_3058_, v_a_3026_);
lean_dec(v_a_3054_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v___x_3074_, 0);
lean_dec(v_unused_3082_);
v___x_3076_ = v___x_3074_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_dec(v___x_3074_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 0, v_a_3053_);
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3053_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
else
{
lean_dec(v_a_3053_);
return v___x_3074_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v_a_3083_ = lean_ctor_get(v___x_3052_, 1);
lean_inc(v_a_3083_);
lean_dec_ref(v___x_3052_);
v___x_3084_ = lean_array_get_size(v_a_3083_);
v___x_3085_ = lean_nat_dec_lt(v___x_3050_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec(v_a_3083_);
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3088_ = lean_box(0);
v___x_3089_ = lean_nat_dec_le(v___x_3084_, v___x_3084_);
if (v___x_3089_ == 0)
{
if (v___x_3085_ == 0)
{
lean_dec(v_a_3083_);
goto v___jp_3028_;
}
else
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = lean_usize_of_nat(v___x_3084_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3083_, v___x_3090_, v___x_3091_, v___x_3088_, v_a_3026_);
lean_dec(v_a_3083_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_dec_ref(v___x_3092_);
goto v___jp_3028_;
}
else
{
return v___x_3092_;
}
}
}
else
{
size_t v___x_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = ((size_t)0ULL);
v___x_3094_ = lean_usize_of_nat(v___x_3084_);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3083_, v___x_3093_, v___x_3094_, v___x_3088_, v_a_3026_);
lean_dec(v_a_3083_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_dec_ref(v___x_3095_);
goto v___jp_3028_;
}
else
{
return v___x_3095_;
}
}
}
}
}
v___jp_3096_:
{
lean_object* v_s_3098_; 
v_s_3098_ = lean_ctor_get(v_scope_3024_, 0);
lean_inc_ref(v_s_3098_);
lean_dec_ref(v_scope_3024_);
v___y_3035_ = v___y_3097_;
v___y_3036_ = v_s_3098_;
goto v___jp_3034_;
}
v___jp_3099_:
{
if (v_a_3101_ == 0)
{
v___y_3097_ = v___y_3100_;
goto v___jp_3096_;
}
else
{
if (v_force_3025_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec_ref(v___y_3100_);
lean_dec_ref(v_url_3033_);
lean_dec_ref(v_scope_3024_);
v___x_3102_ = lean_box(0);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
else
{
v___y_3097_ = v___y_3100_;
goto v___jp_3096_;
}
}
}
v___jp_3106_:
{
lean_object* v_path_3108_; uint8_t v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_path_3108_ = l_System_FilePath_join(v___x_3105_, v___y_3107_);
v___x_3109_ = l_System_FilePath_pathExists(v_path_3108_);
v___x_3110_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3111_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_3111_ == 0)
{
v___y_3100_ = v_path_3108_;
v_a_3101_ = v___x_3109_;
goto v___jp_3099_;
}
else
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_3113_ == 0)
{
if (v___x_3111_ == 0)
{
v___y_3100_ = v_path_3108_;
v_a_3101_ = v___x_3109_;
goto v___jp_3099_;
}
else
{
size_t v___x_3114_; size_t v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = ((size_t)0ULL);
v___x_3115_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_3116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3110_, v___x_3114_, v___x_3115_, v___x_3112_, v_a_3026_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_dec_ref(v___x_3116_);
v___y_3100_ = v_path_3108_;
v_a_3101_ = v___x_3109_;
goto v___jp_3099_;
}
else
{
lean_dec_ref(v_path_3108_);
lean_dec_ref(v_url_3033_);
lean_dec_ref(v_scope_3024_);
return v___x_3116_;
}
}
}
else
{
size_t v___x_3117_; size_t v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = ((size_t)0ULL);
v___x_3118_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_3119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_3110_, v___x_3117_, v___x_3118_, v___x_3112_, v_a_3026_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_dec_ref(v___x_3119_);
v___y_3100_ = v_path_3108_;
v_a_3101_ = v___x_3109_;
goto v___jp_3099_;
}
else
{
lean_dec_ref(v_path_3108_);
lean_dec_ref(v_url_3033_);
lean_dec_ref(v_scope_3024_);
return v___x_3119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifact___boxed(lean_object* v_descr_3128_, lean_object* v_cache_3129_, lean_object* v_service_3130_, lean_object* v_scope_3131_, lean_object* v_force_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
uint8_t v_force_boxed_3135_; lean_object* v_res_3136_; 
v_force_boxed_3135_ = lean_unbox(v_force_3132_);
v_res_3136_ = l_Lake_CacheService_downloadArtifact(v_descr_3128_, v_cache_3129_, v_service_3130_, v_scope_3131_, v_force_boxed_3135_, v_a_3133_);
lean_dec_ref(v_a_3133_);
lean_dec_ref(v_descr_3128_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(lean_object* v_a_3137_, lean_object* v_file_3138_, lean_object* v_contentType_3139_, lean_object* v_url_3140_, lean_object* v_key_3141_){
_start:
{
lean_object* v___y_3144_; lean_object* v_a_3145_; lean_object* v_stderr_3158_; lean_object* v___y_3167_; lean_object* v___y_3170_; lean_object* v_a_3171_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v_stderr_3210_; lean_object* v_a_3211_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; uint8_t v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3225_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__8));
v___x_3226_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_3227_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_3228_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_3229_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__18));
v___x_3230_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_3231_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__20));
v___x_3232_ = lean_string_append(v___x_3231_, v_contentType_3139_);
v___x_3233_ = lean_unsigned_to_nat(14u);
v___x_3234_ = lean_mk_empty_array_with_capacity(v___x_3233_);
lean_dec_ref(v___x_3234_);
v___x_3235_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26, &l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__26);
v___x_3236_ = lean_array_push(v___x_3235_, v_key_3141_);
v___x_3237_ = lean_array_push(v___x_3236_, v___x_3227_);
v___x_3238_ = lean_array_push(v___x_3237_, v___x_3228_);
v___x_3239_ = lean_array_push(v___x_3238_, v___x_3229_);
v___x_3240_ = lean_array_push(v___x_3239_, v_file_3138_);
v___x_3241_ = lean_array_push(v___x_3240_, v_url_3140_);
v___x_3242_ = lean_array_push(v___x_3241_, v___x_3230_);
v___x_3243_ = lean_array_push(v___x_3242_, v___x_3232_);
v___x_3244_ = lean_box(0);
v___x_3245_ = lean_unsigned_to_nat(0u);
v___x_3246_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_3247_ = 1;
v___x_3248_ = 0;
v___x_3249_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3249_, 0, v___x_3225_);
lean_ctor_set(v___x_3249_, 1, v___x_3226_);
lean_ctor_set(v___x_3249_, 2, v___x_3243_);
lean_ctor_set(v___x_3249_, 3, v___x_3244_);
lean_ctor_set(v___x_3249_, 4, v___x_3246_);
lean_ctor_set_uint8(v___x_3249_, sizeof(void*)*5, v___x_3247_);
lean_ctor_set_uint8(v___x_3249_, sizeof(void*)*5 + 1, v___x_3248_);
v___x_3250_ = l_Lake_captureProc_x27(v___x_3249_, v___x_3246_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v_a_3252_; lean_object* v___x_3266_; uint8_t v___x_3267_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
v_a_3252_ = lean_ctor_get(v___x_3250_, 1);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3250_);
v___x_3266_ = lean_array_get_size(v_a_3252_);
v___x_3267_ = lean_nat_dec_lt(v___x_3245_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_dec(v_a_3252_);
goto v___jp_3253_;
}
else
{
lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_nat_dec_le(v___x_3266_, v___x_3266_);
if (v___x_3269_ == 0)
{
if (v___x_3267_ == 0)
{
lean_dec(v_a_3252_);
goto v___jp_3253_;
}
else
{
size_t v___x_3270_; size_t v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = ((size_t)0ULL);
v___x_3271_ = lean_usize_of_nat(v___x_3266_);
v___x_3272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3252_, v___x_3270_, v___x_3271_, v___x_3268_, v_a_3137_);
lean_dec(v_a_3252_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_dec_ref(v___x_3272_);
goto v___jp_3253_;
}
else
{
lean_dec(v_a_3251_);
return v___x_3272_;
}
}
}
else
{
size_t v___x_3273_; size_t v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = ((size_t)0ULL);
v___x_3274_ = lean_usize_of_nat(v___x_3266_);
v___x_3275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3252_, v___x_3273_, v___x_3274_, v___x_3268_, v_a_3137_);
lean_dec(v_a_3252_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_dec_ref(v___x_3275_);
goto v___jp_3253_;
}
else
{
lean_dec(v_a_3251_);
return v___x_3275_;
}
}
}
v___jp_3253_:
{
lean_object* v_stderr_3254_; lean_object* v___x_3255_; 
v_stderr_3254_ = lean_ctor_get(v_a_3251_, 1);
lean_inc_ref(v_stderr_3254_);
v___x_3255_ = l_Lean_Json_parse(v_stderr_3254_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; 
lean_inc_ref(v_stderr_3254_);
lean_dec(v_a_3251_);
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref(v___x_3255_);
v_stderr_3210_ = v_stderr_3254_;
v_a_3211_ = v_a_3256_;
goto v___jp_3209_;
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3258_; 
v_a_3257_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3257_);
lean_dec_ref(v___x_3255_);
v___x_3258_ = l_Lean_Json_getObj_x3f(v_a_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; 
lean_inc_ref(v_stderr_3254_);
lean_dec(v_a_3251_);
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref(v___x_3258_);
v_stderr_3210_ = v_stderr_3254_;
v_a_3211_ = v_a_3259_;
goto v___jp_3209_;
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_a_3260_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3260_);
lean_dec_ref(v___x_3258_);
v___x_3261_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__28));
v___x_3262_ = l_Lake_JsonObject_getJson_x3f(v_a_3260_, v___x_3261_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_inc_ref(v_stderr_3254_);
lean_dec(v_a_3260_);
lean_dec(v_a_3251_);
v_stderr_3158_ = v_stderr_3254_;
goto v___jp_3157_;
}
else
{
lean_object* v_val_3263_; lean_object* v___x_3264_; 
v_val_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_val_3263_);
lean_dec_ref(v___x_3262_);
v___x_3264_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3263_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_dec_ref(v___x_3264_);
v___y_3198_ = v_a_3251_;
v___y_3199_ = v_a_3260_;
goto v___jp_3197_;
}
else
{
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_dec_ref(v___x_3264_);
v___y_3198_ = v_a_3251_;
v___y_3199_ = v_a_3260_;
goto v___jp_3197_;
}
else
{
lean_object* v_a_3265_; 
lean_dec(v_a_3260_);
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3264_);
v___y_3170_ = v_a_3251_;
v_a_3171_ = v_a_3265_;
goto v___jp_3169_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v_a_3276_ = lean_ctor_get(v___x_3250_, 1);
lean_inc(v_a_3276_);
lean_dec_ref(v___x_3250_);
v___x_3277_ = lean_array_get_size(v_a_3276_);
v___x_3278_ = lean_nat_dec_lt(v___x_3245_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
lean_dec(v_a_3276_);
v___x_3279_ = lean_box(0);
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
return v___x_3280_;
}
else
{
lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_nat_dec_le(v___x_3277_, v___x_3277_);
if (v___x_3282_ == 0)
{
if (v___x_3278_ == 0)
{
lean_dec(v_a_3276_);
goto v___jp_3222_;
}
else
{
size_t v___x_3283_; size_t v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = ((size_t)0ULL);
v___x_3284_ = lean_usize_of_nat(v___x_3277_);
v___x_3285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3276_, v___x_3283_, v___x_3284_, v___x_3281_, v_a_3137_);
lean_dec(v_a_3276_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_dec_ref(v___x_3285_);
goto v___jp_3222_;
}
else
{
return v___x_3285_;
}
}
}
else
{
size_t v___x_3286_; size_t v___x_3287_; lean_object* v___x_3288_; 
v___x_3286_ = ((size_t)0ULL);
v___x_3287_ = lean_usize_of_nat(v___x_3277_);
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_3276_, v___x_3286_, v___x_3287_, v___x_3281_, v_a_3137_);
lean_dec(v_a_3276_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_dec_ref(v___x_3288_);
goto v___jp_3222_;
}
else
{
return v___x_3288_;
}
}
}
}
v___jp_3143_:
{
lean_object* v_stderr_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_stderr_3146_ = lean_ctor_get(v___y_3144_, 1);
lean_inc_ref(v_stderr_3146_);
lean_dec_ref(v___y_3144_);
v___x_3147_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__0));
v___x_3148_ = lean_string_append(v___x_3147_, v_a_3145_);
lean_dec_ref(v_a_3145_);
v___x_3149_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__1));
v___x_3150_ = lean_string_append(v___x_3148_, v___x_3149_);
v___x_3151_ = lean_string_append(v___x_3150_, v_stderr_3146_);
lean_dec_ref(v_stderr_3146_);
v___x_3152_ = 3;
v___x_3153_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set_uint8(v___x_3153_, sizeof(void*)*1, v___x_3152_);
lean_inc_ref(v_a_3137_);
v___x_3154_ = lean_apply_2(v_a_3137_, v___x_3153_, lean_box(0));
v___x_3155_ = lean_box(0);
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
v___jp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3159_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__2));
v___x_3160_ = lean_string_append(v___x_3159_, v_stderr_3158_);
lean_dec_ref(v_stderr_3158_);
v___x_3161_ = 3;
v___x_3162_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set_uint8(v___x_3162_, sizeof(void*)*1, v___x_3161_);
lean_inc_ref(v_a_3137_);
v___x_3163_ = lean_apply_2(v_a_3137_, v___x_3162_, lean_box(0));
v___x_3164_ = lean_box(0);
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
v___jp_3166_:
{
lean_object* v_stderr_3168_; 
v_stderr_3168_ = lean_ctor_get(v___y_3167_, 1);
lean_inc_ref(v_stderr_3168_);
lean_dec_ref(v___y_3167_);
v_stderr_3158_ = v_stderr_3168_;
goto v___jp_3157_;
}
v___jp_3169_:
{
if (lean_obj_tag(v_a_3171_) == 0)
{
v___y_3167_ = v___y_3170_;
goto v___jp_3166_;
}
else
{
lean_object* v_val_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3196_; 
v_val_3172_ = lean_ctor_get(v_a_3171_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_a_3171_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3174_ = v_a_3171_;
v_isShared_3175_ = v_isSharedCheck_3196_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_val_3172_);
lean_dec(v_a_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3196_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3176_ = lean_unsigned_to_nat(200u);
v___x_3177_ = lean_nat_dec_eq(v_val_3172_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v_stdout_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v_stdout_3178_ = lean_ctor_get(v___y_3170_, 0);
lean_inc_ref(v_stdout_3178_);
lean_dec_ref(v___y_3170_);
v___x_3179_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__3));
v___x_3180_ = l_Nat_reprFast(v_val_3172_);
v___x_3181_ = lean_string_append(v___x_3179_, v___x_3180_);
lean_dec_ref(v___x_3180_);
v___x_3182_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3183_ = lean_string_append(v___x_3181_, v___x_3182_);
v___x_3184_ = lean_string_append(v___x_3183_, v_stdout_3178_);
lean_dec_ref(v_stdout_3178_);
v___x_3185_ = 3;
v___x_3186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*1, v___x_3185_);
lean_inc_ref(v_a_3137_);
v___x_3187_ = lean_apply_2(v_a_3137_, v___x_3186_, lean_box(0));
v___x_3188_ = lean_box(0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3188_);
v___x_3190_ = v___x_3174_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_dec(v_val_3172_);
lean_dec_ref(v___y_3170_);
v___x_3192_ = lean_box(0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3192_);
v___x_3194_ = v___x_3174_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
v___jp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3201_ = l_Lake_JsonObject_getJson_x3f(v___y_3199_, v___x_3200_);
lean_dec(v___y_3199_);
if (lean_obj_tag(v___x_3201_) == 0)
{
v___y_3167_ = v___y_3198_;
goto v___jp_3166_;
}
else
{
lean_object* v_val_3202_; lean_object* v___x_3203_; 
v_val_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_val_3202_);
lean_dec_ref(v___x_3201_);
v___x_3203_ = l_Option_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_uploadS3_spec__0(v_val_3202_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3206_ = lean_string_append(v___x_3205_, v_a_3204_);
lean_dec(v_a_3204_);
v___y_3144_ = v___y_3198_;
v_a_3145_ = v___x_3206_;
goto v___jp_3143_;
}
else
{
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3207_; 
v_a_3207_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3207_);
lean_dec_ref(v___x_3203_);
v___y_3144_ = v___y_3198_;
v_a_3145_ = v_a_3207_;
goto v___jp_3143_;
}
else
{
lean_object* v_a_3208_; 
v_a_3208_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v___x_3203_);
v___y_3170_ = v___y_3198_;
v_a_3171_ = v_a_3208_;
goto v___jp_3169_;
}
}
}
}
v___jp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3212_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__7));
v___x_3213_ = lean_string_append(v___x_3212_, v_a_3211_);
lean_dec_ref(v_a_3211_);
v___x_3214_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__4));
v___x_3215_ = lean_string_append(v___x_3213_, v___x_3214_);
v___x_3216_ = lean_string_append(v___x_3215_, v_stderr_3210_);
lean_dec_ref(v_stderr_3210_);
v___x_3217_ = 3;
v___x_3218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1, v___x_3217_);
lean_inc_ref(v_a_3137_);
v___x_3219_ = lean_apply_2(v_a_3137_, v___x_3218_, lean_box(0));
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
return v___x_3221_;
}
v___jp_3222_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_box(0);
v___x_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0___boxed(lean_object* v_a_3289_, lean_object* v_file_3290_, lean_object* v_contentType_3291_, lean_object* v_url_3292_, lean_object* v_key_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3289_, v_file_3290_, v_contentType_3291_, v_url_3292_, v_key_3293_);
lean_dec_ref(v_contentType_3291_);
lean_dec_ref(v_a_3289_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact(uint64_t v_contentHash_3297_, lean_object* v_art_3298_, lean_object* v_service_3299_, lean_object* v_scope_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_url_3303_; lean_object* v___y_3305_; lean_object* v_s_3322_; 
lean_inc_ref(v_scope_3300_);
lean_inc_ref(v_service_3299_);
v_url_3303_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl(v_contentHash_3297_, v_service_3299_, v_scope_3300_);
v_s_3322_ = lean_ctor_get(v_scope_3300_, 0);
lean_inc_ref(v_s_3322_);
lean_dec_ref(v_scope_3300_);
v___y_3305_ = v_s_3322_;
goto v___jp_3304_;
v___jp_3304_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v_key_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3306_ = ((lean_object*)(l_Lake_CacheService_uploadArtifact___closed__0));
v___x_3307_ = lean_string_append(v___y_3305_, v___x_3306_);
v___x_3308_ = l_Lake_lowerHexUInt64(v_contentHash_3297_);
v___x_3309_ = lean_string_append(v___x_3307_, v___x_3308_);
lean_dec_ref(v___x_3308_);
v___x_3310_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3311_ = lean_string_append(v___x_3309_, v___x_3310_);
v___x_3312_ = lean_string_append(v___x_3311_, v_art_3298_);
v___x_3313_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3314_ = lean_string_append(v___x_3312_, v___x_3313_);
v___x_3315_ = lean_string_append(v___x_3314_, v_url_3303_);
v___x_3316_ = 1;
v___x_3317_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*1, v___x_3316_);
lean_inc_ref(v_a_3301_);
v___x_3318_ = lean_apply_2(v_a_3301_, v___x_3317_, lean_box(0));
v_key_3319_ = lean_ctor_get(v_service_3299_, 1);
lean_inc_ref(v_key_3319_);
lean_dec_ref(v_service_3299_);
v___x_3320_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3321_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_3301_, v_art_3298_, v___x_3320_, v_url_3303_, v_key_3319_);
return v___x_3321_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifact___boxed(lean_object* v_contentHash_3323_, lean_object* v_art_3324_, lean_object* v_service_3325_, lean_object* v_scope_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
uint64_t v_contentHash_boxed_3329_; lean_object* v_res_3330_; 
v_contentHash_boxed_3329_ = lean_unbox_uint64(v_contentHash_3323_);
lean_dec_ref(v_contentHash_3323_);
v_res_3330_ = l_Lake_CacheService_uploadArtifact(v_contentHash_boxed_3329_, v_art_3324_, v_service_3325_, v_scope_3326_, v_a_3327_);
lean_dec_ref(v_a_3327_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(uint8_t v_x_3331_){
_start:
{
if (v_x_3331_ == 0)
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_unsigned_to_nat(0u);
return v___x_3332_;
}
else
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_unsigned_to_nat(1u);
return v___x_3333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx___boxed(lean_object* v_x_3334_){
_start:
{
uint8_t v_x_boxed_3335_; lean_object* v_res_3336_; 
v_x_boxed_3335_ = lean_unbox(v_x_3334_);
v_res_3336_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_boxed_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(uint8_t v_x_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx___boxed(lean_object* v_x_3339_){
_start:
{
uint8_t v_x_4__boxed_3340_; lean_object* v_res_3341_; 
v_x_4__boxed_3340_ = lean_unbox(v_x_3339_);
v_res_3341_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_toCtorIdx(v_x_4__boxed_3340_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(lean_object* v_k_3342_){
_start:
{
lean_inc(v_k_3342_);
return v_k_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg___boxed(lean_object* v_k_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___redArg(v_k_3343_);
lean_dec(v_k_3343_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(lean_object* v_motive_3345_, lean_object* v_ctorIdx_3346_, uint8_t v_t_3347_, lean_object* v_h_3348_, lean_object* v_k_3349_){
_start:
{
lean_inc(v_k_3349_);
return v_k_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim___boxed(lean_object* v_motive_3350_, lean_object* v_ctorIdx_3351_, lean_object* v_t_3352_, lean_object* v_h_3353_, lean_object* v_k_3354_){
_start:
{
uint8_t v_t_boxed_3355_; lean_object* v_res_3356_; 
v_t_boxed_3355_ = lean_unbox(v_t_3352_);
v_res_3356_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorElim(v_motive_3350_, v_ctorIdx_3351_, v_t_boxed_3355_, v_h_3353_, v_k_3354_);
lean_dec(v_k_3354_);
lean_dec(v_ctorIdx_3351_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(lean_object* v_get_3357_){
_start:
{
lean_inc(v_get_3357_);
return v_get_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg___boxed(lean_object* v_get_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___redArg(v_get_3358_);
lean_dec(v_get_3358_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(lean_object* v_motive_3360_, uint8_t v_t_3361_, lean_object* v_h_3362_, lean_object* v_get_3363_){
_start:
{
lean_inc(v_get_3363_);
return v_get_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim___boxed(lean_object* v_motive_3364_, lean_object* v_t_3365_, lean_object* v_h_3366_, lean_object* v_get_3367_){
_start:
{
uint8_t v_t_boxed_3368_; lean_object* v_res_3369_; 
v_t_boxed_3368_ = lean_unbox(v_t_3365_);
v_res_3369_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_get_elim(v_motive_3364_, v_t_boxed_3368_, v_h_3366_, v_get_3367_);
lean_dec(v_get_3367_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(lean_object* v_put_3370_){
_start:
{
lean_inc(v_put_3370_);
return v_put_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg___boxed(lean_object* v_put_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___redArg(v_put_3371_);
lean_dec(v_put_3371_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(lean_object* v_motive_3373_, uint8_t v_t_3374_, lean_object* v_h_3375_, lean_object* v_put_3376_){
_start:
{
lean_inc(v_put_3376_);
return v_put_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim___boxed(lean_object* v_motive_3377_, lean_object* v_t_3378_, lean_object* v_h_3379_, lean_object* v_put_3380_){
_start:
{
uint8_t v_t_boxed_3381_; lean_object* v_res_3382_; 
v_t_boxed_3381_ = lean_unbox(v_t_3378_);
v_res_3382_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_put_elim(v_motive_3377_, v_t_boxed_3381_, v_h_3379_, v_put_3380_);
lean_dec(v_put_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(lean_object* v_n_3383_){
_start:
{
lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3384_ = lean_unsigned_to_nat(0u);
v___x_3385_ = lean_nat_dec_le(v_n_3383_, v___x_3384_);
if (v___x_3385_ == 0)
{
uint8_t v___x_3386_; 
v___x_3386_ = 1;
return v___x_3386_;
}
else
{
uint8_t v___x_3387_; 
v___x_3387_ = 0;
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat___boxed(lean_object* v_n_3388_){
_start:
{
uint8_t v_res_3389_; lean_object* v_r_3390_; 
v_res_3389_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ofNat(v_n_3388_);
lean_dec(v_n_3388_);
v_r_3390_ = lean_box(v_res_3389_);
return v_r_3390_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(uint8_t v_x_3391_, uint8_t v_y_3392_){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3393_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_x_3391_);
v___x_3394_ = l___private_Lake_Config_Cache_0__Lake_CacheService_TransferKind_ctorIdx(v_y_3392_);
v___x_3395_ = lean_nat_dec_eq(v___x_3393_, v___x_3394_);
lean_dec(v___x_3394_);
lean_dec(v___x_3393_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind___boxed(lean_object* v_x_3396_, lean_object* v_y_3397_){
_start:
{
uint8_t v_x_13__boxed_3398_; uint8_t v_y_14__boxed_3399_; uint8_t v_res_3400_; lean_object* v_r_3401_; 
v_x_13__boxed_3398_ = lean_unbox(v_x_3396_);
v_y_14__boxed_3399_ = lean_unbox(v_y_3397_);
v_res_3400_ = l___private_Lake_Config_Cache_0__Lake_CacheService_instDecidableEqTransferKind(v_x_13__boxed_3398_, v_y_14__boxed_3399_);
v_r_3401_ = lean_box(v_res_3400_);
return v_r_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(lean_object* v_cfg_3403_, lean_object* v_out_3404_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3405_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___closed__0));
v___x_3406_ = l_Lake_JsonObject_getJson_x3f(v_out_3404_, v___x_3405_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_box(0);
return v___x_3407_;
}
else
{
lean_object* v_val_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3424_; 
v_val_3408_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3410_ = v___x_3406_;
v_isShared_3411_ = v_isSharedCheck_3424_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_val_3408_);
lean_dec(v___x_3406_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3424_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Json_getNat_x3f(v_val_3408_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v___x_3413_; 
lean_dec_ref(v___x_3412_);
lean_del_object(v___x_3410_);
v___x_3413_ = lean_box(0);
return v___x_3413_;
}
else
{
if (lean_obj_tag(v___x_3412_) == 1)
{
lean_object* v_a_3414_; lean_object* v_infos_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v_a_3414_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___x_3412_);
v_infos_3415_ = lean_ctor_get(v_cfg_3403_, 1);
v___x_3416_ = lean_array_get_size(v_infos_3415_);
v___x_3417_ = lean_nat_dec_lt(v_a_3414_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; 
lean_dec(v_a_3414_);
lean_del_object(v___x_3410_);
v___x_3418_ = lean_box(0);
return v___x_3418_;
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3419_ = lean_array_fget_borrowed(v_infos_3415_, v_a_3414_);
lean_dec(v_a_3414_);
lean_inc(v___x_3419_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3419_);
v___x_3421_ = v___x_3410_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
else
{
lean_object* v___x_3423_; 
lean_dec_ref(v___x_3412_);
lean_del_object(v___x_3410_);
v___x_3423_ = lean_box(0);
return v___x_3423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f___boxed(lean_object* v_cfg_3425_, lean_object* v_out_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_3425_, v_out_3426_);
lean_dec(v_out_3426_);
lean_dec_ref(v_cfg_3425_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(lean_object* v_s_3428_, lean_object* v_pos_3429_){
_start:
{
lean_object* v_str_3430_; lean_object* v_startInclusive_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v_str_3430_ = lean_ctor_get(v_s_3428_, 0);
v_startInclusive_3431_ = lean_ctor_get(v_s_3428_, 1);
v___x_3432_ = lean_nat_add(v_startInclusive_3431_, v_pos_3429_);
v___x_3433_ = lean_nat_sub(v___x_3432_, v_startInclusive_3431_);
v___x_3434_ = lean_unsigned_to_nat(0u);
v___x_3435_ = lean_nat_dec_eq(v___x_3433_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; uint8_t v___y_3444_; lean_object* v___x_3445_; uint32_t v___x_3446_; uint8_t v___y_3448_; uint32_t v___x_3453_; uint8_t v___x_3454_; 
lean_inc(v_startInclusive_3431_);
lean_inc_ref(v_str_3430_);
v___x_3436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3436_, 0, v_str_3430_);
lean_ctor_set(v___x_3436_, 1, v_startInclusive_3431_);
lean_ctor_set(v___x_3436_, 2, v___x_3432_);
v___x_3437_ = lean_unsigned_to_nat(1u);
v___x_3438_ = lean_nat_sub(v___x_3433_, v___x_3437_);
lean_dec(v___x_3433_);
v___x_3439_ = l_String_Slice_posLE(v___x_3436_, v___x_3438_);
lean_dec_ref(v___x_3436_);
v___x_3445_ = lean_nat_add(v_startInclusive_3431_, v___x_3439_);
v___x_3446_ = lean_string_utf8_get_fast(v_str_3430_, v___x_3445_);
lean_dec(v___x_3445_);
v___x_3453_ = 32;
v___x_3454_ = lean_uint32_dec_eq(v___x_3446_, v___x_3453_);
if (v___x_3454_ == 0)
{
uint32_t v___x_3455_; uint8_t v___x_3456_; 
v___x_3455_ = 9;
v___x_3456_ = lean_uint32_dec_eq(v___x_3446_, v___x_3455_);
v___y_3448_ = v___x_3456_;
goto v___jp_3447_;
}
else
{
v___y_3448_ = v___x_3454_;
goto v___jp_3447_;
}
v___jp_3440_:
{
uint8_t v___x_3441_; 
v___x_3441_ = lean_nat_dec_lt(v___x_3439_, v_pos_3429_);
if (v___x_3441_ == 0)
{
lean_dec(v___x_3439_);
return v_pos_3429_;
}
else
{
lean_dec(v_pos_3429_);
v_pos_3429_ = v___x_3439_;
goto _start;
}
}
v___jp_3443_:
{
if (v___y_3444_ == 0)
{
lean_dec(v___x_3439_);
return v_pos_3429_;
}
else
{
goto v___jp_3440_;
}
}
v___jp_3447_:
{
if (v___y_3448_ == 0)
{
uint32_t v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = 13;
v___x_3450_ = lean_uint32_dec_eq(v___x_3446_, v___x_3449_);
if (v___x_3450_ == 0)
{
uint32_t v___x_3451_; uint8_t v___x_3452_; 
v___x_3451_ = 10;
v___x_3452_ = lean_uint32_dec_eq(v___x_3446_, v___x_3451_);
v___y_3444_ = v___x_3452_;
goto v___jp_3443_;
}
else
{
v___y_3444_ = v___x_3450_;
goto v___jp_3443_;
}
}
else
{
goto v___jp_3440_;
}
}
}
else
{
lean_dec(v___x_3433_);
lean_dec(v___x_3432_);
return v_pos_3429_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0___boxed(lean_object* v_s_3457_, lean_object* v_pos_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v_s_3457_, v_pos_3458_);
lean_dec_ref(v_s_3457_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(lean_object* v_cfg_3472_, lean_object* v_hOut_3473_, lean_object* v_info_3474_, lean_object* v_code_x3f_3475_, lean_object* v_out_3476_, lean_object* v_line_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_msg_3481_; lean_object* v___y_3482_; lean_object* v___y_3499_; lean_object* v_msg_3500_; lean_object* v___y_3501_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v_a_3520_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v_val_3531_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; uint8_t v_kind_3574_; lean_object* v_scope_3575_; lean_object* v_msg_3577_; lean_object* v___y_3578_; lean_object* v_msg_3619_; lean_object* v___y_3620_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3649_; 
v_kind_3574_ = lean_ctor_get_uint8(v_cfg_3472_, sizeof(void*)*3);
v_scope_3575_ = lean_ctor_get(v_cfg_3472_, 0);
lean_inc_ref(v_scope_3575_);
lean_dec_ref(v_cfg_3472_);
if (v_kind_3574_ == 0)
{
lean_object* v___x_3651_; 
v___x_3651_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___y_3649_ = v___x_3651_;
goto v___jp_3648_;
}
else
{
lean_object* v___x_3652_; 
v___x_3652_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___y_3649_ = v___x_3652_;
goto v___jp_3648_;
}
v___jp_3480_:
{
uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3483_ = 3;
v___x_3484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3484_, 0, v_msg_3481_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*1, v___x_3483_);
lean_inc_ref_n(v___y_3482_, 2);
v___x_3485_ = lean_apply_2(v___y_3482_, v___x_3484_, lean_box(0));
v___x_3486_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__0));
v___x_3487_ = lean_unsigned_to_nat(0u);
v___x_3488_ = lean_string_utf8_byte_size(v_line_3477_);
lean_inc_ref(v_line_3477_);
v___x_3489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3489_, 0, v_line_3477_);
lean_ctor_set(v___x_3489_, 1, v___x_3487_);
lean_ctor_set(v___x_3489_, 2, v___x_3488_);
v___x_3490_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_3489_, v___x_3488_);
lean_dec_ref(v___x_3489_);
v___x_3491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3491_, 0, v_line_3477_);
lean_ctor_set(v___x_3491_, 1, v___x_3487_);
lean_ctor_set(v___x_3491_, 2, v___x_3490_);
v___x_3492_ = l_String_Slice_toString(v___x_3491_);
lean_dec_ref(v___x_3491_);
v___x_3493_ = lean_string_append(v___x_3486_, v___x_3492_);
lean_dec_ref(v___x_3492_);
v___x_3494_ = 0;
v___x_3495_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*1, v___x_3494_);
v___x_3496_ = lean_apply_2(v___y_3482_, v___x_3495_, lean_box(0));
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
return v___x_3497_;
}
v___jp_3498_:
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Lake_removeFileIfExists(v___y_3499_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_dec_ref(v___x_3502_);
v_msg_3481_ = v_msg_3500_;
v___y_3482_ = v___y_3501_;
goto v___jp_3480_;
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v_msg_3500_);
lean_dec_ref(v_line_3477_);
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3515_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3515_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; uint8_t v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3507_ = lean_io_error_to_string(v_a_3503_);
v___x_3508_ = 3;
v___x_3509_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3509_, 0, v___x_3507_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*1, v___x_3508_);
lean_inc_ref(v___y_3501_);
v___x_3510_ = lean_apply_2(v___y_3501_, v___x_3509_, lean_box(0));
v___x_3511_ = lean_box(0);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3511_);
v___x_3513_ = v___x_3505_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
v___jp_3516_:
{
if (lean_obj_tag(v_a_3520_) == 1)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v_a_3521_ = lean_ctor_get(v_a_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref(v_a_3520_);
v___x_3522_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3523_ = lean_string_append(v___y_3517_, v___x_3522_);
v___x_3524_ = lean_string_append(v___x_3523_, v_a_3521_);
lean_dec(v_a_3521_);
v___y_3499_ = v___y_3519_;
v_msg_3500_ = v___x_3524_;
v___y_3501_ = v___y_3518_;
goto v___jp_3498_;
}
else
{
lean_dec_ref(v_a_3520_);
v___y_3499_ = v___y_3519_;
v_msg_3500_ = v___y_3517_;
v___y_3501_ = v___y_3518_;
goto v___jp_3498_;
}
}
v___jp_3525_:
{
lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3532_ = lean_array_get_size(v___y_3527_);
v___x_3533_ = lean_nat_dec_lt(v___y_3529_, v___x_3532_);
if (v___x_3533_ == 0)
{
v___y_3517_ = v___y_3526_;
v___y_3518_ = v___y_3528_;
v___y_3519_ = v___y_3530_;
v_a_3520_ = v_val_3531_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3534_ = lean_box(0);
v___x_3535_ = lean_nat_dec_le(v___x_3532_, v___x_3532_);
if (v___x_3535_ == 0)
{
if (v___x_3533_ == 0)
{
v___y_3517_ = v___y_3526_;
v___y_3518_ = v___y_3528_;
v___y_3519_ = v___y_3530_;
v_a_3520_ = v_val_3531_;
goto v___jp_3516_;
}
else
{
size_t v___x_3536_; size_t v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = ((size_t)0ULL);
v___x_3537_ = lean_usize_of_nat(v___x_3532_);
v___x_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3527_, v___x_3536_, v___x_3537_, v___x_3534_, v___y_3528_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_dec_ref(v___x_3538_);
v___y_3517_ = v___y_3526_;
v___y_3518_ = v___y_3528_;
v___y_3519_ = v___y_3530_;
v_a_3520_ = v_val_3531_;
goto v___jp_3516_;
}
else
{
lean_dec_ref(v_val_3531_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v_line_3477_);
return v___x_3538_;
}
}
}
else
{
size_t v___x_3539_; size_t v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = ((size_t)0ULL);
v___x_3540_ = lean_usize_of_nat(v___x_3532_);
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___y_3527_, v___x_3539_, v___x_3540_, v___x_3534_, v___y_3528_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_dec_ref(v___x_3541_);
v___y_3517_ = v___y_3526_;
v___y_3518_ = v___y_3528_;
v___y_3519_ = v___y_3530_;
v_a_3520_ = v_val_3531_;
goto v___jp_3516_;
}
else
{
lean_dec_ref(v_val_3531_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v_line_3477_);
return v___x_3541_;
}
}
}
}
v___jp_3542_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3547_ = l_Lake_JsonObject_getJson_x3f(v_out_3476_, v___x_3546_);
if (lean_obj_tag(v___x_3547_) == 0)
{
v___y_3499_ = v___y_3545_;
v_msg_3500_ = v___y_3543_;
v___y_3501_ = v___y_3544_;
goto v___jp_3498_;
}
else
{
lean_object* v_val_3548_; lean_object* v___x_3549_; 
v_val_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_val_3548_);
lean_dec_ref(v___x_3547_);
v___x_3549_ = l_Lean_Json_getNat_x3f(v_val_3548_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_dec_ref(v___x_3549_);
v___y_3499_ = v___y_3545_;
v_msg_3500_ = v___y_3543_;
v___y_3501_ = v___y_3544_;
goto v___jp_3498_;
}
else
{
if (lean_obj_tag(v___x_3549_) == 1)
{
lean_object* v_a_3550_; lean_object* v___x_3551_; uint8_t v___x_3552_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref(v___x_3549_);
v___x_3551_ = lean_unsigned_to_nat(0u);
v___x_3552_ = lean_nat_dec_lt(v___x_3551_, v_a_3550_);
lean_dec(v_a_3550_);
if (v___x_3552_ == 0)
{
v___y_3499_ = v___y_3545_;
v_msg_3500_ = v___y_3543_;
v___y_3501_ = v___y_3544_;
goto v___jp_3498_;
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__3));
v___x_3554_ = l_Lake_JsonObject_getJson_x3f(v_out_3476_, v___x_3553_);
if (lean_obj_tag(v___x_3554_) == 0)
{
v___y_3499_ = v___y_3545_;
v_msg_3500_ = v___y_3543_;
v___y_3501_ = v___y_3544_;
goto v___jp_3498_;
}
else
{
lean_object* v_val_3555_; lean_object* v___x_3556_; 
v_val_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_val_3555_);
lean_dec_ref(v___x_3554_);
v___x_3556_ = l_Lean_Json_getStr_x3f(v_val_3555_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_dec_ref(v___x_3556_);
v___y_3499_ = v___y_3545_;
v_msg_3500_ = v___y_3543_;
v___y_3501_ = v___y_3544_;
goto v___jp_3498_;
}
else
{
if (lean_obj_tag(v___x_3556_) == 1)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3573_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3573_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3573_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3561_ = ((lean_object*)(l_Lake_CacheService_artifactContentType___closed__0));
v___x_3562_ = lean_string_dec_eq(v_a_3557_, v___x_3561_);
lean_dec(v_a_3557_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_3564_ = l_IO_FS_readFile(v___y_3545_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref(v___x_3564_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v_a_3565_);
v___x_3567_ = v___x_3559_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
v___y_3526_ = v___y_3543_;
v___y_3527_ = v___x_3563_;
v___y_3528_ = v___y_3544_;
v___y_3529_ = v___x_3551_;
v___y_3530_ = v___y_3545_;
v_val_3531_ = v___x_3567_;
goto v___jp_3525_;
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; 
v_a_3569_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___x_3564_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set_tag(v___x_3559_, 0);
lean_ctor_set(v___x_3559_, 0, v_a_3569_);
v___x_3571_ = v___x_3559_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
v___y_3526_ = v___y_3543_;
v___y_3527_ = v___x_3563_;
v___y_3528_ = v___y_3544_;
v___y_3529_ = v___x_3551_;
v___y_3530_ = v___y_3545_;
v_val_3531_ = v___x_3571_;
goto v___jp_3525_;
}
}
}
else
{
lean_del_object(v___x_3559_);
v___y_3499_ = v___y_3545_;
v_msg_3500_ = v___y_3543_;
v___y_3501_ = v___y_3544_;
goto v___jp_3498_;
}
}
}
else
{
lean_dec_ref(v___x_3556_);
v___y_3499_ = v___y_3545_;
v_msg_3500_ = v___y_3543_;
v___y_3501_ = v___y_3544_;
goto v___jp_3498_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3549_);
v___y_3499_ = v___y_3545_;
v_msg_3500_ = v___y_3543_;
v___y_3501_ = v___y_3544_;
goto v___jp_3498_;
}
}
}
}
v___jp_3576_:
{
lean_object* v_url_3579_; lean_object* v_path_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v_msg_3586_; 
v_url_3579_ = lean_ctor_get(v_info_3474_, 0);
v_path_3580_ = lean_ctor_get(v_info_3474_, 1);
v___x_3581_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3582_ = lean_string_append(v_msg_3577_, v___x_3581_);
v___x_3583_ = lean_string_append(v___x_3582_, v_path_3580_);
v___x_3584_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3585_ = lean_string_append(v___x_3583_, v___x_3584_);
v_msg_3586_ = lean_string_append(v___x_3585_, v_url_3579_);
if (v_kind_3574_ == 0)
{
if (lean_obj_tag(v_code_x3f_3475_) == 1)
{
lean_object* v_a_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v_a_3587_ = lean_ctor_get(v_code_x3f_3475_, 0);
lean_inc(v_a_3587_);
lean_dec_ref(v_code_x3f_3475_);
v___x_3588_ = lean_unsigned_to_nat(404u);
v___x_3589_ = lean_nat_dec_eq(v_a_3587_, v___x_3588_);
lean_dec(v_a_3587_);
if (v___x_3589_ == 0)
{
v___y_3543_ = v_msg_3586_;
v___y_3544_ = v___y_3578_;
v___y_3545_ = v_path_3580_;
goto v___jp_3542_;
}
else
{
v___y_3499_ = v_path_3580_;
v_msg_3500_ = v_msg_3586_;
v___y_3501_ = v___y_3578_;
goto v___jp_3498_;
}
}
else
{
lean_dec_ref(v_code_x3f_3475_);
v___y_3543_ = v_msg_3586_;
v___y_3544_ = v___y_3578_;
v___y_3545_ = v_path_3580_;
goto v___jp_3542_;
}
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
lean_dec_ref(v_code_x3f_3475_);
v___x_3590_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__2));
v___x_3591_ = l_Lake_JsonObject_getJson_x3f(v_out_3476_, v___x_3590_);
if (lean_obj_tag(v___x_3591_) == 0)
{
v_msg_3481_ = v_msg_3586_;
v___y_3482_ = v___y_3578_;
goto v___jp_3480_;
}
else
{
lean_object* v_val_3592_; lean_object* v___x_3593_; 
v_val_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_val_3592_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = l_Lean_Json_getNat_x3f(v_val_3592_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_dec_ref(v___x_3593_);
v_msg_3481_ = v_msg_3586_;
v___y_3482_ = v___y_3578_;
goto v___jp_3480_;
}
else
{
if (lean_obj_tag(v___x_3593_) == 1)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = lean_unsigned_to_nat(0u);
v___x_3596_ = lean_nat_dec_lt(v___x_3595_, v_a_3594_);
if (v___x_3596_ == 0)
{
lean_dec(v_a_3594_);
v_msg_3481_ = v_msg_3586_;
v___y_3482_ = v___y_3578_;
goto v___jp_3480_;
}
else
{
size_t v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = lean_usize_of_nat(v_a_3594_);
lean_dec(v_a_3594_);
v___x_3598_ = lean_io_prim_handle_read(v_hOut_3473_, v___x_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; uint8_t v___x_3600_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v___x_3598_);
v___x_3600_ = lean_string_validate_utf8(v_a_3599_);
if (v___x_3600_ == 0)
{
lean_dec(v_a_3599_);
v_msg_3481_ = v_msg_3586_;
v___y_3482_ = v___y_3578_;
goto v___jp_3480_;
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3601_ = lean_string_from_utf8_unchecked(v_a_3599_);
v___x_3602_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__1));
v___x_3603_ = lean_string_append(v_msg_3586_, v___x_3602_);
v___x_3604_ = lean_string_append(v___x_3603_, v___x_3601_);
lean_dec_ref(v___x_3601_);
v_msg_3481_ = v___x_3604_;
v___y_3482_ = v___y_3578_;
goto v___jp_3480_;
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref(v_msg_3586_);
lean_dec_ref(v_line_3477_);
v_a_3605_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3607_ = v___x_3598_;
v_isShared_3608_ = v_isSharedCheck_3617_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3598_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3617_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; uint8_t v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3609_ = lean_io_error_to_string(v_a_3605_);
v___x_3610_ = 3;
v___x_3611_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*1, v___x_3610_);
lean_inc_ref(v___y_3578_);
v___x_3612_ = lean_apply_2(v___y_3578_, v___x_3611_, lean_box(0));
v___x_3613_ = lean_box(0);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3613_);
v___x_3615_ = v___x_3607_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3593_);
v_msg_3481_ = v_msg_3586_;
v___y_3482_ = v___y_3578_;
goto v___jp_3480_;
}
}
}
}
}
v___jp_3618_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_3622_ = l_Lake_JsonObject_getJson_x3f(v_out_3476_, v___x_3621_);
if (lean_obj_tag(v___x_3622_) == 0)
{
v_msg_3577_ = v_msg_3619_;
v___y_3578_ = v___y_3620_;
goto v___jp_3576_;
}
else
{
lean_object* v_val_3623_; lean_object* v___x_3624_; 
v_val_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_val_3623_);
lean_dec_ref(v___x_3622_);
v___x_3624_ = l_Lean_Json_getStr_x3f(v_val_3623_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_dec_ref(v___x_3624_);
v_msg_3577_ = v_msg_3619_;
v___y_3578_ = v___y_3620_;
goto v___jp_3576_;
}
else
{
if (lean_obj_tag(v___x_3624_) == 1)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v_msg_3628_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref(v___x_3624_);
v___x_3626_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__5));
v___x_3627_ = lean_string_append(v_msg_3619_, v___x_3626_);
v_msg_3628_ = lean_string_append(v___x_3627_, v_a_3625_);
lean_dec(v_a_3625_);
v_msg_3577_ = v_msg_3628_;
v___y_3578_ = v___y_3620_;
goto v___jp_3576_;
}
else
{
lean_dec_ref(v___x_3624_);
v_msg_3577_ = v_msg_3619_;
v___y_3578_ = v___y_3620_;
goto v___jp_3576_;
}
}
}
}
v___jp_3629_:
{
lean_object* v_descr_3632_; uint64_t v_hash_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v_msg_3640_; 
v_descr_3632_ = lean_ctor_get(v_info_3474_, 2);
v_hash_3633_ = lean_ctor_get_uint64(v_descr_3632_, sizeof(void*)*1);
v___x_3634_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_3635_ = lean_string_append(v___y_3631_, v___x_3634_);
v___x_3636_ = lean_string_append(v___x_3635_, v___y_3630_);
v___x_3637_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__7));
v___x_3638_ = lean_string_append(v___x_3636_, v___x_3637_);
v___x_3639_ = l_Lake_lowerHexUInt64(v_hash_3633_);
v_msg_3640_ = lean_string_append(v___x_3638_, v___x_3639_);
lean_dec_ref(v___x_3639_);
if (lean_obj_tag(v_code_x3f_3475_) == 1)
{
lean_object* v_a_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_msg_3647_; 
v_a_3641_ = lean_ctor_get(v_code_x3f_3475_, 0);
v___x_3642_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__8));
v___x_3643_ = lean_string_append(v_msg_3640_, v___x_3642_);
lean_inc(v_a_3641_);
v___x_3644_ = l_Nat_reprFast(v_a_3641_);
v___x_3645_ = lean_string_append(v___x_3643_, v___x_3644_);
lean_dec_ref(v___x_3644_);
v___x_3646_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v_msg_3647_ = lean_string_append(v___x_3645_, v___x_3646_);
v_msg_3619_ = v_msg_3647_;
v___y_3620_ = v_a_3478_;
goto v___jp_3618_;
}
else
{
v_msg_3619_ = v_msg_3640_;
v___y_3620_ = v_a_3478_;
goto v___jp_3618_;
}
}
v___jp_3648_:
{
lean_object* v_s_3650_; 
v_s_3650_ = lean_ctor_get(v_scope_3575_, 0);
lean_inc_ref(v_s_3650_);
lean_dec_ref(v_scope_3575_);
v___y_3630_ = v___y_3649_;
v___y_3631_ = v_s_3650_;
goto v___jp_3629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___boxed(lean_object* v_cfg_3653_, lean_object* v_hOut_3654_, lean_object* v_info_3655_, lean_object* v_code_x3f_3656_, lean_object* v_out_3657_, lean_object* v_line_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3653_, v_hOut_3654_, v_info_3655_, v_code_x3f_3656_, v_out_3657_, v_line_3658_, v_a_3659_);
lean_dec_ref(v_a_3659_);
lean_dec(v_out_3657_);
lean_dec_ref(v_info_3655_);
lean_dec(v_hOut_3654_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(lean_object* v_cfg_3662_, lean_object* v_hOut_3663_, lean_object* v_val_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, uint8_t v___x_3667_, lean_object* v_code_x3f_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure(v_cfg_3662_, v_hOut_3663_, v_val_3664_, v_code_x3f_3668_, v_a_3665_, v_a_3666_, v___y_3670_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3689_; 
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___x_3672_, 0);
lean_dec(v_unused_3690_);
v___x_3674_ = v___x_3672_;
v_isShared_3675_ = v_isSharedCheck_3689_;
goto v_resetjp_3673_;
}
else
{
lean_dec(v___x_3672_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3689_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v_numSuccesses_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3688_; 
v_numSuccesses_3676_ = lean_ctor_get(v___y_3669_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___y_3669_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3678_ = v___y_3669_;
v_isShared_3679_ = v_isSharedCheck_3688_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_numSuccesses_3676_);
lean_dec(v___y_3669_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3688_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3680_ = lean_box(0);
if (v_isShared_3679_ == 0)
{
v___x_3682_ = v___x_3678_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_numSuccesses_3676_);
v___x_3682_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3685_; 
lean_ctor_set_uint8(v___x_3682_, sizeof(void*)*1, v___x_3667_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3680_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3683_);
v___x_3685_ = v___x_3674_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v___y_3669_);
v_a_3691_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3672_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3672_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed(lean_object* v_cfg_3699_, lean_object* v_hOut_3700_, lean_object* v_val_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v___x_3704_, lean_object* v_code_x3f_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v___x_28076__boxed_3709_; lean_object* v_res_3710_; 
v___x_28076__boxed_3709_ = lean_unbox(v___x_3704_);
v_res_3710_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_3699_, v_hOut_3700_, v_val_3701_, v_a_3702_, v_a_3703_, v___x_28076__boxed_3709_, v_code_x3f_3705_, v___y_3706_, v___y_3707_);
lean_dec_ref(v___y_3707_);
lean_dec(v_a_3702_);
lean_dec_ref(v_val_3701_);
lean_dec(v_hOut_3700_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(lean_object* v_cfg_3713_, lean_object* v_path_3714_, uint8_t v___x_3715_, lean_object* v_descr_3716_, lean_object* v_url_3717_, uint8_t v___x_3718_, lean_object* v_00___3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
uint64_t v___y_3724_; lean_object* v___y_3764_; lean_object* v___y_3819_; uint8_t v_kind_3848_; 
v_kind_3848_ = lean_ctor_get_uint8(v_cfg_3713_, sizeof(void*)*3);
if (v_kind_3848_ == 0)
{
lean_object* v_scope_3849_; lean_object* v_s_3850_; 
v_scope_3849_ = lean_ctor_get(v_cfg_3713_, 0);
lean_inc_ref(v_scope_3849_);
lean_dec_ref(v_cfg_3713_);
v_s_3850_ = lean_ctor_get(v_scope_3849_, 0);
lean_inc_ref(v_s_3850_);
lean_dec_ref(v_scope_3849_);
v___y_3764_ = v_s_3850_;
goto v___jp_3763_;
}
else
{
lean_object* v_scope_3851_; lean_object* v_s_3852_; 
v_scope_3851_ = lean_ctor_get(v_cfg_3713_, 0);
lean_inc_ref(v_scope_3851_);
lean_dec_ref(v_cfg_3713_);
v_s_3852_ = lean_ctor_get(v_scope_3851_, 0);
lean_inc_ref(v_s_3852_);
lean_dec_ref(v_scope_3851_);
v___y_3819_ = v_s_3852_;
goto v___jp_3818_;
}
v___jp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3725_ = ((lean_object*)(l_Lake_downloadArtifactCore___closed__1));
lean_inc_ref(v_path_3714_);
v___x_3726_ = lean_string_append(v_path_3714_, v___x_3725_);
v___x_3727_ = l_Lake_lowerHexUInt64(v___y_3724_);
v___x_3728_ = lean_string_append(v___x_3726_, v___x_3727_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = 3;
v___x_3730_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*1, v___x_3729_);
lean_inc_ref(v___y_3721_);
v___x_3731_ = lean_apply_2(v___y_3721_, v___x_3730_, lean_box(0));
v___x_3732_ = lean_io_remove_file(v_path_3714_);
lean_dec_ref(v_path_3714_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3749_; 
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; 
v_unused_3750_ = lean_ctor_get(v___x_3732_, 0);
lean_dec(v_unused_3750_);
v___x_3734_ = v___x_3732_;
v_isShared_3735_ = v_isSharedCheck_3749_;
goto v_resetjp_3733_;
}
else
{
lean_dec(v___x_3732_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3749_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v_numSuccesses_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3748_; 
v_numSuccesses_3736_ = lean_ctor_get(v___y_3720_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___y_3720_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3738_ = v___y_3720_;
v_isShared_3739_ = v_isSharedCheck_3748_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_numSuccesses_3736_);
lean_dec(v___y_3720_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3748_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3740_ = lean_box(0);
if (v_isShared_3739_ == 0)
{
v___x_3742_ = v___x_3738_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_numSuccesses_3736_);
v___x_3742_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3745_; 
lean_ctor_set_uint8(v___x_3742_, sizeof(void*)*1, v___x_3715_);
v___x_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3740_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 0, v___x_3743_);
v___x_3745_ = v___x_3734_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref(v___y_3720_);
v_a_3751_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3753_ = v___x_3732_;
v_isShared_3754_ = v_isSharedCheck_3762_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3732_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3762_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3755_ = lean_io_error_to_string(v_a_3751_);
v___x_3756_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
lean_ctor_set_uint8(v___x_3756_, sizeof(void*)*1, v___x_3729_);
lean_inc_ref(v___y_3721_);
v___x_3757_ = lean_apply_2(v___y_3721_, v___x_3756_, lean_box(0));
v___x_3758_ = lean_box(0);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v___x_3758_);
v___x_3760_ = v___x_3753_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
v___jp_3763_:
{
uint64_t v_hash_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v_hash_3765_ = lean_ctor_get_uint64(v_descr_3716_, sizeof(void*)*1);
v___x_3766_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__0));
v___x_3767_ = lean_string_append(v___y_3764_, v___x_3766_);
v___x_3768_ = l_Lake_lowerHexUInt64(v_hash_3765_);
v___x_3769_ = lean_string_append(v___x_3767_, v___x_3768_);
lean_dec_ref(v___x_3768_);
v___x_3770_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
v___x_3772_ = lean_string_append(v___x_3771_, v_path_3714_);
v___x_3773_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3774_ = lean_string_append(v___x_3772_, v___x_3773_);
v___x_3775_ = lean_string_append(v___x_3774_, v_url_3717_);
v___x_3776_ = 1;
v___x_3777_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3777_, 0, v___x_3775_);
lean_ctor_set_uint8(v___x_3777_, sizeof(void*)*1, v___x_3776_);
lean_inc_ref(v___y_3721_);
v___x_3778_ = lean_apply_2(v___y_3721_, v___x_3777_, lean_box(0));
v___x_3779_ = l_Lake_computeBinFileHash(v_path_3714_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3804_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3782_ = v___x_3779_;
v_isShared_3783_ = v_isSharedCheck_3804_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3779_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3804_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
uint64_t v___x_3784_; uint8_t v___x_3785_; 
v___x_3784_ = lean_unbox_uint64(v_a_3780_);
v___x_3785_ = lean_uint64_dec_eq(v___x_3784_, v_hash_3765_);
if (v___x_3785_ == 0)
{
uint64_t v___x_3786_; 
lean_del_object(v___x_3782_);
v___x_3786_ = lean_unbox_uint64(v_a_3780_);
lean_dec(v_a_3780_);
v___y_3724_ = v___x_3786_;
goto v___jp_3723_;
}
else
{
if (v___x_3718_ == 0)
{
uint8_t v_didError_3787_; lean_object* v_numSuccesses_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3802_; 
lean_dec(v_a_3780_);
lean_dec_ref(v_path_3714_);
v_didError_3787_ = lean_ctor_get_uint8(v___y_3720_, sizeof(void*)*1);
v_numSuccesses_3788_ = lean_ctor_get(v___y_3720_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___y_3720_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3790_ = v___y_3720_;
v_isShared_3791_ = v_isSharedCheck_3802_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_numSuccesses_3788_);
lean_dec(v___y_3720_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3802_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3796_; 
v___x_3792_ = lean_box(0);
v___x_3793_ = lean_unsigned_to_nat(1u);
v___x_3794_ = lean_nat_add(v_numSuccesses_3788_, v___x_3793_);
lean_dec(v_numSuccesses_3788_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v___x_3794_);
v___x_3796_ = v___x_3790_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3794_);
lean_ctor_set_uint8(v_reuseFailAlloc_3801_, sizeof(void*)*1, v_didError_3787_);
v___x_3796_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3792_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3797_);
v___x_3799_ = v___x_3782_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
uint64_t v___x_3803_; 
lean_del_object(v___x_3782_);
v___x_3803_ = lean_unbox_uint64(v_a_3780_);
lean_dec(v_a_3780_);
v___y_3724_ = v___x_3803_;
goto v___jp_3723_;
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3817_; 
lean_dec_ref(v___y_3720_);
lean_dec_ref(v_path_3714_);
v_a_3805_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3807_ = v___x_3779_;
v_isShared_3808_ = v_isSharedCheck_3817_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3779_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3817_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; uint8_t v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3809_ = lean_io_error_to_string(v_a_3805_);
v___x_3810_ = 3;
v___x_3811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set_uint8(v___x_3811_, sizeof(void*)*1, v___x_3810_);
lean_inc_ref(v___y_3721_);
v___x_3812_ = lean_apply_2(v___y_3721_, v___x_3811_, lean_box(0));
v___x_3813_ = lean_box(0);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3813_);
v___x_3815_ = v___x_3807_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
v___jp_3818_:
{
uint64_t v_hash_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v_didError_3834_; lean_object* v_numSuccesses_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3847_; 
v_hash_3820_ = lean_ctor_get_uint64(v_descr_3716_, sizeof(void*)*1);
v___x_3821_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___closed__1));
v___x_3822_ = lean_string_append(v___y_3819_, v___x_3821_);
v___x_3823_ = l_Lake_lowerHexUInt64(v_hash_3820_);
v___x_3824_ = lean_string_append(v___x_3822_, v___x_3823_);
lean_dec_ref(v___x_3823_);
v___x_3825_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_3826_ = lean_string_append(v___x_3824_, v___x_3825_);
v___x_3827_ = lean_string_append(v___x_3826_, v_path_3714_);
lean_dec_ref(v_path_3714_);
v___x_3828_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_3829_ = lean_string_append(v___x_3827_, v___x_3828_);
v___x_3830_ = lean_string_append(v___x_3829_, v_url_3717_);
v___x_3831_ = 1;
v___x_3832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3832_, 0, v___x_3830_);
lean_ctor_set_uint8(v___x_3832_, sizeof(void*)*1, v___x_3831_);
lean_inc_ref(v___y_3721_);
v___x_3833_ = lean_apply_2(v___y_3721_, v___x_3832_, lean_box(0));
v_didError_3834_ = lean_ctor_get_uint8(v___y_3720_, sizeof(void*)*1);
v_numSuccesses_3835_ = lean_ctor_get(v___y_3720_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___y_3720_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3837_ = v___y_3720_;
v_isShared_3838_ = v_isSharedCheck_3847_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_numSuccesses_3835_);
lean_dec(v___y_3720_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3847_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3839_ = lean_box(0);
v___x_3840_ = lean_unsigned_to_nat(1u);
v___x_3841_ = lean_nat_add(v_numSuccesses_3835_, v___x_3840_);
lean_dec(v_numSuccesses_3835_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3841_);
v___x_3843_ = v___x_3837_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3841_);
lean_ctor_set_uint8(v_reuseFailAlloc_3846_, sizeof(void*)*1, v_didError_3834_);
v___x_3843_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3839_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
return v___x_3845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1___boxed(lean_object* v_cfg_3853_, lean_object* v_path_3854_, lean_object* v___x_3855_, lean_object* v_descr_3856_, lean_object* v_url_3857_, lean_object* v___x_3858_, lean_object* v_00___3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
uint8_t v___x_28156__boxed_3863_; uint8_t v___x_28159__boxed_3864_; lean_object* v_res_3865_; 
v___x_28156__boxed_3863_ = lean_unbox(v___x_3855_);
v___x_28159__boxed_3864_ = lean_unbox(v___x_3858_);
v_res_3865_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_3853_, v_path_3854_, v___x_28156__boxed_3863_, v_descr_3856_, v_url_3857_, v___x_28159__boxed_3864_, v_00___3859_, v___y_3860_, v___y_3861_);
lean_dec_ref(v___y_3861_);
lean_dec_ref(v_url_3857_);
lean_dec_ref(v_descr_3856_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(lean_object* v_a_3872_, lean_object* v_cfg_3873_, lean_object* v_h_3874_, lean_object* v_hOut_3875_, lean_object* v_s_3876_){
_start:
{
lean_object* v___y_3879_; lean_object* v___x_3891_; 
v___x_3891_ = lean_io_prim_handle_get_line(v_h_3874_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3990_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3990_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3990_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v_startInclusive_3904_; lean_object* v_endExclusive_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3900_ = lean_unsigned_to_nat(0u);
v___x_3901_ = lean_string_utf8_byte_size(v_a_3892_);
lean_inc(v_a_3892_);
v___x_3902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3902_, 0, v_a_3892_);
lean_ctor_set(v___x_3902_, 1, v___x_3900_);
lean_ctor_set(v___x_3902_, 2, v___x_3901_);
v___x_3903_ = l_String_Slice_trimAscii(v___x_3902_);
v_startInclusive_3904_ = lean_ctor_get(v___x_3903_, 1);
lean_inc(v_startInclusive_3904_);
v_endExclusive_3905_ = lean_ctor_get(v___x_3903_, 2);
lean_inc(v_endExclusive_3905_);
v___x_3906_ = lean_nat_sub(v_endExclusive_3905_, v_startInclusive_3904_);
lean_dec(v_startInclusive_3904_);
lean_dec(v_endExclusive_3905_);
v___x_3907_ = lean_nat_dec_eq(v___x_3906_, v___x_3900_);
lean_dec(v___x_3906_);
if (v___x_3907_ == 0)
{
uint8_t v___x_3908_; lean_object* v___y_3910_; lean_object* v_a_3928_; lean_object* v___x_3947_; 
lean_del_object(v___x_3894_);
v___x_3908_ = 1;
lean_inc(v_a_3892_);
v___x_3947_ = l_Lean_Json_parse(v_a_3892_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; 
lean_dec(v_a_3892_);
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref(v___x_3947_);
v_a_3928_ = v_a_3948_;
goto v___jp_3927_;
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3950_; 
v_a_3949_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3949_);
lean_dec_ref(v___x_3947_);
v___x_3950_ = l_Lean_Json_getObj_x3f(v_a_3949_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; 
lean_dec(v_a_3892_);
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref(v___x_3950_);
v_a_3928_ = v_a_3951_;
goto v___jp_3927_;
}
else
{
lean_object* v_a_3952_; lean_object* v___x_3953_; 
v_a_3952_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3952_);
lean_dec_ref(v___x_3950_);
v___x_3953_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_3873_, v_a_3952_);
if (lean_obj_tag(v___x_3953_) == 1)
{
lean_object* v_val_3954_; lean_object* v_url_3955_; lean_object* v_path_3956_; lean_object* v_descr_3957_; lean_object* v___x_3958_; lean_object* v___f_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_dec_ref(v___x_3903_);
v_val_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc_n(v_val_3954_, 2);
lean_dec_ref(v___x_3953_);
v_url_3955_ = lean_ctor_get(v_val_3954_, 0);
v_path_3956_ = lean_ctor_get(v_val_3954_, 1);
v_descr_3957_ = lean_ctor_get(v_val_3954_, 2);
v___x_3958_ = lean_box(v___x_3908_);
lean_inc(v_a_3892_);
lean_inc(v_a_3952_);
lean_inc(v_hOut_3875_);
lean_inc_ref(v_cfg_3873_);
v___f_3959_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0___boxed), 10, 6);
lean_closure_set(v___f_3959_, 0, v_cfg_3873_);
lean_closure_set(v___f_3959_, 1, v_hOut_3875_);
lean_closure_set(v___f_3959_, 2, v_val_3954_);
lean_closure_set(v___f_3959_, 3, v_a_3952_);
lean_closure_set(v___f_3959_, 4, v_a_3892_);
lean_closure_set(v___f_3959_, 5, v___x_3958_);
v___x_3960_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_3961_ = l_Lake_JsonObject_getJson_x3f(v_a_3952_, v___x_3960_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v___x_3962_; 
lean_dec(v_val_3954_);
lean_dec(v_a_3952_);
lean_dec(v_a_3892_);
v___x_3962_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___y_3897_ = v___f_3959_;
v___y_3898_ = v___x_3962_;
goto v___jp_3896_;
}
else
{
lean_object* v_val_3963_; lean_object* v___x_3964_; 
v_val_3963_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_val_3963_);
lean_dec_ref(v___x_3961_);
v___x_3964_ = l_Lean_Json_getNat_x3f(v_val_3963_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v_val_3954_);
lean_dec(v_a_3952_);
lean_dec(v_a_3892_);
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3967_ = v___x_3964_;
v_isShared_3968_ = v_isSharedCheck_3974_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3964_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3974_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3972_; 
v___x_3969_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_3970_ = lean_string_append(v___x_3969_, v_a_3965_);
lean_dec(v_a_3965_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_3970_);
v___x_3972_ = v___x_3967_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
v___y_3897_ = v___f_3959_;
v___y_3898_ = v___x_3972_;
goto v___jp_3896_;
}
}
}
else
{
if (lean_obj_tag(v___x_3964_) == 1)
{
lean_object* v_a_3975_; lean_object* v___x_3976_; uint8_t v___x_3977_; 
lean_dec_ref(v___f_3959_);
v_a_3975_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3975_);
v___x_3976_ = lean_unsigned_to_nat(200u);
v___x_3977_ = lean_nat_dec_eq(v_a_3975_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3978_ = lean_unsigned_to_nat(201u);
v___x_3979_ = lean_nat_dec_eq(v_a_3975_, v___x_3978_);
lean_dec(v_a_3975_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; 
lean_inc_ref(v_cfg_3873_);
v___x_3980_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_3873_, v_hOut_3875_, v_val_3954_, v_a_3952_, v_a_3892_, v___x_3908_, v___x_3964_, v_s_3876_, v_a_3872_);
lean_dec(v_a_3952_);
lean_dec(v_val_3954_);
v___y_3879_ = v___x_3980_;
goto v___jp_3878_;
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_inc_ref(v_descr_3957_);
lean_inc_ref(v_path_3956_);
lean_inc_ref(v_url_3955_);
lean_dec_ref(v___x_3964_);
lean_dec(v_val_3954_);
lean_dec(v_a_3952_);
lean_dec(v_a_3892_);
v___x_3981_ = lean_box(0);
lean_inc_ref(v_cfg_3873_);
v___x_3982_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_3873_, v_path_3956_, v___x_3908_, v_descr_3957_, v_url_3955_, v___x_3907_, v___x_3981_, v_s_3876_, v_a_3872_);
lean_dec_ref(v_url_3955_);
lean_dec_ref(v_descr_3957_);
v___y_3879_ = v___x_3982_;
goto v___jp_3878_;
}
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_inc_ref(v_descr_3957_);
lean_inc_ref(v_path_3956_);
lean_inc_ref(v_url_3955_);
lean_dec(v_a_3975_);
lean_dec_ref(v___x_3964_);
lean_dec(v_val_3954_);
lean_dec(v_a_3952_);
lean_dec(v_a_3892_);
v___x_3983_ = lean_box(0);
lean_inc_ref(v_cfg_3873_);
v___x_3984_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_3873_, v_path_3956_, v___x_3908_, v_descr_3957_, v_url_3955_, v___x_3907_, v___x_3983_, v_s_3876_, v_a_3872_);
lean_dec_ref(v_url_3955_);
lean_dec_ref(v_descr_3957_);
v___y_3879_ = v___x_3984_;
goto v___jp_3878_;
}
}
else
{
lean_dec(v_val_3954_);
lean_dec(v_a_3952_);
lean_dec(v_a_3892_);
v___y_3897_ = v___f_3959_;
v___y_3898_ = v___x_3964_;
goto v___jp_3896_;
}
}
}
}
else
{
lean_object* v_scope_3985_; lean_object* v_s_3986_; 
lean_dec(v___x_3953_);
lean_dec(v_a_3952_);
lean_dec(v_a_3892_);
v_scope_3985_ = lean_ctor_get(v_cfg_3873_, 0);
v_s_3986_ = lean_ctor_get(v_scope_3985_, 0);
lean_inc_ref(v_s_3986_);
v___y_3910_ = v_s_3986_;
goto v___jp_3909_;
}
}
}
v___jp_3909_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v_numSuccesses_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3926_; 
v___x_3911_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_3912_ = lean_string_append(v___y_3910_, v___x_3911_);
v___x_3913_ = l_String_Slice_toString(v___x_3903_);
lean_dec_ref(v___x_3903_);
v___x_3914_ = lean_string_append(v___x_3912_, v___x_3913_);
lean_dec_ref(v___x_3913_);
v___x_3915_ = 3;
v___x_3916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3916_, 0, v___x_3914_);
lean_ctor_set_uint8(v___x_3916_, sizeof(void*)*1, v___x_3915_);
lean_inc_ref(v_a_3872_);
v___x_3917_ = lean_apply_2(v_a_3872_, v___x_3916_, lean_box(0));
v_numSuccesses_3918_ = lean_ctor_get(v_s_3876_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_s_3876_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3920_ = v_s_3876_;
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_numSuccesses_3918_);
lean_dec(v_s_3876_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_numSuccesses_3918_);
v___x_3923_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_ctor_set_uint8(v___x_3923_, sizeof(void*)*1, v___x_3908_);
v_s_3876_ = v___x_3923_;
goto _start;
}
}
}
v___jp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v_numSuccesses_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3946_; 
v___x_3929_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_3930_ = lean_string_append(v___x_3929_, v_a_3928_);
lean_dec_ref(v_a_3928_);
v___x_3931_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_3932_ = lean_string_append(v___x_3930_, v___x_3931_);
v___x_3933_ = l_String_Slice_toString(v___x_3903_);
lean_dec_ref(v___x_3903_);
v___x_3934_ = lean_string_append(v___x_3932_, v___x_3933_);
lean_dec_ref(v___x_3933_);
v___x_3935_ = 3;
v___x_3936_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*1, v___x_3935_);
lean_inc_ref(v_a_3872_);
v___x_3937_ = lean_apply_2(v_a_3872_, v___x_3936_, lean_box(0));
v_numSuccesses_3938_ = lean_ctor_get(v_s_3876_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v_s_3876_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3940_ = v_s_3876_;
v_isShared_3941_ = v_isSharedCheck_3946_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_numSuccesses_3938_);
lean_dec(v_s_3876_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3946_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_numSuccesses_3938_);
v___x_3943_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*1, v___x_3908_);
v_s_3876_ = v___x_3943_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_3988_; 
lean_dec_ref(v___x_3903_);
lean_dec(v_a_3892_);
lean_dec(v_hOut_3875_);
lean_dec_ref(v_cfg_3873_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v_s_3876_);
v___x_3988_ = v___x_3894_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_s_3876_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
v___jp_3896_:
{
lean_object* v___x_3899_; 
lean_inc_ref(v_a_3872_);
v___x_3899_ = lean_apply_4(v___y_3897_, v___y_3898_, v_s_3876_, v_a_3872_, lean_box(0));
v___y_3879_ = v___x_3899_;
goto v___jp_3878_;
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4003_; 
lean_dec_ref(v_s_3876_);
lean_dec(v_hOut_3875_);
lean_dec_ref(v_cfg_3873_);
v_a_3991_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3993_ = v___x_3891_;
v_isShared_3994_ = v_isSharedCheck_4003_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3891_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4003_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3995_; uint8_t v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3995_ = lean_io_error_to_string(v_a_3991_);
v___x_3996_ = 3;
v___x_3997_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3997_, 0, v___x_3995_);
lean_ctor_set_uint8(v___x_3997_, sizeof(void*)*1, v___x_3996_);
lean_inc_ref(v_a_3872_);
v___x_3998_ = lean_apply_2(v_a_3872_, v___x_3997_, lean_box(0));
v___x_3999_ = lean_box(0);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_3999_);
v___x_4001_ = v___x_3993_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
v___jp_3878_:
{
if (lean_obj_tag(v___y_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v_snd_3881_; 
v_a_3880_ = lean_ctor_get(v___y_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref(v___y_3879_);
v_snd_3881_ = lean_ctor_get(v_a_3880_, 1);
lean_inc(v_snd_3881_);
lean_dec(v_a_3880_);
v_s_3876_ = v_snd_3881_;
goto _start;
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec(v_hOut_3875_);
lean_dec_ref(v_cfg_3873_);
v_a_3883_ = lean_ctor_get(v___y_3879_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___y_3879_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___y_3879_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___y_3879_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___boxed(lean_object* v_a_4004_, lean_object* v_cfg_4005_, lean_object* v_h_4006_, lean_object* v_hOut_4007_, lean_object* v_s_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4004_, v_cfg_4005_, v_h_4006_, v_hOut_4007_, v_s_4008_);
lean_dec(v_h_4006_);
lean_dec_ref(v_a_4004_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(lean_object* v_cfg_4011_, lean_object* v_h_4012_, lean_object* v_hOut_4013_, lean_object* v_s_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v___y_4018_; lean_object* v___x_4030_; 
v___x_4030_ = lean_io_prim_handle_get_line(v_h_4012_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4126_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4033_ = v___x_4030_;
v_isShared_4034_ = v_isSharedCheck_4126_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4030_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4126_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v_startInclusive_4039_; lean_object* v_endExclusive_4040_; lean_object* v___x_4041_; uint8_t v___x_4042_; 
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = lean_string_utf8_byte_size(v_a_4031_);
lean_inc(v_a_4031_);
v___x_4037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4037_, 0, v_a_4031_);
lean_ctor_set(v___x_4037_, 1, v___x_4035_);
lean_ctor_set(v___x_4037_, 2, v___x_4036_);
v___x_4038_ = l_String_Slice_trimAscii(v___x_4037_);
v_startInclusive_4039_ = lean_ctor_get(v___x_4038_, 1);
lean_inc(v_startInclusive_4039_);
v_endExclusive_4040_ = lean_ctor_get(v___x_4038_, 2);
lean_inc(v_endExclusive_4040_);
v___x_4041_ = lean_nat_sub(v_endExclusive_4040_, v_startInclusive_4039_);
lean_dec(v_startInclusive_4039_);
lean_dec(v_endExclusive_4040_);
v___x_4042_ = lean_nat_dec_eq(v___x_4041_, v___x_4035_);
lean_dec(v___x_4041_);
if (v___x_4042_ == 0)
{
uint8_t v___x_4043_; lean_object* v___y_4045_; lean_object* v_a_4063_; lean_object* v___x_4082_; 
lean_del_object(v___x_4033_);
v___x_4043_ = 1;
lean_inc(v_a_4031_);
v___x_4082_ = l_Lean_Json_parse(v_a_4031_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; 
lean_dec(v_a_4031_);
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref(v___x_4082_);
v_a_4063_ = v_a_4083_;
goto v___jp_4062_;
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4085_; 
v_a_4084_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4084_);
lean_dec_ref(v___x_4082_);
v___x_4085_ = l_Lean_Json_getObj_x3f(v_a_4084_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v_a_4086_; 
lean_dec(v_a_4031_);
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref(v___x_4085_);
v_a_4063_ = v_a_4086_;
goto v___jp_4062_;
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4088_; 
v_a_4087_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_a_4087_);
lean_dec_ref(v___x_4085_);
v___x_4088_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_getInfo_x3f(v_cfg_4011_, v_a_4087_);
if (lean_obj_tag(v___x_4088_) == 1)
{
lean_object* v_val_4089_; lean_object* v_url_4090_; lean_object* v_path_4091_; lean_object* v_descr_4092_; lean_object* v___y_4094_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
lean_dec_ref(v___x_4038_);
v_val_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_val_4089_);
lean_dec_ref(v___x_4088_);
v_url_4090_ = lean_ctor_get(v_val_4089_, 0);
v_path_4091_ = lean_ctor_get(v_val_4089_, 1);
v_descr_4092_ = lean_ctor_get(v_val_4089_, 2);
v___x_4096_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_4097_ = l_Lake_JsonObject_getJson_x3f(v_a_4087_, v___x_4096_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v___x_4098_; 
v___x_4098_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__4));
v___y_4094_ = v___x_4098_;
goto v___jp_4093_;
}
else
{
lean_object* v_val_4099_; lean_object* v___x_4100_; 
v_val_4099_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_val_4099_);
lean_dec_ref(v___x_4097_);
v___x_4100_ = l_Lean_Json_getNat_x3f(v_val_4099_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4110_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4110_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4110_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
v___x_4105_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__6));
v___x_4106_ = lean_string_append(v___x_4105_, v_a_4101_);
lean_dec(v_a_4101_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4106_);
v___x_4108_ = v___x_4103_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
v___y_4094_ = v___x_4108_;
goto v___jp_4093_;
}
}
}
else
{
if (lean_obj_tag(v___x_4100_) == 1)
{
lean_object* v_a_4111_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
v_a_4111_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4111_);
v___x_4112_ = lean_unsigned_to_nat(200u);
v___x_4113_ = lean_nat_dec_eq(v_a_4111_, v___x_4112_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; uint8_t v___x_4115_; 
v___x_4114_ = lean_unsigned_to_nat(201u);
v___x_4115_ = lean_nat_dec_eq(v_a_4111_, v___x_4114_);
lean_dec(v_a_4111_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; 
lean_inc_ref(v_cfg_4011_);
v___x_4116_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4011_, v_hOut_4013_, v_val_4089_, v_a_4087_, v_a_4031_, v___x_4043_, v___x_4100_, v_s_4014_, v_a_4015_);
lean_dec(v_a_4087_);
lean_dec(v_val_4089_);
v___y_4018_ = v___x_4116_;
goto v___jp_4017_;
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_inc_ref(v_descr_4092_);
lean_inc_ref(v_path_4091_);
lean_inc_ref(v_url_4090_);
lean_dec_ref(v___x_4100_);
lean_dec(v_val_4089_);
lean_dec(v_a_4087_);
lean_dec(v_a_4031_);
v___x_4117_ = lean_box(0);
lean_inc_ref(v_cfg_4011_);
v___x_4118_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4011_, v_path_4091_, v___x_4043_, v_descr_4092_, v_url_4090_, v___x_4042_, v___x_4117_, v_s_4014_, v_a_4015_);
lean_dec_ref(v_url_4090_);
lean_dec_ref(v_descr_4092_);
v___y_4018_ = v___x_4118_;
goto v___jp_4017_;
}
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
lean_inc_ref(v_descr_4092_);
lean_inc_ref(v_path_4091_);
lean_inc_ref(v_url_4090_);
lean_dec(v_a_4111_);
lean_dec_ref(v___x_4100_);
lean_dec(v_val_4089_);
lean_dec(v_a_4087_);
lean_dec(v_a_4031_);
v___x_4119_ = lean_box(0);
lean_inc_ref(v_cfg_4011_);
v___x_4120_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__1(v_cfg_4011_, v_path_4091_, v___x_4043_, v_descr_4092_, v_url_4090_, v___x_4042_, v___x_4119_, v_s_4014_, v_a_4015_);
lean_dec_ref(v_url_4090_);
lean_dec_ref(v_descr_4092_);
v___y_4018_ = v___x_4120_;
goto v___jp_4017_;
}
}
else
{
v___y_4094_ = v___x_4100_;
goto v___jp_4093_;
}
}
}
v___jp_4093_:
{
lean_object* v___x_4095_; 
lean_inc_ref(v_cfg_4011_);
v___x_4095_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___lam__0(v_cfg_4011_, v_hOut_4013_, v_val_4089_, v_a_4087_, v_a_4031_, v___x_4043_, v___y_4094_, v_s_4014_, v_a_4015_);
lean_dec(v_a_4087_);
lean_dec(v_val_4089_);
v___y_4018_ = v___x_4095_;
goto v___jp_4017_;
}
}
else
{
lean_object* v_scope_4121_; lean_object* v_s_4122_; 
lean_dec(v___x_4088_);
lean_dec(v_a_4087_);
lean_dec(v_a_4031_);
v_scope_4121_ = lean_ctor_get(v_cfg_4011_, 0);
v_s_4122_ = lean_ctor_get(v_scope_4121_, 0);
lean_inc_ref(v_s_4122_);
v___y_4045_ = v_s_4122_;
goto v___jp_4044_;
}
}
}
v___jp_4044_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v_numSuccesses_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4061_; 
v___x_4046_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__0));
v___x_4047_ = lean_string_append(v___y_4045_, v___x_4046_);
v___x_4048_ = l_String_Slice_toString(v___x_4038_);
lean_dec_ref(v___x_4038_);
v___x_4049_ = lean_string_append(v___x_4047_, v___x_4048_);
lean_dec_ref(v___x_4048_);
v___x_4050_ = 3;
v___x_4051_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4051_, 0, v___x_4049_);
lean_ctor_set_uint8(v___x_4051_, sizeof(void*)*1, v___x_4050_);
lean_inc_ref(v_a_4015_);
v___x_4052_ = lean_apply_2(v_a_4015_, v___x_4051_, lean_box(0));
v_numSuccesses_4053_ = lean_ctor_get(v_s_4014_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_s_4014_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4055_ = v_s_4014_;
v_isShared_4056_ = v_isSharedCheck_4061_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_numSuccesses_4053_);
lean_dec(v_s_4014_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4061_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_numSuccesses_4053_);
v___x_4058_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4059_; 
lean_ctor_set_uint8(v___x_4058_, sizeof(void*)*1, v___x_4043_);
v___x_4059_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4015_, v_cfg_4011_, v_h_4012_, v_hOut_4013_, v___x_4058_);
return v___x_4059_;
}
}
}
v___jp_4062_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v_numSuccesses_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4081_; 
v___x_4064_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__1));
v___x_4065_ = lean_string_append(v___x_4064_, v_a_4063_);
lean_dec_ref(v_a_4063_);
v___x_4066_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_4067_ = lean_string_append(v___x_4065_, v___x_4066_);
v___x_4068_ = l_String_Slice_toString(v___x_4038_);
lean_dec_ref(v___x_4038_);
v___x_4069_ = lean_string_append(v___x_4067_, v___x_4068_);
lean_dec_ref(v___x_4068_);
v___x_4070_ = 3;
v___x_4071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4071_, 0, v___x_4069_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*1, v___x_4070_);
lean_inc_ref(v_a_4015_);
v___x_4072_ = lean_apply_2(v_a_4015_, v___x_4071_, lean_box(0));
v_numSuccesses_4073_ = lean_ctor_get(v_s_4014_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_s_4014_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4075_ = v_s_4014_;
v_isShared_4076_ = v_isSharedCheck_4081_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_numSuccesses_4073_);
lean_dec(v_s_4014_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4081_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_numSuccesses_4073_);
v___x_4078_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4079_; 
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*1, v___x_4043_);
v___x_4079_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4015_, v_cfg_4011_, v_h_4012_, v_hOut_4013_, v___x_4078_);
return v___x_4079_;
}
}
}
}
else
{
lean_object* v___x_4124_; 
lean_dec_ref(v___x_4038_);
lean_dec(v_a_4031_);
lean_dec(v_hOut_4013_);
lean_dec_ref(v_cfg_4011_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v_s_4014_);
v___x_4124_ = v___x_4033_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_s_4014_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4139_; 
lean_dec_ref(v_s_4014_);
lean_dec(v_hOut_4013_);
lean_dec_ref(v_cfg_4011_);
v_a_4127_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4129_ = v___x_4030_;
v_isShared_4130_ = v_isSharedCheck_4139_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4030_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4139_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4131_; uint8_t v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
v___x_4131_ = lean_io_error_to_string(v_a_4127_);
v___x_4132_ = 3;
v___x_4133_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4133_, 0, v___x_4131_);
lean_ctor_set_uint8(v___x_4133_, sizeof(void*)*1, v___x_4132_);
lean_inc_ref(v_a_4015_);
v___x_4134_ = lean_apply_2(v_a_4015_, v___x_4133_, lean_box(0));
v___x_4135_ = lean_box(0);
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 0, v___x_4135_);
v___x_4137_ = v___x_4129_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
v___jp_4017_:
{
if (lean_obj_tag(v___y_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v_snd_4020_; lean_object* v___x_4021_; 
v_a_4019_ = lean_ctor_get(v___y_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref(v___y_4018_);
v_snd_4020_ = lean_ctor_get(v_a_4019_, 1);
lean_inc(v_snd_4020_);
lean_dec(v_a_4019_);
v___x_4021_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0(v_a_4015_, v_cfg_4011_, v_h_4012_, v_hOut_4013_, v_snd_4020_);
return v___x_4021_;
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec(v_hOut_4013_);
lean_dec_ref(v_cfg_4011_);
v_a_4022_ = lean_ctor_get(v___y_4018_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___y_4018_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___y_4018_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___y_4018_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___boxed(lean_object* v_cfg_4140_, lean_object* v_h_4141_, lean_object* v_hOut_4142_, lean_object* v_s_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4140_, v_h_4141_, v_hOut_4142_, v_s_4143_, v_a_4144_);
lean_dec_ref(v_a_4144_);
lean_dec(v_h_4141_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(lean_object* v_snd_4147_, lean_object* v___y_4148_, lean_object* v_a_x3f_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = lean_io_remove_file(v_snd_4147_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4172_; 
v_a_4160_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4162_ = v___x_4151_;
v_isShared_4163_ = v_isSharedCheck_4172_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4151_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4172_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; uint8_t v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4164_ = lean_io_error_to_string(v_a_4160_);
v___x_4165_ = 3;
v___x_4166_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4166_, 0, v___x_4164_);
lean_ctor_set_uint8(v___x_4166_, sizeof(void*)*1, v___x_4165_);
lean_inc_ref(v___y_4148_);
v___x_4167_ = lean_apply_2(v___y_4148_, v___x_4166_, lean_box(0));
v___x_4168_ = lean_box(0);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v___x_4168_);
v___x_4170_ = v___x_4162_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0___boxed(lean_object* v_snd_4173_, lean_object* v___y_4174_, lean_object* v_a_x3f_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4173_, v___y_4174_, v_a_x3f_4175_);
lean_dec(v_a_x3f_4175_);
lean_dec_ref(v___y_4174_);
lean_dec_ref(v_snd_4173_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(lean_object* v_f_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v___x_4181_; 
v___x_4181_ = lean_io_create_tempfile();
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v_fst_4183_; lean_object* v_snd_4184_; lean_object* v_r_4185_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref(v___x_4181_);
v_fst_4183_ = lean_ctor_get(v_a_4182_, 0);
lean_inc(v_fst_4183_);
v_snd_4184_ = lean_ctor_get(v_a_4182_, 1);
lean_inc_n(v_snd_4184_, 2);
lean_dec(v_a_4182_);
lean_inc_ref(v___y_4179_);
v_r_4185_ = lean_apply_4(v_f_4178_, v_fst_4183_, v_snd_4184_, v___y_4179_, lean_box(0));
if (lean_obj_tag(v_r_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4210_; 
v_a_4186_ = lean_ctor_get(v_r_4185_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v_r_4185_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4188_ = v_r_4185_;
v_isShared_4189_ = v_isSharedCheck_4210_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v_r_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4210_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
lean_inc(v_a_4186_);
if (v_isShared_4189_ == 0)
{
lean_ctor_set_tag(v___x_4188_, 1);
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4184_, v___y_4179_, v___x_4191_);
lean_dec_ref(v___x_4191_);
lean_dec(v_snd_4184_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4199_ == 0)
{
lean_object* v_unused_4200_; 
v_unused_4200_ = lean_ctor_get(v___x_4192_, 0);
lean_dec(v_unused_4200_);
v___x_4194_ = v___x_4192_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_dec(v___x_4192_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v_a_4186_);
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4186_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_dec(v_a_4186_);
v_a_4201_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4192_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4192_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_a_4211_ = lean_ctor_get(v_r_4185_, 0);
lean_inc(v_a_4211_);
lean_dec_ref(v_r_4185_);
v___x_4212_ = lean_box(0);
v___x_4213_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___lam__0(v_snd_4184_, v___y_4179_, v___x_4212_);
lean_dec(v_snd_4184_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4220_ == 0)
{
lean_object* v_unused_4221_; 
v_unused_4221_ = lean_ctor_get(v___x_4213_, 0);
lean_dec(v_unused_4221_);
v___x_4215_ = v___x_4213_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_dec(v___x_4213_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
lean_ctor_set_tag(v___x_4215_, 1);
lean_ctor_set(v___x_4215_, 0, v_a_4211_);
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4211_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec(v_a_4211_);
v_a_4222_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4213_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4213_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v_f_4178_);
v_a_4230_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4232_ = v___x_4181_;
v_isShared_4233_ = v_isSharedCheck_4242_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4181_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4242_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4234_; uint8_t v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4234_ = lean_io_error_to_string(v_a_4230_);
v___x_4235_ = 3;
v___x_4236_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4236_, 0, v___x_4234_);
lean_ctor_set_uint8(v___x_4236_, sizeof(void*)*1, v___x_4235_);
lean_inc_ref(v___y_4179_);
v___x_4237_ = lean_apply_2(v___y_4179_, v___x_4236_, lean_box(0));
v___x_4238_ = lean_box(0);
if (v_isShared_4233_ == 0)
{
lean_ctor_set(v___x_4232_, 0, v___x_4238_);
v___x_4240_ = v___x_4232_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg___boxed(lean_object* v_f_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4243_, v___y_4244_);
lean_dec_ref(v___y_4244_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(lean_object* v_00_u03b1_4247_, lean_object* v_f_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v_f_4248_, v___y_4249_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___boxed(lean_object* v_00_u03b1_4252_, lean_object* v_f_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2(v_00_u03b1_4252_, v_f_4253_, v___y_4254_);
lean_dec_ref(v___y_4254_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(lean_object* v_h_4259_, lean_object* v_as_4260_, size_t v_i_4261_, size_t v_stop_4262_, lean_object* v_b_4263_, lean_object* v___y_4264_){
_start:
{
uint8_t v___x_4266_; 
v___x_4266_ = lean_usize_dec_eq(v_i_4261_, v_stop_4262_);
if (v___x_4266_ == 0)
{
lean_object* v___x_4267_; lean_object* v_url_4268_; lean_object* v_path_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4267_ = lean_array_uget_borrowed(v_as_4260_, v_i_4261_);
v_url_4268_ = lean_ctor_get(v___x_4267_, 0);
v_path_4269_ = lean_ctor_get(v___x_4267_, 1);
v___x_4270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
lean_inc_ref(v_url_4268_);
v___x_4271_ = l_String_quote(v_url_4268_);
v___x_4272_ = lean_string_append(v___x_4270_, v___x_4271_);
lean_dec_ref(v___x_4271_);
v___x_4273_ = l_IO_FS_Handle_putStrLn(v_h_4259_, v___x_4272_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
lean_dec_ref(v___x_4273_);
v___x_4274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__1));
lean_inc_ref(v_path_4269_);
v___x_4275_ = l_String_quote(v_path_4269_);
v___x_4276_ = lean_string_append(v___x_4274_, v___x_4275_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = l_IO_FS_Handle_putStrLn(v_h_4259_, v___x_4276_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; size_t v___x_4279_; size_t v___x_4280_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref(v___x_4277_);
v___x_4279_ = ((size_t)1ULL);
v___x_4280_ = lean_usize_add(v_i_4261_, v___x_4279_);
v_i_4261_ = v___x_4280_;
v_b_4263_ = v_a_4278_;
goto _start;
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4294_; 
v_a_4282_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4284_ = v___x_4277_;
v_isShared_4285_ = v_isSharedCheck_4294_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4277_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4294_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4292_; 
v___x_4286_ = lean_io_error_to_string(v_a_4282_);
v___x_4287_ = 3;
v___x_4288_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4288_, 0, v___x_4286_);
lean_ctor_set_uint8(v___x_4288_, sizeof(void*)*1, v___x_4287_);
lean_inc_ref(v___y_4264_);
v___x_4289_ = lean_apply_2(v___y_4264_, v___x_4288_, lean_box(0));
v___x_4290_ = lean_box(0);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 0, v___x_4290_);
v___x_4292_ = v___x_4284_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4307_; 
v_a_4295_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4297_ = v___x_4273_;
v_isShared_4298_ = v_isSharedCheck_4307_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4273_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4307_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; uint8_t v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4305_; 
v___x_4299_ = lean_io_error_to_string(v_a_4295_);
v___x_4300_ = 3;
v___x_4301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set_uint8(v___x_4301_, sizeof(void*)*1, v___x_4300_);
lean_inc_ref(v___y_4264_);
v___x_4302_ = lean_apply_2(v___y_4264_, v___x_4301_, lean_box(0));
v___x_4303_ = lean_box(0);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4303_);
v___x_4305_ = v___x_4297_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4303_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
else
{
lean_object* v___x_4308_; 
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v_b_4263_);
return v___x_4308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___boxed(lean_object* v_h_4309_, lean_object* v_as_4310_, lean_object* v_i_4311_, lean_object* v_stop_4312_, lean_object* v_b_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
size_t v_i_boxed_4316_; size_t v_stop_boxed_4317_; lean_object* v_res_4318_; 
v_i_boxed_4316_ = lean_unbox_usize(v_i_4311_);
lean_dec(v_i_4311_);
v_stop_boxed_4317_ = lean_unbox_usize(v_stop_4312_);
lean_dec(v_stop_4312_);
v_res_4318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4309_, v_as_4310_, v_i_boxed_4316_, v_stop_boxed_4317_, v_b_4313_, v___y_4314_);
lean_dec_ref(v___y_4314_);
lean_dec_ref(v_as_4310_);
lean_dec(v_h_4309_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(lean_object* v_h_4320_, lean_object* v_as_4321_, size_t v_i_4322_, size_t v_stop_4323_, lean_object* v_b_4324_, lean_object* v___y_4325_){
_start:
{
uint8_t v___x_4327_; 
v___x_4327_ = lean_usize_dec_eq(v_i_4322_, v_stop_4323_);
if (v___x_4327_ == 0)
{
lean_object* v___x_4328_; lean_object* v_url_4329_; lean_object* v_path_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4328_ = lean_array_uget_borrowed(v_as_4321_, v_i_4322_);
v_url_4329_ = lean_ctor_get(v___x_4328_, 0);
v_path_4330_ = lean_ctor_get(v___x_4328_, 1);
v___x_4331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___closed__0));
lean_inc_ref(v_path_4330_);
v___x_4332_ = l_String_quote(v_path_4330_);
v___x_4333_ = lean_string_append(v___x_4331_, v___x_4332_);
lean_dec_ref(v___x_4332_);
v___x_4334_ = l_IO_FS_Handle_putStrLn(v_h_4320_, v___x_4333_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
lean_dec_ref(v___x_4334_);
v___x_4335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0___closed__0));
lean_inc_ref(v_url_4329_);
v___x_4336_ = l_String_quote(v_url_4329_);
v___x_4337_ = lean_string_append(v___x_4335_, v___x_4336_);
lean_dec_ref(v___x_4336_);
v___x_4338_ = l_IO_FS_Handle_putStrLn(v_h_4320_, v___x_4337_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; size_t v___x_4340_; size_t v___x_4341_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4339_);
lean_dec_ref(v___x_4338_);
v___x_4340_ = ((size_t)1ULL);
v___x_4341_ = lean_usize_add(v_i_4322_, v___x_4340_);
v_i_4322_ = v___x_4341_;
v_b_4324_ = v_a_4339_;
goto _start;
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4355_; 
v_a_4343_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4345_ = v___x_4338_;
v_isShared_4346_ = v_isSharedCheck_4355_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4338_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4355_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4347_; uint8_t v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4353_; 
v___x_4347_ = lean_io_error_to_string(v_a_4343_);
v___x_4348_ = 3;
v___x_4349_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4349_, 0, v___x_4347_);
lean_ctor_set_uint8(v___x_4349_, sizeof(void*)*1, v___x_4348_);
lean_inc_ref(v___y_4325_);
v___x_4350_ = lean_apply_2(v___y_4325_, v___x_4349_, lean_box(0));
v___x_4351_ = lean_box(0);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 0, v___x_4351_);
v___x_4353_ = v___x_4345_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4351_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4368_; 
v_a_4356_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4358_ = v___x_4334_;
v_isShared_4359_ = v_isSharedCheck_4368_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4334_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4368_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4360_; uint8_t v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4366_; 
v___x_4360_ = lean_io_error_to_string(v_a_4356_);
v___x_4361_ = 3;
v___x_4362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set_uint8(v___x_4362_, sizeof(void*)*1, v___x_4361_);
lean_inc_ref(v___y_4325_);
v___x_4363_ = lean_apply_2(v___y_4325_, v___x_4362_, lean_box(0));
v___x_4364_ = lean_box(0);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4364_);
v___x_4366_ = v___x_4358_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4364_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
else
{
lean_object* v___x_4369_; 
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v_b_4324_);
return v___x_4369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1___boxed(lean_object* v_h_4370_, lean_object* v_as_4371_, lean_object* v_i_4372_, lean_object* v_stop_4373_, lean_object* v_b_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
size_t v_i_boxed_4377_; size_t v_stop_boxed_4378_; lean_object* v_res_4379_; 
v_i_boxed_4377_ = lean_unbox_usize(v_i_4372_);
lean_dec(v_i_4372_);
v_stop_boxed_4378_ = lean_unbox_usize(v_stop_4373_);
lean_dec(v_stop_4373_);
v_res_4379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4370_, v_as_4371_, v_i_boxed_4377_, v_stop_boxed_4378_, v_b_4374_, v___y_4375_);
lean_dec_ref(v___y_4375_);
lean_dec_ref(v_as_4371_);
lean_dec(v_h_4370_);
return v_res_4379_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11(void){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4395_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4396_ = lean_unsigned_to_nat(11u);
v___x_4397_ = lean_mk_empty_array_with_capacity(v___x_4396_);
v___x_4398_ = lean_array_push(v___x_4397_, v___x_4395_);
return v___x_4398_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12(void){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4399_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4400_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__11);
v___x_4401_ = lean_array_push(v___x_4400_, v___x_4399_);
return v___x_4401_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4402_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__6));
v___x_4403_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__12);
v___x_4404_ = lean_array_push(v___x_4403_, v___x_4402_);
return v___x_4404_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14(void){
_start:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4405_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4406_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__13);
v___x_4407_ = lean_array_push(v___x_4406_, v___x_4405_);
return v___x_4407_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4408_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4409_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__14);
v___x_4410_ = lean_array_push(v___x_4409_, v___x_4408_);
return v___x_4410_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16(void){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4411_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4412_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__15);
v___x_4413_ = lean_array_push(v___x_4412_, v___x_4411_);
return v___x_4413_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4415_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__16);
v___x_4416_ = lean_array_push(v___x_4415_, v___x_4414_);
return v___x_4416_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4418_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__17);
v___x_4419_ = lean_array_push(v___x_4418_, v___x_4417_);
return v___x_4419_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19(void){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4420_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4421_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__18);
v___x_4422_ = lean_array_push(v___x_4421_, v___x_4420_);
return v___x_4422_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20(void){
_start:
{
lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4423_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4424_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__19);
v___x_4425_ = lean_array_push(v___x_4424_, v___x_4423_);
return v___x_4425_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4427_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__5));
v___x_4428_ = lean_unsigned_to_nat(17u);
v___x_4429_ = lean_mk_empty_array_with_capacity(v___x_4428_);
v___x_4430_ = lean_array_push(v___x_4429_, v___x_4427_);
return v___x_4430_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_4432_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__22);
v___x_4433_ = lean_array_push(v___x_4432_, v___x_4431_);
return v___x_4433_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24(void){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4434_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__17));
v___x_4435_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__23);
v___x_4436_ = lean_array_push(v___x_4435_, v___x_4434_);
return v___x_4436_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25(void){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4437_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_4438_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__24);
v___x_4439_ = lean_array_push(v___x_4438_, v___x_4437_);
return v___x_4439_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26(void){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_4441_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__25);
v___x_4442_ = lean_array_push(v___x_4441_, v___x_4440_);
return v___x_4442_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__21));
v___x_4444_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__26);
v___x_4445_ = lean_array_push(v___x_4444_, v___x_4443_);
return v___x_4445_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28(void){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4446_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_4447_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__27);
v___x_4448_ = lean_array_push(v___x_4447_, v___x_4446_);
return v___x_4448_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29(void){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_4450_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__28);
v___x_4451_ = lean_array_push(v___x_4450_, v___x_4449_);
return v___x_4451_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__13));
v___x_4453_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__29);
v___x_4454_ = lean_array_push(v___x_4453_, v___x_4452_);
return v___x_4454_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31(void){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__14));
v___x_4456_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__30);
v___x_4457_ = lean_array_push(v___x_4456_, v___x_4455_);
return v___x_4457_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32(void){
_start:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4458_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__15));
v___x_4459_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__31);
v___x_4460_ = lean_array_push(v___x_4459_, v___x_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(lean_object* v_cfg_4461_, lean_object* v_h_4462_, lean_object* v_path_4463_, lean_object* v___y_4464_){
_start:
{
uint8_t v___y_4467_; lean_object* v___y_4473_; uint8_t v___y_4474_; uint32_t v___y_4475_; lean_object* v___y_4476_; uint8_t v_kind_4485_; lean_object* v_scope_4486_; lean_object* v_infos_4487_; lean_object* v_key_4488_; uint8_t v___y_4490_; uint32_t v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; uint32_t v___y_4500_; uint8_t v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4515_; uint32_t v___y_4516_; uint8_t v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4524_; lean_object* v___y_4525_; uint8_t v___y_4526_; uint32_t v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4539_; uint32_t v___y_4540_; uint8_t v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v_a_4546_; lean_object* v___y_4640_; lean_object* v___y_4668_; 
v_kind_4485_ = lean_ctor_get_uint8(v_cfg_4461_, sizeof(void*)*3);
v_scope_4486_ = lean_ctor_get(v_cfg_4461_, 0);
lean_inc_ref(v_scope_4486_);
v_infos_4487_ = lean_ctor_get(v_cfg_4461_, 1);
lean_inc_ref(v_infos_4487_);
v_key_4488_ = lean_ctor_get(v_cfg_4461_, 2);
if (v_kind_4485_ == 0)
{
lean_object* v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4669_ = lean_unsigned_to_nat(0u);
v___x_4670_ = lean_array_get_size(v_infos_4487_);
v___x_4671_ = lean_nat_dec_lt(v___x_4669_, v___x_4670_);
if (v___x_4671_ == 0)
{
goto v___jp_4622_;
}
else
{
lean_object* v___x_4672_; uint8_t v___x_4673_; 
v___x_4672_ = lean_box(0);
v___x_4673_ = lean_nat_dec_le(v___x_4670_, v___x_4670_);
if (v___x_4673_ == 0)
{
if (v___x_4671_ == 0)
{
goto v___jp_4622_;
}
else
{
size_t v___x_4674_; size_t v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = ((size_t)0ULL);
v___x_4675_ = lean_usize_of_nat(v___x_4670_);
v___x_4676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4462_, v_infos_4487_, v___x_4674_, v___x_4675_, v___x_4672_, v___y_4464_);
v___y_4640_ = v___x_4676_;
goto v___jp_4639_;
}
}
else
{
size_t v___x_4677_; size_t v___x_4678_; lean_object* v___x_4679_; 
v___x_4677_ = ((size_t)0ULL);
v___x_4678_ = lean_usize_of_nat(v___x_4670_);
v___x_4679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_4462_, v_infos_4487_, v___x_4677_, v___x_4678_, v___x_4672_, v___y_4464_);
v___y_4640_ = v___x_4679_;
goto v___jp_4639_;
}
}
}
else
{
lean_object* v___x_4680_; lean_object* v___x_4681_; uint8_t v___x_4682_; 
v___x_4680_ = lean_unsigned_to_nat(0u);
v___x_4681_ = lean_array_get_size(v_infos_4487_);
v___x_4682_ = lean_nat_dec_lt(v___x_4680_, v___x_4681_);
if (v___x_4682_ == 0)
{
goto v___jp_4641_;
}
else
{
lean_object* v___x_4683_; uint8_t v___x_4684_; 
v___x_4683_ = lean_box(0);
v___x_4684_ = lean_nat_dec_le(v___x_4681_, v___x_4681_);
if (v___x_4684_ == 0)
{
if (v___x_4682_ == 0)
{
goto v___jp_4641_;
}
else
{
size_t v___x_4685_; size_t v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = ((size_t)0ULL);
v___x_4686_ = lean_usize_of_nat(v___x_4681_);
v___x_4687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4462_, v_infos_4487_, v___x_4685_, v___x_4686_, v___x_4683_, v___y_4464_);
v___y_4668_ = v___x_4687_;
goto v___jp_4667_;
}
}
else
{
size_t v___x_4688_; size_t v___x_4689_; lean_object* v___x_4690_; 
v___x_4688_ = ((size_t)0ULL);
v___x_4689_ = lean_usize_of_nat(v___x_4681_);
v___x_4690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_4462_, v_infos_4487_, v___x_4688_, v___x_4689_, v___x_4683_, v___y_4464_);
v___y_4668_ = v___x_4690_;
goto v___jp_4667_;
}
}
}
v___jp_4466_:
{
if (v___y_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = lean_box(0);
v___x_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4468_);
return v___x_4469_;
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = lean_box(0);
v___x_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
v___jp_4472_:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4477_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_4478_ = lean_string_append(v___y_4476_, v___x_4477_);
v___x_4479_ = lean_uint32_to_nat(v___y_4475_);
v___x_4480_ = l_Nat_reprFast(v___x_4479_);
v___x_4481_ = lean_string_append(v___x_4478_, v___x_4480_);
lean_dec_ref(v___x_4480_);
v___x_4482_ = 3;
v___x_4483_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4483_, 0, v___x_4481_);
lean_ctor_set_uint8(v___x_4483_, sizeof(void*)*1, v___x_4482_);
lean_inc_ref(v___y_4473_);
v___x_4484_ = lean_apply_2(v___y_4473_, v___x_4483_, lean_box(0));
v___y_4467_ = v___y_4474_;
goto v___jp_4466_;
}
v___jp_4489_:
{
uint32_t v___x_4493_; uint8_t v___x_4494_; 
v___x_4493_ = 0;
v___x_4494_ = lean_uint32_dec_eq(v___y_4491_, v___x_4493_);
if (v___x_4494_ == 0)
{
lean_object* v_s_4495_; 
v_s_4495_ = lean_ctor_get(v_scope_4486_, 0);
lean_inc_ref(v_s_4495_);
lean_dec_ref(v_scope_4486_);
v___y_4473_ = v___y_4492_;
v___y_4474_ = v___y_4490_;
v___y_4475_ = v___y_4491_;
v___y_4476_ = v_s_4495_;
goto v___jp_4472_;
}
else
{
lean_dec_ref(v_scope_4486_);
v___y_4467_ = v___y_4490_;
goto v___jp_4466_;
}
}
v___jp_4496_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4504_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_4505_ = lean_string_append(v___y_4503_, v___x_4504_);
lean_inc(v___y_4498_);
lean_inc(v___y_4497_);
lean_inc_ref(v___y_4502_);
v___x_4506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4506_, 0, v___y_4502_);
lean_ctor_set(v___x_4506_, 1, v___y_4497_);
lean_ctor_set(v___x_4506_, 2, v___y_4498_);
v___x_4507_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_4506_, v___y_4498_);
lean_dec_ref(v___x_4506_);
v___x_4508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4508_, 0, v___y_4502_);
lean_ctor_set(v___x_4508_, 1, v___y_4497_);
lean_ctor_set(v___x_4508_, 2, v___x_4507_);
v___x_4509_ = l_String_Slice_toString(v___x_4508_);
lean_dec_ref(v___x_4508_);
v___x_4510_ = lean_string_append(v___x_4505_, v___x_4509_);
lean_dec_ref(v___x_4509_);
v___x_4511_ = 2;
v___x_4512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4512_, 0, v___x_4510_);
lean_ctor_set_uint8(v___x_4512_, sizeof(void*)*1, v___x_4511_);
lean_inc_ref(v___y_4499_);
v___x_4513_ = lean_apply_2(v___y_4499_, v___x_4512_, lean_box(0));
v___y_4490_ = v___y_4501_;
v___y_4491_ = v___y_4500_;
v___y_4492_ = v___y_4499_;
goto v___jp_4489_;
}
v___jp_4514_:
{
lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4520_ = lean_string_utf8_byte_size(v___y_4518_);
v___x_4521_ = lean_nat_dec_eq(v___x_4520_, v___y_4515_);
if (v___x_4521_ == 0)
{
lean_object* v_s_4522_; 
v_s_4522_ = lean_ctor_get(v_scope_4486_, 0);
lean_inc_ref(v_s_4522_);
v___y_4497_ = v___y_4515_;
v___y_4498_ = v___x_4520_;
v___y_4499_ = v___y_4519_;
v___y_4500_ = v___y_4516_;
v___y_4501_ = v___y_4517_;
v___y_4502_ = v___y_4518_;
v___y_4503_ = v_s_4522_;
goto v___jp_4496_;
}
else
{
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4515_);
v___y_4490_ = v___y_4517_;
v___y_4491_ = v___y_4516_;
v___y_4492_ = v___y_4519_;
goto v___jp_4489_;
}
}
v___jp_4523_:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4530_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_4531_ = lean_string_append(v___y_4529_, v___x_4530_);
v___x_4532_ = lean_string_append(v___x_4531_, v___y_4525_);
v___x_4533_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_4534_ = lean_string_append(v___x_4532_, v___x_4533_);
v___x_4535_ = 3;
v___x_4536_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4536_, 0, v___x_4534_);
lean_ctor_set_uint8(v___x_4536_, sizeof(void*)*1, v___x_4535_);
lean_inc_ref(v___y_4464_);
v___x_4537_ = lean_apply_2(v___y_4464_, v___x_4536_, lean_box(0));
v___y_4515_ = v___y_4524_;
v___y_4516_ = v___y_4527_;
v___y_4517_ = v___y_4526_;
v___y_4518_ = v___y_4528_;
v___y_4519_ = v___y_4464_;
goto v___jp_4514_;
}
v___jp_4538_:
{
lean_object* v_s_4544_; 
v_s_4544_ = lean_ctor_get(v_scope_4486_, 0);
lean_inc_ref(v_s_4544_);
v___y_4524_ = v___y_4539_;
v___y_4525_ = v___y_4543_;
v___y_4526_ = v___y_4541_;
v___y_4527_ = v___y_4540_;
v___y_4528_ = v___y_4542_;
v___y_4529_ = v_s_4544_;
goto v___jp_4523_;
}
v___jp_4545_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; uint8_t v___x_4552_; uint8_t v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4547_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_4548_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_4549_ = lean_box(0);
v___x_4550_ = lean_unsigned_to_nat(0u);
v___x_4551_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_4552_ = 1;
v___x_4553_ = 0;
v___x_4554_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4554_, 0, v___x_4547_);
lean_ctor_set(v___x_4554_, 1, v___x_4548_);
lean_ctor_set(v___x_4554_, 2, v_a_4546_);
lean_ctor_set(v___x_4554_, 3, v___x_4549_);
lean_ctor_set(v___x_4554_, 4, v___x_4551_);
lean_ctor_set_uint8(v___x_4554_, sizeof(void*)*5, v___x_4552_);
lean_ctor_set_uint8(v___x_4554_, sizeof(void*)*5 + 1, v___x_4553_);
v___x_4555_ = lean_io_process_spawn(v___x_4554_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v_stdout_4557_; lean_object* v_stderr_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref(v___x_4555_);
v_stdout_4557_ = lean_ctor_get(v_a_4556_, 1);
lean_inc_n(v_stdout_4557_, 2);
v_stderr_4558_ = lean_ctor_get(v_a_4556_, 2);
v___x_4559_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
v___x_4560_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_4461_, v_stderr_4558_, v_stdout_4557_, v___x_4559_, v___y_4464_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4562_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref(v___x_4560_);
v___x_4562_ = lean_io_process_child_wait(v___x_4547_, v_a_4556_);
lean_dec(v_a_4556_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; lean_object* v___x_4564_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref(v___x_4562_);
v___x_4564_ = l_IO_FS_Handle_readToEnd(v_stdout_4557_);
lean_dec(v_stdout_4557_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_object* v_a_4565_; uint8_t v_didError_4566_; lean_object* v_numSuccesses_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; 
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
lean_inc(v_a_4565_);
lean_dec_ref(v___x_4564_);
v_didError_4566_ = lean_ctor_get_uint8(v_a_4561_, sizeof(void*)*1);
v_numSuccesses_4567_ = lean_ctor_get(v_a_4561_, 0);
lean_inc(v_numSuccesses_4567_);
lean_dec(v_a_4561_);
v___x_4568_ = lean_array_get_size(v_infos_4487_);
lean_dec_ref(v_infos_4487_);
v___x_4569_ = lean_nat_dec_lt(v_numSuccesses_4567_, v___x_4568_);
lean_dec(v_numSuccesses_4567_);
if (v___x_4569_ == 0)
{
uint32_t v___x_4570_; 
v___x_4570_ = lean_unbox_uint32(v_a_4563_);
lean_dec(v_a_4563_);
v___y_4515_ = v___x_4550_;
v___y_4516_ = v___x_4570_;
v___y_4517_ = v_didError_4566_;
v___y_4518_ = v_a_4565_;
v___y_4519_ = v___y_4464_;
goto v___jp_4514_;
}
else
{
if (v_kind_4485_ == 0)
{
lean_object* v___x_4571_; uint32_t v___x_4572_; 
v___x_4571_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_4572_ = lean_unbox_uint32(v_a_4563_);
lean_dec(v_a_4563_);
v___y_4539_ = v___x_4550_;
v___y_4540_ = v___x_4572_;
v___y_4541_ = v_didError_4566_;
v___y_4542_ = v_a_4565_;
v___y_4543_ = v___x_4571_;
goto v___jp_4538_;
}
else
{
lean_object* v___x_4573_; uint32_t v___x_4574_; 
v___x_4573_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_4574_ = lean_unbox_uint32(v_a_4563_);
lean_dec(v_a_4563_);
v___y_4539_ = v___x_4550_;
v___y_4540_ = v___x_4574_;
v___y_4541_ = v_didError_4566_;
v___y_4542_ = v_a_4565_;
v___y_4543_ = v___x_4573_;
goto v___jp_4538_;
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_a_4563_);
lean_dec(v_a_4561_);
lean_dec_ref(v_infos_4487_);
lean_dec_ref(v_scope_4486_);
v_a_4575_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4577_ = v___x_4564_;
v_isShared_4578_ = v_isSharedCheck_4587_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4564_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4587_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4579_; uint8_t v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4585_; 
v___x_4579_ = lean_io_error_to_string(v_a_4575_);
v___x_4580_ = 3;
v___x_4581_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4581_, 0, v___x_4579_);
lean_ctor_set_uint8(v___x_4581_, sizeof(void*)*1, v___x_4580_);
lean_inc_ref(v___y_4464_);
v___x_4582_ = lean_apply_2(v___y_4464_, v___x_4581_, lean_box(0));
v___x_4583_ = lean_box(0);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 0, v___x_4583_);
v___x_4585_ = v___x_4577_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4583_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4600_; 
lean_dec(v_a_4561_);
lean_dec(v_stdout_4557_);
lean_dec_ref(v_infos_4487_);
lean_dec_ref(v_scope_4486_);
v_a_4588_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4590_ = v___x_4562_;
v_isShared_4591_ = v_isSharedCheck_4600_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4562_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4600_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4592_; uint8_t v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4598_; 
v___x_4592_ = lean_io_error_to_string(v_a_4588_);
v___x_4593_ = 3;
v___x_4594_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4594_, 0, v___x_4592_);
lean_ctor_set_uint8(v___x_4594_, sizeof(void*)*1, v___x_4593_);
lean_inc_ref(v___y_4464_);
v___x_4595_ = lean_apply_2(v___y_4464_, v___x_4594_, lean_box(0));
v___x_4596_ = lean_box(0);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 0, v___x_4596_);
v___x_4598_ = v___x_4590_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec(v_stdout_4557_);
lean_dec(v_a_4556_);
lean_dec_ref(v_infos_4487_);
lean_dec_ref(v_scope_4486_);
v_a_4601_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4560_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4560_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4621_; 
lean_dec_ref(v_infos_4487_);
lean_dec_ref(v_scope_4486_);
lean_dec_ref(v_cfg_4461_);
v_a_4609_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4611_ = v___x_4555_;
v_isShared_4612_ = v_isSharedCheck_4621_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4555_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4621_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; uint8_t v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4619_; 
v___x_4613_ = lean_io_error_to_string(v_a_4609_);
v___x_4614_ = 3;
v___x_4615_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4615_, 0, v___x_4613_);
lean_ctor_set_uint8(v___x_4615_, sizeof(void*)*1, v___x_4614_);
lean_inc_ref(v___y_4464_);
v___x_4616_ = lean_apply_2(v___y_4464_, v___x_4615_, lean_box(0));
v___x_4617_ = lean_box(0);
if (v_isShared_4612_ == 0)
{
lean_ctor_set(v___x_4611_, 0, v___x_4617_);
v___x_4619_ = v___x_4611_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
v___jp_4622_:
{
lean_object* v___x_4623_; 
v___x_4623_ = lean_io_prim_handle_flush(v_h_4462_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
lean_dec_ref(v___x_4623_);
v___x_4624_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_4625_ = lean_array_push(v___x_4624_, v_path_4463_);
v_a_4546_ = v___x_4625_;
goto v___jp_4545_;
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4638_; 
lean_dec_ref(v_infos_4487_);
lean_dec_ref(v_scope_4486_);
lean_dec_ref(v_path_4463_);
lean_dec_ref(v_cfg_4461_);
v_a_4626_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4628_ = v___x_4623_;
v_isShared_4629_ = v_isSharedCheck_4638_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4623_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4638_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; uint8_t v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4636_; 
v___x_4630_ = lean_io_error_to_string(v_a_4626_);
v___x_4631_ = 3;
v___x_4632_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4632_, 0, v___x_4630_);
lean_ctor_set_uint8(v___x_4632_, sizeof(void*)*1, v___x_4631_);
lean_inc_ref(v___y_4464_);
v___x_4633_ = lean_apply_2(v___y_4464_, v___x_4632_, lean_box(0));
v___x_4634_ = lean_box(0);
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 0, v___x_4634_);
v___x_4636_ = v___x_4628_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
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
v___jp_4639_:
{
if (lean_obj_tag(v___y_4640_) == 0)
{
lean_dec_ref(v___y_4640_);
goto v___jp_4622_;
}
else
{
lean_dec_ref(v_infos_4487_);
lean_dec_ref(v_scope_4486_);
lean_dec_ref(v_path_4463_);
lean_dec_ref(v_cfg_4461_);
return v___y_4640_;
}
}
v___jp_4641_:
{
lean_object* v___x_4642_; 
v___x_4642_ = lean_io_prim_handle_flush(v_h_4462_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
lean_dec_ref(v___x_4642_);
v___x_4643_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_4644_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_4645_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_4646_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_4647_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_4488_);
v___x_4648_ = lean_array_push(v___x_4647_, v_key_4488_);
v___x_4649_ = lean_array_push(v___x_4648_, v___x_4643_);
v___x_4650_ = lean_array_push(v___x_4649_, v___x_4644_);
v___x_4651_ = lean_array_push(v___x_4650_, v___x_4645_);
v___x_4652_ = lean_array_push(v___x_4651_, v___x_4646_);
v___x_4653_ = lean_array_push(v___x_4652_, v_path_4463_);
v_a_4546_ = v___x_4653_;
goto v___jp_4545_;
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4666_; 
lean_dec_ref(v_infos_4487_);
lean_dec_ref(v_scope_4486_);
lean_dec_ref(v_path_4463_);
lean_dec_ref(v_cfg_4461_);
v_a_4654_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4656_ = v___x_4642_;
v_isShared_4657_ = v_isSharedCheck_4666_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4642_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4666_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4658_; uint8_t v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4664_; 
v___x_4658_ = lean_io_error_to_string(v_a_4654_);
v___x_4659_ = 3;
v___x_4660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4660_, 0, v___x_4658_);
lean_ctor_set_uint8(v___x_4660_, sizeof(void*)*1, v___x_4659_);
lean_inc_ref(v___y_4464_);
v___x_4661_ = lean_apply_2(v___y_4464_, v___x_4660_, lean_box(0));
v___x_4662_ = lean_box(0);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 0, v___x_4662_);
v___x_4664_ = v___x_4656_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
}
v___jp_4667_:
{
if (lean_obj_tag(v___y_4668_) == 0)
{
lean_dec_ref(v___y_4668_);
goto v___jp_4641_;
}
else
{
lean_dec_ref(v_infos_4487_);
lean_dec_ref(v_scope_4486_);
lean_dec_ref(v_path_4463_);
lean_dec_ref(v_cfg_4461_);
return v___y_4668_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed(lean_object* v_cfg_4691_, lean_object* v_h_4692_, lean_object* v_path_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0(v_cfg_4691_, v_h_4692_, v_path_4693_, v___y_4694_);
lean_dec_ref(v___y_4694_);
lean_dec(v_h_4692_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(lean_object* v_cfg_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v___f_4700_; lean_object* v___x_4701_; 
v___f_4700_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___boxed), 5, 1);
lean_closure_set(v___f_4700_, 0, v_cfg_4697_);
v___x_4701_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_4700_, v_a_4698_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___boxed(lean_object* v_cfg_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts(v_cfg_4702_, v_a_4703_);
lean_dec_ref(v_a_4703_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(lean_object* v_service_4707_, lean_object* v_scope_4708_){
_start:
{
lean_object* v___y_4710_; 
if (lean_obj_tag(v_scope_4708_) == 0)
{
lean_object* v_s_4713_; lean_object* v_apiEndpoint_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_s_4713_ = lean_ctor_get(v_scope_4708_, 0);
lean_inc_ref(v_s_4713_);
lean_dec_ref(v_scope_4708_);
v_apiEndpoint_4714_ = lean_ctor_get(v_service_4707_, 4);
lean_inc_ref(v_apiEndpoint_4714_);
lean_dec_ref(v_service_4707_);
v___x_4715_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_4716_ = lean_string_append(v_apiEndpoint_4714_, v___x_4715_);
v___x_4717_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_4716_, v_s_4713_);
v___y_4710_ = v___x_4717_;
goto v___jp_4709_;
}
else
{
lean_object* v_s_4718_; lean_object* v_apiEndpoint_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v_s_4718_ = lean_ctor_get(v_scope_4708_, 0);
lean_inc_ref(v_s_4718_);
lean_dec_ref(v_scope_4708_);
v_apiEndpoint_4719_ = lean_ctor_get(v_service_4707_, 4);
lean_inc_ref(v_apiEndpoint_4719_);
lean_dec_ref(v_service_4707_);
v___x_4720_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_4721_ = lean_string_append(v_apiEndpoint_4719_, v___x_4720_);
v___x_4722_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_4721_, v_s_4718_);
v___y_4710_ = v___x_4722_;
goto v___jp_4709_;
}
v___jp_4709_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl___closed__0));
v___x_4712_ = lean_string_append(v___y_4710_, v___x_4711_);
return v___x_4712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(size_t v_sz_4723_, size_t v_i_4724_, lean_object* v_bs_4725_){
_start:
{
uint8_t v___x_4726_; 
v___x_4726_ = lean_usize_dec_lt(v_i_4724_, v_sz_4723_);
if (v___x_4726_ == 0)
{
return v_bs_4725_;
}
else
{
lean_object* v_v_4727_; lean_object* v_descr_4728_; uint64_t v_hash_4729_; lean_object* v___x_4730_; lean_object* v_bs_x27_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; size_t v___x_4734_; size_t v___x_4735_; lean_object* v___x_4736_; 
v_v_4727_ = lean_array_uget_borrowed(v_bs_4725_, v_i_4724_);
v_descr_4728_ = lean_ctor_get(v_v_4727_, 2);
v_hash_4729_ = lean_ctor_get_uint64(v_descr_4728_, sizeof(void*)*1);
v___x_4730_ = lean_unsigned_to_nat(0u);
v_bs_x27_4731_ = lean_array_uset(v_bs_4725_, v_i_4724_, v___x_4730_);
v___x_4732_ = l_Lake_lowerHexUInt64(v_hash_4729_);
v___x_4733_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
v___x_4734_ = ((size_t)1ULL);
v___x_4735_ = lean_usize_add(v_i_4724_, v___x_4734_);
v___x_4736_ = lean_array_uset(v_bs_x27_4731_, v_i_4724_, v___x_4733_);
v_i_4724_ = v___x_4735_;
v_bs_4725_ = v___x_4736_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0___boxed(lean_object* v_sz_4738_, lean_object* v_i_4739_, lean_object* v_bs_4740_){
_start:
{
size_t v_sz_boxed_4741_; size_t v_i_boxed_4742_; lean_object* v_res_4743_; 
v_sz_boxed_4741_ = lean_unbox_usize(v_sz_4738_);
lean_dec(v_sz_4738_);
v_i_boxed_4742_ = lean_unbox_usize(v_i_4739_);
lean_dec(v_i_4739_);
v_res_4743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_boxed_4741_, v_i_boxed_4742_, v_bs_4740_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(lean_object* v_a_4744_, lean_object* v_n_4745_, lean_object* v_j_4746_, lean_object* v_a_4747_){
_start:
{
lean_object* v_zero_4748_; uint8_t v_isZero_4749_; 
v_zero_4748_ = lean_unsigned_to_nat(0u);
v_isZero_4749_ = lean_nat_dec_eq(v_j_4746_, v_zero_4748_);
if (v_isZero_4749_ == 1)
{
lean_dec(v_j_4746_);
return v_a_4747_;
}
else
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v_path_4752_; lean_object* v_descr_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4765_; 
v___x_4750_ = lean_nat_sub(v_n_4745_, v_j_4746_);
v___x_4751_ = lean_array_fget(v_a_4747_, v___x_4750_);
v_path_4752_ = lean_ctor_get(v___x_4751_, 1);
v_descr_4753_ = lean_ctor_get(v___x_4751_, 2);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4765_ == 0)
{
lean_object* v_unused_4766_; 
v_unused_4766_ = lean_ctor_get(v___x_4751_, 0);
lean_dec(v_unused_4766_);
v___x_4755_ = v___x_4751_;
v_isShared_4756_ = v_isSharedCheck_4765_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_descr_4753_);
lean_inc(v_path_4752_);
lean_dec(v___x_4751_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4765_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v_one_4757_; lean_object* v_n_4758_; lean_object* v___x_4759_; lean_object* v___x_4761_; 
v_one_4757_ = lean_unsigned_to_nat(1u);
v_n_4758_ = lean_nat_sub(v_j_4746_, v_one_4757_);
lean_dec(v_j_4746_);
v___x_4759_ = lean_array_fget_borrowed(v_a_4744_, v___x_4750_);
lean_inc(v___x_4759_);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 0, v___x_4759_);
v___x_4761_ = v___x_4755_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4759_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_path_4752_);
lean_ctor_set(v_reuseFailAlloc_4764_, 2, v_descr_4753_);
v___x_4761_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4762_; 
v___x_4762_ = lean_array_fset(v_a_4747_, v___x_4750_, v___x_4761_);
lean_dec(v___x_4750_);
v_j_4746_ = v_n_4758_;
v_a_4747_ = v___x_4762_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg___boxed(lean_object* v_a_4767_, lean_object* v_n_4768_, lean_object* v_j_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_4767_, v_n_4768_, v_j_4769_, v_a_4770_);
lean_dec(v_n_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4771_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0(void){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4772_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_4773_ = lean_unsigned_to_nat(2u);
v___x_4774_ = lean_mk_empty_array_with_capacity(v___x_4773_);
v___x_4775_ = lean_array_push(v___x_4774_, v___x_4772_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(lean_object* v_as_4776_, size_t v_i_4777_, size_t v_stop_4778_, lean_object* v_b_4779_){
_start:
{
uint8_t v___x_4780_; 
v___x_4780_ = lean_usize_dec_eq(v_i_4777_, v_stop_4778_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; size_t v___x_4785_; size_t v___x_4786_; 
v___x_4781_ = lean_array_uget_borrowed(v_as_4776_, v_i_4777_);
v___x_4782_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___closed__0);
lean_inc(v___x_4781_);
v___x_4783_ = lean_array_push(v___x_4782_, v___x_4781_);
v___x_4784_ = l_Array_append___redArg(v_b_4779_, v___x_4783_);
lean_dec_ref(v___x_4783_);
v___x_4785_ = ((size_t)1ULL);
v___x_4786_ = lean_usize_add(v_i_4777_, v___x_4785_);
v_i_4777_ = v___x_4786_;
v_b_4779_ = v___x_4784_;
goto _start;
}
else
{
return v_b_4779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3___boxed(lean_object* v_as_4788_, lean_object* v_i_4789_, lean_object* v_stop_4790_, lean_object* v_b_4791_){
_start:
{
size_t v_i_boxed_4792_; size_t v_stop_boxed_4793_; lean_object* v_res_4794_; 
v_i_boxed_4792_ = lean_unbox_usize(v_i_4789_);
lean_dec(v_i_4789_);
v_stop_boxed_4793_ = lean_unbox_usize(v_stop_4790_);
lean_dec(v_stop_4790_);
v_res_4794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v_as_4788_, v_i_boxed_4792_, v_stop_boxed_4793_, v_b_4791_);
lean_dec_ref(v_as_4788_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(lean_object* v_x_4797_){
_start:
{
if (lean_obj_tag(v_x_4797_) == 0)
{
lean_object* v___x_4798_; 
v___x_4798_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2___closed__0));
return v___x_4798_;
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4799_, 0, v_x_4797_);
v___x_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
return v___x_4800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(size_t v_sz_4801_, size_t v_i_4802_, lean_object* v_bs_4803_){
_start:
{
uint8_t v___x_4804_; 
v___x_4804_ = lean_usize_dec_lt(v_i_4802_, v_sz_4801_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; 
v___x_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4805_, 0, v_bs_4803_);
return v___x_4805_;
}
else
{
lean_object* v_v_4806_; lean_object* v___x_4807_; 
v_v_4806_ = lean_array_uget_borrowed(v_bs_4803_, v_i_4802_);
lean_inc(v_v_4806_);
v___x_4807_ = l_Lean_Json_getStr_x3f(v_v_4806_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec_ref(v_bs_4803_);
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4807_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4807_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4817_; lean_object* v_bs_x27_4818_; size_t v___x_4819_; size_t v___x_4820_; lean_object* v___x_4821_; 
v_a_4816_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_a_4816_);
lean_dec_ref(v___x_4807_);
v___x_4817_ = lean_unsigned_to_nat(0u);
v_bs_x27_4818_ = lean_array_uset(v_bs_4803_, v_i_4802_, v___x_4817_);
v___x_4819_ = ((size_t)1ULL);
v___x_4820_ = lean_usize_add(v_i_4802_, v___x_4819_);
v___x_4821_ = lean_array_uset(v_bs_x27_4818_, v_i_4802_, v_a_4816_);
v_i_4802_ = v___x_4820_;
v_bs_4803_ = v___x_4821_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_4823_, lean_object* v_i_4824_, lean_object* v_bs_4825_){
_start:
{
size_t v_sz_boxed_4826_; size_t v_i_boxed_4827_; lean_object* v_res_4828_; 
v_sz_boxed_4826_ = lean_unbox_usize(v_sz_4823_);
lean_dec(v_sz_4823_);
v_i_boxed_4827_ = lean_unbox_usize(v_i_4824_);
lean_dec(v_i_4824_);
v_res_4828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(v_sz_boxed_4826_, v_i_boxed_4827_, v_bs_4825_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(lean_object* v_x_4829_){
_start:
{
if (lean_obj_tag(v_x_4829_) == 4)
{
lean_object* v_elems_4830_; size_t v_sz_4831_; size_t v___x_4832_; lean_object* v___x_4833_; 
v_elems_4830_ = lean_ctor_get(v_x_4829_, 0);
lean_inc_ref(v_elems_4830_);
lean_dec_ref(v_x_4829_);
v_sz_4831_ = lean_array_size(v_elems_4830_);
v___x_4832_ = ((size_t)0ULL);
v___x_4833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1_spec__2(v_sz_4831_, v___x_4832_, v_elems_4830_);
return v___x_4833_;
}
else
{
lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4834_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__0));
v___x_4835_ = lean_unsigned_to_nat(80u);
v___x_4836_ = l_Lean_Json_pretty(v_x_4829_, v___x_4835_);
v___x_4837_ = lean_string_append(v___x_4834_, v___x_4836_);
lean_dec_ref(v___x_4836_);
v___x_4838_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheMap_parseCacheEntry_go_spec__0___closed__1));
v___x_4839_ = lean_string_append(v___x_4837_, v___x_4838_);
v___x_4840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
return v___x_4840_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(lean_object* v_x_4843_){
_start:
{
if (lean_obj_tag(v_x_4843_) == 0)
{
lean_object* v___x_4844_; 
v___x_4844_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3___closed__0));
return v___x_4844_;
}
else
{
lean_object* v___x_4845_; 
v___x_4845_ = l_Lean_Json_getObj_x3f(v_x_4843_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4862_; 
v_a_4854_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4856_ = v___x_4845_;
v_isShared_4857_ = v_isSharedCheck_4862_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4845_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4862_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4858_; lean_object* v___x_4860_; 
v___x_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4858_, 0, v_a_4854_);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v___x_4858_);
v___x_4860_ = v___x_4856_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(lean_object* v_val_4875_){
_start:
{
lean_object* v_a_4877_; lean_object* v___x_4921_; 
lean_inc(v_val_4875_);
v___x_4921_ = l_Lean_Json_getObj_x3f(v_val_4875_);
if (lean_obj_tag(v___x_4921_) == 1)
{
lean_object* v_a_4922_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4922_);
lean_dec_ref(v___x_4921_);
v___x_4929_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__0));
v___x_4930_ = l_Lake_JsonObject_getJson_x3f(v_a_4922_, v___x_4929_);
if (lean_obj_tag(v___x_4930_) == 0)
{
goto v___jp_4923_;
}
else
{
lean_object* v_val_4931_; lean_object* v___x_4932_; 
v_val_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_val_4931_);
lean_dec_ref(v___x_4930_);
v___x_4932_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__3(v_val_4931_);
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4942_; 
lean_dec(v_a_4922_);
lean_dec(v_val_4875_);
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4935_ = v___x_4932_;
v_isShared_4936_ = v_isSharedCheck_4942_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4932_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4942_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4940_; 
v___x_4937_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__1));
v___x_4938_ = lean_string_append(v___x_4937_, v_a_4933_);
lean_dec(v_a_4933_);
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 0, v___x_4938_);
v___x_4940_ = v___x_4935_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
else
{
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4950_; 
lean_dec(v_a_4922_);
lean_dec(v_val_4875_);
v_a_4943_ = lean_ctor_get(v___x_4932_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4932_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4945_ = v___x_4932_;
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_a_4943_);
lean_dec(v___x_4932_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4948_; 
if (v_isShared_4946_ == 0)
{
lean_ctor_set_tag(v___x_4945_, 0);
v___x_4948_ = v___x_4945_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_a_4943_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
else
{
lean_object* v_a_4951_; 
v_a_4951_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4951_);
lean_dec_ref(v___x_4932_);
if (lean_obj_tag(v_a_4951_) == 1)
{
lean_object* v_val_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
lean_dec(v_a_4922_);
lean_dec(v_val_4875_);
v_val_4952_ = lean_ctor_get(v_a_4951_, 0);
lean_inc(v_val_4952_);
lean_dec_ref(v_a_4951_);
v___x_4953_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__2));
v___x_4954_ = l_Lake_JsonObject_getJson_x3f(v_val_4952_, v___x_4953_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v___x_4955_; 
lean_dec(v_val_4952_);
v___x_4955_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__4));
return v___x_4955_;
}
else
{
lean_object* v_val_4956_; lean_object* v___x_4957_; 
v_val_4956_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_val_4956_);
lean_dec_ref(v___x_4954_);
v___x_4957_ = l_Lean_Json_getNat_x3f(v_val_4956_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4967_; 
lean_dec(v_val_4952_);
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4960_ = v___x_4957_;
v_isShared_4961_ = v_isSharedCheck_4967_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4957_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4967_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4965_; 
v___x_4962_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__5));
v___x_4963_ = lean_string_append(v___x_4962_, v_a_4958_);
lean_dec(v_a_4958_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 0, v___x_4963_);
v___x_4965_ = v___x_4960_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4963_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
else
{
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
lean_dec(v_val_4952_);
v_a_4968_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4957_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4957_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
lean_ctor_set_tag(v___x_4970_, 0);
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v_a_4976_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4976_);
lean_dec_ref(v___x_4957_);
v___x_4977_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__6));
v___x_4978_ = l_Lake_JsonObject_getJson_x3f(v_val_4952_, v___x_4977_);
lean_dec(v_val_4952_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v___x_4979_; 
lean_dec(v_a_4976_);
v___x_4979_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__8));
return v___x_4979_;
}
else
{
lean_object* v_val_4980_; lean_object* v___x_4981_; 
v_val_4980_ = lean_ctor_get(v___x_4978_, 0);
lean_inc(v_val_4980_);
lean_dec_ref(v___x_4978_);
v___x_4981_ = l_Lean_Json_getStr_x3f(v_val_4980_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_4991_; 
lean_dec(v_a_4976_);
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4984_ = v___x_4981_;
v_isShared_4985_ = v_isSharedCheck_4991_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4981_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_4991_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4989_; 
v___x_4986_ = ((lean_object*)(l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1___closed__9));
v___x_4987_ = lean_string_append(v___x_4986_, v_a_4982_);
lean_dec(v_a_4982_);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 0, v___x_4987_);
v___x_4989_ = v___x_4984_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4987_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
else
{
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec(v_a_4976_);
v_a_4992_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4981_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4981_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
lean_ctor_set_tag(v___x_4994_, 0);
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5008_; 
v_a_5000_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5002_ = v___x_4981_;
v_isShared_5003_ = v_isSharedCheck_5008_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4981_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5008_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5004_; lean_object* v___x_5006_; 
v___x_5004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5004_, 0, v_a_4976_);
lean_ctor_set(v___x_5004_, 1, v_a_5000_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set(v___x_5002_, 0, v___x_5004_);
v___x_5006_ = v___x_5002_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
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
lean_dec(v_a_4951_);
goto v___jp_4923_;
}
}
}
}
v___jp_4923_:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; 
v___x_4924_ = ((lean_object*)(l_Lake_CacheOutput_toJson___closed__0));
v___x_4925_ = l_Lake_JsonObject_getJson_x3f(v_a_4922_, v___x_4924_);
lean_dec(v_a_4922_);
if (lean_obj_tag(v___x_4925_) == 0)
{
v_a_4877_ = v___x_4925_;
goto v___jp_4876_;
}
else
{
lean_object* v_val_4926_; lean_object* v___x_4927_; lean_object* v_a_4928_; 
v_val_4926_ = lean_ctor_get(v___x_4925_, 0);
lean_inc(v_val_4926_);
lean_dec_ref(v___x_4925_);
v___x_4927_ = l_Option_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__2(v_val_4926_);
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
lean_inc(v_a_4928_);
lean_dec_ref(v___x_4927_);
v_a_4877_ = v_a_4928_;
goto v___jp_4876_;
}
}
}
else
{
lean_object* v___x_5009_; 
lean_dec_ref(v___x_4921_);
v___x_5009_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_4875_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_5009_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_5009_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5026_; 
v_a_5018_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5020_ = v___x_5009_;
v_isShared_5021_ = v_isSharedCheck_5026_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5009_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5026_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5022_; lean_object* v___x_5024_; 
v___x_5022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5022_, 0, v_a_5018_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set(v___x_5020_, 0, v___x_5022_);
v___x_5024_ = v___x_5020_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
v___jp_4876_:
{
if (lean_obj_tag(v_a_4877_) == 1)
{
lean_object* v_val_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4902_; 
lean_dec(v_val_4875_);
v_val_4878_ = lean_ctor_get(v_a_4877_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v_a_4877_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4880_ = v_a_4877_;
v_isShared_4881_ = v_isSharedCheck_4902_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_val_4878_);
lean_dec(v_a_4877_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4902_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4882_; 
v___x_4882_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_4878_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
lean_del_object(v___x_4880_);
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4882_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4882_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4888_; 
if (v_isShared_4886_ == 0)
{
v___x_4888_ = v___x_4885_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4883_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4901_; 
v_a_4891_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4893_ = v___x_4882_;
v_isShared_4894_ = v_isSharedCheck_4901_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4882_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4901_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4881_ == 0)
{
lean_ctor_set_tag(v___x_4880_, 0);
lean_ctor_set(v___x_4880_, 0, v_a_4891_);
v___x_4896_ = v___x_4880_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
lean_object* v___x_4898_; 
if (v_isShared_4894_ == 0)
{
lean_ctor_set(v___x_4893_, 0, v___x_4896_);
v___x_4898_ = v___x_4893_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4896_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
}
else
{
lean_object* v___x_4903_; 
lean_dec(v_a_4877_);
v___x_4903_ = l_Array_fromJson_x3f___at___00Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1_spec__1(v_val_4875_);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_object* v_a_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4911_; 
v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4911_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4906_ = v___x_4903_;
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_a_4904_);
lean_dec(v___x_4903_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4911_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4909_; 
if (v_isShared_4907_ == 0)
{
v___x_4909_ = v___x_4906_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4904_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
}
else
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4920_; 
v_a_4912_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4914_ = v___x_4903_;
v_isShared_4915_ = v_isSharedCheck_4920_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4903_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4920_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4916_; lean_object* v___x_4918_; 
v___x_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4916_, 0, v_a_4912_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v___x_4916_);
v___x_4918_ = v___x_4914_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4916_);
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
}
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18(void){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5045_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__16));
v___x_5046_ = lean_unsigned_to_nat(12u);
v___x_5047_ = lean_mk_empty_array_with_capacity(v___x_5046_);
v___x_5048_ = lean_array_push(v___x_5047_, v___x_5045_);
return v___x_5048_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19(void){
_start:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5049_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__14));
v___x_5050_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__18);
v___x_5051_ = lean_array_push(v___x_5050_, v___x_5049_);
return v___x_5051_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20(void){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5052_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__7));
v___x_5053_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__19);
v___x_5054_ = lean_array_push(v___x_5053_, v___x_5052_);
return v___x_5054_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21(void){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5055_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__15));
v___x_5056_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__20);
v___x_5057_ = lean_array_push(v___x_5056_, v___x_5055_);
return v___x_5057_;
}
}
static lean_object* _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22(void){
_start:
{
lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = l_Lake_Reservoir_lakeHeaders;
v___x_5059_ = lean_array_get_size(v___x_5058_);
return v___x_5059_;
}
}
static uint8_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23(void){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; uint8_t v___x_5062_; 
v___x_5060_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5061_ = lean_unsigned_to_nat(0u);
v___x_5062_ = lean_nat_dec_lt(v___x_5061_, v___x_5060_);
return v___x_5062_;
}
}
static uint8_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24(void){
_start:
{
lean_object* v___x_5063_; uint8_t v___x_5064_; 
v___x_5063_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5064_ = lean_nat_dec_le(v___x_5063_, v___x_5063_);
return v___x_5064_;
}
}
static size_t _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25(void){
_start:
{
lean_object* v___x_5065_; size_t v___x_5066_; 
v___x_5065_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__22);
v___x_5066_ = lean_usize_of_nat(v___x_5065_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(lean_object* v_infos_5067_, lean_object* v_url_5068_, lean_object* v_h_5069_, lean_object* v_path_5070_, lean_object* v___y_5071_){
_start:
{
uint32_t v___y_5074_; lean_object* v___y_5075_; lean_object* v___y_5086_; uint32_t v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v_a_5090_; uint8_t v___y_5118_; lean_object* v___y_5119_; uint32_t v___y_5120_; lean_object* v___y_5121_; lean_object* v_msg_5122_; lean_object* v___y_5123_; uint8_t v___y_5137_; lean_object* v___y_5138_; uint32_t v___y_5139_; lean_object* v___y_5140_; lean_object* v___y_5141_; lean_object* v_msg_5142_; lean_object* v___y_5143_; uint8_t v___y_5154_; lean_object* v___y_5155_; uint32_t v___y_5156_; lean_object* v___y_5157_; lean_object* v___y_5158_; lean_object* v___y_5159_; lean_object* v_msg_5160_; lean_object* v___y_5161_; uint8_t v___y_5174_; lean_object* v___y_5175_; uint32_t v___y_5176_; lean_object* v___y_5177_; lean_object* v___y_5178_; size_t v_sz_5196_; size_t v___x_5197_; lean_object* v___x_5198_; lean_object* v_body_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v_sz_5196_ = lean_array_size(v_infos_5067_);
v___x_5197_ = ((size_t)0ULL);
lean_inc_ref(v_infos_5067_);
v___x_5198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_5196_, v___x_5197_, v_infos_5067_);
v_body_5199_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_body_5199_, 0, v___x_5198_);
v___x_5200_ = l_Lean_Json_compress(v_body_5199_);
v___x_5201_ = lean_io_prim_handle_put_str(v_h_5069_, v___x_5200_);
lean_dec_ref(v___x_5200_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v___x_5202_; 
lean_dec_ref(v___x_5201_);
v___x_5202_ = lean_io_prim_handle_flush(v_h_5069_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v___y_5204_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; uint8_t v___x_5306_; 
lean_dec_ref(v___x_5202_);
v___x_5287_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16));
v___x_5288_ = lean_string_append(v___x_5287_, v_path_5070_);
v___x_5289_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_5290_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_5291_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_5292_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_5293_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_5294_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5295_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17));
v___x_5296_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21);
v___x_5297_ = lean_array_push(v___x_5296_, v___x_5288_);
v___x_5298_ = lean_array_push(v___x_5297_, v___x_5289_);
v___x_5299_ = lean_array_push(v___x_5298_, v___x_5290_);
v___x_5300_ = lean_array_push(v___x_5299_, v___x_5291_);
v___x_5301_ = lean_array_push(v___x_5300_, v___x_5292_);
v___x_5302_ = lean_array_push(v___x_5301_, v___x_5293_);
v___x_5303_ = lean_array_push(v___x_5302_, v___x_5294_);
v___x_5304_ = lean_array_push(v___x_5303_, v___x_5295_);
v___x_5305_ = l_Lake_Reservoir_lakeHeaders;
v___x_5306_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23);
if (v___x_5306_ == 0)
{
v___y_5204_ = v___x_5304_;
goto v___jp_5203_;
}
else
{
uint8_t v___x_5307_; 
v___x_5307_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24);
if (v___x_5307_ == 0)
{
if (v___x_5306_ == 0)
{
v___y_5204_ = v___x_5304_;
goto v___jp_5203_;
}
else
{
size_t v___x_5308_; lean_object* v___x_5309_; 
v___x_5308_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_5309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5305_, v___x_5197_, v___x_5308_, v___x_5304_);
v___y_5204_ = v___x_5309_;
goto v___jp_5203_;
}
}
else
{
size_t v___x_5310_; lean_object* v___x_5311_; 
v___x_5310_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5305_, v___x_5197_, v___x_5310_, v___x_5304_);
v___y_5204_ = v___x_5311_;
goto v___jp_5203_;
}
}
v___jp_5203_:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; uint8_t v___x_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
v___x_5205_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_5206_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
lean_inc_ref(v_url_5068_);
v___x_5207_ = lean_array_push(v___y_5204_, v_url_5068_);
v___x_5208_ = lean_box(0);
v___x_5209_ = lean_unsigned_to_nat(0u);
v___x_5210_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_5211_ = 1;
v___x_5212_ = 0;
v___x_5213_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_5213_, 0, v___x_5205_);
lean_ctor_set(v___x_5213_, 1, v___x_5206_);
lean_ctor_set(v___x_5213_, 2, v___x_5207_);
lean_ctor_set(v___x_5213_, 3, v___x_5208_);
lean_ctor_set(v___x_5213_, 4, v___x_5210_);
lean_ctor_set_uint8(v___x_5213_, sizeof(void*)*5, v___x_5211_);
lean_ctor_set_uint8(v___x_5213_, sizeof(void*)*5 + 1, v___x_5212_);
lean_inc_ref(v___x_5213_);
v___x_5214_ = l_Lake_mkCmdLog(v___x_5213_);
v___x_5215_ = 0;
v___x_5216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5216_, 0, v___x_5214_);
lean_ctor_set_uint8(v___x_5216_, sizeof(void*)*1, v___x_5215_);
lean_inc_ref(v___y_5071_);
v___x_5217_ = lean_apply_2(v___y_5071_, v___x_5216_, lean_box(0));
v___x_5218_ = l_IO_Process_output(v___x_5213_, v___x_5208_);
if (lean_obj_tag(v___x_5218_) == 0)
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5273_; 
v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5221_ = v___x_5218_;
v_isShared_5222_ = v_isSharedCheck_5273_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5218_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5273_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
uint32_t v_exitCode_5223_; lean_object* v_stdout_5224_; lean_object* v_stderr_5225_; lean_object* v___x_5226_; 
v_exitCode_5223_ = lean_ctor_get_uint32(v_a_5219_, sizeof(void*)*2);
v_stdout_5224_ = lean_ctor_get(v_a_5219_, 0);
lean_inc_ref_n(v_stdout_5224_, 2);
v_stderr_5225_ = lean_ctor_get(v_a_5219_, 1);
lean_inc_ref(v_stderr_5225_);
lean_dec(v_a_5219_);
v___x_5226_ = l_Lean_Json_parse(v_stdout_5224_);
if (lean_obj_tag(v___x_5226_) == 0)
{
lean_dec_ref(v___x_5226_);
lean_del_object(v___x_5221_);
lean_dec_ref(v_infos_5067_);
v___y_5174_ = v___x_5215_;
v___y_5175_ = v_stderr_5225_;
v___y_5176_ = v_exitCode_5223_;
v___y_5177_ = v___x_5209_;
v___y_5178_ = v_stdout_5224_;
goto v___jp_5173_;
}
else
{
lean_object* v_a_5227_; lean_object* v___x_5228_; 
v_a_5227_ = lean_ctor_get(v___x_5226_, 0);
lean_inc(v_a_5227_);
lean_dec_ref(v___x_5226_);
v___x_5228_ = l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(v_a_5227_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_dec_ref(v___x_5228_);
lean_del_object(v___x_5221_);
lean_dec_ref(v_infos_5067_);
v___y_5174_ = v___x_5215_;
v___y_5175_ = v_stderr_5225_;
v___y_5176_ = v_exitCode_5223_;
v___y_5177_ = v___x_5209_;
v___y_5178_ = v_stdout_5224_;
goto v___jp_5173_;
}
else
{
lean_object* v_a_5229_; 
lean_dec_ref(v_stderr_5225_);
lean_dec_ref(v_stdout_5224_);
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_a_5229_);
lean_dec_ref(v___x_5228_);
if (lean_obj_tag(v_a_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; uint8_t v___x_5233_; 
v_a_5230_ = lean_ctor_get(v_a_5229_, 0);
lean_inc(v_a_5230_);
lean_dec_ref(v_a_5229_);
v___x_5231_ = lean_array_get_size(v_infos_5067_);
v___x_5232_ = lean_array_get_size(v_a_5230_);
v___x_5233_ = lean_nat_dec_eq(v___x_5231_, v___x_5232_);
if (v___x_5233_ == 0)
{
lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; uint8_t v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5249_; 
lean_dec(v_a_5230_);
lean_dec_ref(v_infos_5067_);
v___x_5234_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5235_ = lean_string_append(v___x_5234_, v_url_5068_);
lean_dec_ref(v_url_5068_);
v___x_5236_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10));
v___x_5237_ = lean_string_append(v___x_5235_, v___x_5236_);
v___x_5238_ = l_Nat_reprFast(v___x_5231_);
v___x_5239_ = lean_string_append(v___x_5237_, v___x_5238_);
lean_dec_ref(v___x_5238_);
v___x_5240_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11));
v___x_5241_ = lean_string_append(v___x_5239_, v___x_5240_);
v___x_5242_ = l_Nat_reprFast(v___x_5232_);
v___x_5243_ = lean_string_append(v___x_5241_, v___x_5242_);
lean_dec_ref(v___x_5242_);
v___x_5244_ = 3;
v___x_5245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5245_, 0, v___x_5243_);
lean_ctor_set_uint8(v___x_5245_, sizeof(void*)*1, v___x_5244_);
lean_inc_ref(v___y_5071_);
v___x_5246_ = lean_apply_2(v___y_5071_, v___x_5245_, lean_box(0));
v___x_5247_ = lean_box(0);
if (v_isShared_5222_ == 0)
{
lean_ctor_set_tag(v___x_5221_, 1);
lean_ctor_set(v___x_5221_, 0, v___x_5247_);
v___x_5249_ = v___x_5221_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5247_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
else
{
lean_object* v___x_5251_; lean_object* v___x_5253_; 
lean_dec_ref(v_url_5068_);
v___x_5251_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5230_, v___x_5231_, v___x_5231_, v_infos_5067_);
lean_dec(v_a_5230_);
if (v_isShared_5222_ == 0)
{
lean_ctor_set(v___x_5221_, 0, v___x_5251_);
v___x_5253_ = v___x_5221_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5251_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
}
else
{
lean_object* v_status_5255_; lean_object* v_message_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; uint8_t v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5271_; 
lean_dec_ref(v_infos_5067_);
v_status_5255_ = lean_ctor_get(v_a_5229_, 0);
lean_inc(v_status_5255_);
v_message_5256_ = lean_ctor_get(v_a_5229_, 1);
lean_inc_ref(v_message_5256_);
lean_dec_ref(v_a_5229_);
v___x_5257_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5258_ = l_Nat_reprFast(v_status_5255_);
v___x_5259_ = lean_string_append(v___x_5257_, v___x_5258_);
lean_dec_ref(v___x_5258_);
v___x_5260_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12));
v___x_5261_ = lean_string_append(v___x_5259_, v___x_5260_);
v___x_5262_ = lean_string_append(v___x_5261_, v_url_5068_);
lean_dec_ref(v_url_5068_);
v___x_5263_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13));
v___x_5264_ = lean_string_append(v___x_5262_, v___x_5263_);
v___x_5265_ = lean_string_append(v___x_5264_, v_message_5256_);
lean_dec_ref(v_message_5256_);
v___x_5266_ = 3;
v___x_5267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5267_, 0, v___x_5265_);
lean_ctor_set_uint8(v___x_5267_, sizeof(void*)*1, v___x_5266_);
lean_inc_ref(v___y_5071_);
v___x_5268_ = lean_apply_2(v___y_5071_, v___x_5267_, lean_box(0));
v___x_5269_ = lean_box(0);
if (v_isShared_5222_ == 0)
{
lean_ctor_set_tag(v___x_5221_, 1);
lean_ctor_set(v___x_5221_, 0, v___x_5269_);
v___x_5271_ = v___x_5221_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v___x_5269_);
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
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5286_; 
lean_dec_ref(v_url_5068_);
lean_dec_ref(v_infos_5067_);
v_a_5274_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5276_ = v___x_5218_;
v_isShared_5277_ = v_isSharedCheck_5286_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5218_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5286_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5278_; uint8_t v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5284_; 
v___x_5278_ = lean_io_error_to_string(v_a_5274_);
v___x_5279_ = 3;
v___x_5280_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5280_, 0, v___x_5278_);
lean_ctor_set_uint8(v___x_5280_, sizeof(void*)*1, v___x_5279_);
lean_inc_ref(v___y_5071_);
v___x_5281_ = lean_apply_2(v___y_5071_, v___x_5280_, lean_box(0));
v___x_5282_ = lean_box(0);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 0, v___x_5282_);
v___x_5284_ = v___x_5276_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5282_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
}
else
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5324_; 
lean_dec_ref(v_url_5068_);
lean_dec_ref(v_infos_5067_);
v_a_5312_ = lean_ctor_get(v___x_5202_, 0);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5314_ = v___x_5202_;
v_isShared_5315_ = v_isSharedCheck_5324_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5202_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5324_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5316_; uint8_t v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5322_; 
v___x_5316_ = lean_io_error_to_string(v_a_5312_);
v___x_5317_ = 3;
v___x_5318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5318_, 0, v___x_5316_);
lean_ctor_set_uint8(v___x_5318_, sizeof(void*)*1, v___x_5317_);
lean_inc_ref(v___y_5071_);
v___x_5319_ = lean_apply_2(v___y_5071_, v___x_5318_, lean_box(0));
v___x_5320_ = lean_box(0);
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 0, v___x_5320_);
v___x_5322_ = v___x_5314_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v___x_5320_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5337_; 
lean_dec_ref(v_url_5068_);
lean_dec_ref(v_infos_5067_);
v_a_5325_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5327_ = v___x_5201_;
v_isShared_5328_ = v_isSharedCheck_5337_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5201_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5337_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5329_; uint8_t v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5335_; 
v___x_5329_ = lean_io_error_to_string(v_a_5325_);
v___x_5330_ = 3;
v___x_5331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5331_, 0, v___x_5329_);
lean_ctor_set_uint8(v___x_5331_, sizeof(void*)*1, v___x_5330_);
lean_inc_ref(v___y_5071_);
v___x_5332_ = lean_apply_2(v___y_5071_, v___x_5331_, lean_box(0));
v___x_5333_ = lean_box(0);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 0, v___x_5333_);
v___x_5335_ = v___x_5327_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5333_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
v___jp_5073_:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; uint8_t v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5076_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0));
v___x_5077_ = lean_uint32_to_nat(v___y_5074_);
v___x_5078_ = l_Nat_reprFast(v___x_5077_);
v___x_5079_ = lean_string_append(v___x_5076_, v___x_5078_);
lean_dec_ref(v___x_5078_);
v___x_5080_ = 3;
v___x_5081_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5081_, 0, v___x_5079_);
lean_ctor_set_uint8(v___x_5081_, sizeof(void*)*1, v___x_5080_);
lean_inc_ref(v___y_5075_);
v___x_5082_ = lean_apply_2(v___y_5075_, v___x_5081_, lean_box(0));
v___x_5083_ = lean_box(0);
v___x_5084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5084_, 0, v___x_5083_);
return v___x_5084_;
}
v___jp_5085_:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; uint8_t v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; uint8_t v___x_5107_; 
v___x_5091_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5092_ = lean_string_append(v___x_5091_, v_url_5068_);
lean_dec_ref(v_url_5068_);
v___x_5093_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2));
v___x_5094_ = lean_string_append(v___x_5092_, v___x_5093_);
v___x_5095_ = lean_string_append(v___x_5094_, v_a_5090_);
lean_dec_ref(v_a_5090_);
v___x_5096_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_5097_ = lean_string_append(v___x_5095_, v___x_5096_);
v___x_5098_ = lean_string_utf8_byte_size(v___y_5086_);
lean_inc(v___y_5088_);
v___x_5099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5099_, 0, v___y_5086_);
lean_ctor_set(v___x_5099_, 1, v___y_5088_);
lean_ctor_set(v___x_5099_, 2, v___x_5098_);
v___x_5100_ = l_String_Slice_trimAscii(v___x_5099_);
v___x_5101_ = l_String_Slice_toString(v___x_5100_);
lean_dec_ref(v___x_5100_);
v___x_5102_ = lean_string_append(v___x_5097_, v___x_5101_);
lean_dec_ref(v___x_5101_);
v___x_5103_ = 3;
v___x_5104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5104_, 0, v___x_5102_);
lean_ctor_set_uint8(v___x_5104_, sizeof(void*)*1, v___x_5103_);
lean_inc_ref(v___y_5071_);
v___x_5105_ = lean_apply_2(v___y_5071_, v___x_5104_, lean_box(0));
v___x_5106_ = lean_string_utf8_byte_size(v___y_5089_);
v___x_5107_ = lean_nat_dec_eq(v___x_5106_, v___y_5088_);
if (v___x_5107_ == 0)
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; uint8_t v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; 
v___x_5108_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3));
lean_inc(v___y_5088_);
lean_inc_ref(v___y_5089_);
v___x_5109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5109_, 0, v___y_5089_);
lean_ctor_set(v___x_5109_, 1, v___y_5088_);
lean_ctor_set(v___x_5109_, 2, v___x_5106_);
v___x_5110_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5109_, v___x_5106_);
lean_dec_ref(v___x_5109_);
v___x_5111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5111_, 0, v___y_5089_);
lean_ctor_set(v___x_5111_, 1, v___y_5088_);
lean_ctor_set(v___x_5111_, 2, v___x_5110_);
v___x_5112_ = l_String_Slice_toString(v___x_5111_);
lean_dec_ref(v___x_5111_);
v___x_5113_ = lean_string_append(v___x_5108_, v___x_5112_);
lean_dec_ref(v___x_5112_);
v___x_5114_ = 2;
v___x_5115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5115_, 0, v___x_5113_);
lean_ctor_set_uint8(v___x_5115_, sizeof(void*)*1, v___x_5114_);
lean_inc_ref(v___y_5071_);
v___x_5116_ = lean_apply_2(v___y_5071_, v___x_5115_, lean_box(0));
v___y_5074_ = v___y_5087_;
v___y_5075_ = v___y_5071_;
goto v___jp_5073_;
}
else
{
lean_dec_ref(v___y_5089_);
lean_dec(v___y_5088_);
v___y_5074_ = v___y_5087_;
v___y_5075_ = v___y_5071_;
goto v___jp_5073_;
}
}
v___jp_5117_:
{
uint8_t v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; 
v___x_5124_ = 3;
v___x_5125_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5125_, 0, v_msg_5122_);
lean_ctor_set_uint8(v___x_5125_, sizeof(void*)*1, v___x_5124_);
lean_inc_ref_n(v___y_5123_, 2);
v___x_5126_ = lean_apply_2(v___y_5123_, v___x_5125_, lean_box(0));
v___x_5127_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4));
v___x_5128_ = lean_string_utf8_byte_size(v___y_5119_);
lean_inc(v___y_5121_);
lean_inc_ref(v___y_5119_);
v___x_5129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5129_, 0, v___y_5119_);
lean_ctor_set(v___x_5129_, 1, v___y_5121_);
lean_ctor_set(v___x_5129_, 2, v___x_5128_);
v___x_5130_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5129_, v___x_5128_);
lean_dec_ref(v___x_5129_);
v___x_5131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5131_, 0, v___y_5119_);
lean_ctor_set(v___x_5131_, 1, v___y_5121_);
lean_ctor_set(v___x_5131_, 2, v___x_5130_);
v___x_5132_ = l_String_Slice_toString(v___x_5131_);
lean_dec_ref(v___x_5131_);
v___x_5133_ = lean_string_append(v___x_5127_, v___x_5132_);
lean_dec_ref(v___x_5132_);
v___x_5134_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5134_, 0, v___x_5133_);
lean_ctor_set_uint8(v___x_5134_, sizeof(void*)*1, v___y_5118_);
v___x_5135_ = lean_apply_2(v___y_5123_, v___x_5134_, lean_box(0));
v___y_5074_ = v___y_5120_;
v___y_5075_ = v___y_5123_;
goto v___jp_5073_;
}
v___jp_5136_:
{
lean_object* v___x_5144_; uint8_t v___x_5145_; 
v___x_5144_ = lean_string_utf8_byte_size(v___y_5141_);
v___x_5145_ = lean_nat_dec_eq(v___x_5144_, v___y_5140_);
if (v___x_5145_ == 0)
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5146_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_5147_ = lean_string_append(v_msg_5142_, v___x_5146_);
lean_inc_n(v___y_5140_, 2);
lean_inc_ref(v___y_5141_);
v___x_5148_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5148_, 0, v___y_5141_);
lean_ctor_set(v___x_5148_, 1, v___y_5140_);
lean_ctor_set(v___x_5148_, 2, v___x_5144_);
v___x_5149_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5148_, v___x_5144_);
lean_dec_ref(v___x_5148_);
v___x_5150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5150_, 0, v___y_5141_);
lean_ctor_set(v___x_5150_, 1, v___y_5140_);
lean_ctor_set(v___x_5150_, 2, v___x_5149_);
v___x_5151_ = l_String_Slice_toString(v___x_5150_);
lean_dec_ref(v___x_5150_);
v___x_5152_ = lean_string_append(v___x_5147_, v___x_5151_);
lean_dec_ref(v___x_5151_);
v___y_5118_ = v___y_5137_;
v___y_5119_ = v___y_5138_;
v___y_5120_ = v___y_5139_;
v___y_5121_ = v___y_5140_;
v_msg_5122_ = v___x_5152_;
v___y_5123_ = v___y_5143_;
goto v___jp_5117_;
}
else
{
lean_dec_ref(v___y_5141_);
v___y_5118_ = v___y_5137_;
v___y_5119_ = v___y_5138_;
v___y_5120_ = v___y_5139_;
v___y_5121_ = v___y_5140_;
v_msg_5122_ = v_msg_5142_;
v___y_5123_ = v___y_5143_;
goto v___jp_5117_;
}
}
v___jp_5153_:
{
lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5162_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6));
v___x_5163_ = lean_string_append(v_msg_5160_, v___x_5162_);
v___x_5164_ = lean_string_append(v___x_5163_, v_url_5068_);
lean_dec_ref(v_url_5068_);
v___x_5165_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_5166_ = l_Lake_JsonObject_getJson_x3f(v___y_5159_, v___x_5165_);
lean_dec(v___y_5159_);
if (lean_obj_tag(v___x_5166_) == 0)
{
v___y_5137_ = v___y_5154_;
v___y_5138_ = v___y_5155_;
v___y_5139_ = v___y_5156_;
v___y_5140_ = v___y_5157_;
v___y_5141_ = v___y_5158_;
v_msg_5142_ = v___x_5164_;
v___y_5143_ = v___y_5161_;
goto v___jp_5136_;
}
else
{
lean_object* v_val_5167_; lean_object* v___x_5168_; 
v_val_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_val_5167_);
lean_dec_ref(v___x_5166_);
v___x_5168_ = l_Lean_Json_getStr_x3f(v_val_5167_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_dec_ref(v___x_5168_);
v___y_5137_ = v___y_5154_;
v___y_5138_ = v___y_5155_;
v___y_5139_ = v___y_5156_;
v___y_5140_ = v___y_5157_;
v___y_5141_ = v___y_5158_;
v_msg_5142_ = v___x_5164_;
v___y_5143_ = v___y_5161_;
goto v___jp_5136_;
}
else
{
if (lean_obj_tag(v___x_5168_) == 1)
{
lean_object* v_a_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref(v___x_5168_);
v___x_5170_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7));
v___x_5171_ = lean_string_append(v___x_5164_, v___x_5170_);
v___x_5172_ = lean_string_append(v___x_5171_, v_a_5169_);
lean_dec(v_a_5169_);
v___y_5137_ = v___y_5154_;
v___y_5138_ = v___y_5155_;
v___y_5139_ = v___y_5156_;
v___y_5140_ = v___y_5157_;
v___y_5141_ = v___y_5158_;
v_msg_5142_ = v___x_5172_;
v___y_5143_ = v___y_5161_;
goto v___jp_5136_;
}
else
{
lean_dec_ref(v___x_5168_);
v___y_5137_ = v___y_5154_;
v___y_5138_ = v___y_5155_;
v___y_5139_ = v___y_5156_;
v___y_5140_ = v___y_5157_;
v___y_5141_ = v___y_5158_;
v_msg_5142_ = v___x_5164_;
v___y_5143_ = v___y_5161_;
goto v___jp_5136_;
}
}
}
}
v___jp_5173_:
{
lean_object* v___x_5179_; 
lean_inc_ref(v___y_5175_);
v___x_5179_ = l_Lean_Json_parse(v___y_5175_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v_a_5180_; 
v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
lean_inc(v_a_5180_);
lean_dec_ref(v___x_5179_);
v___y_5086_ = v___y_5175_;
v___y_5087_ = v___y_5176_;
v___y_5088_ = v___y_5177_;
v___y_5089_ = v___y_5178_;
v_a_5090_ = v_a_5180_;
goto v___jp_5085_;
}
else
{
lean_object* v_a_5181_; lean_object* v___x_5182_; 
v_a_5181_ = lean_ctor_get(v___x_5179_, 0);
lean_inc(v_a_5181_);
lean_dec_ref(v___x_5179_);
v___x_5182_ = l_Lean_Json_getObj_x3f(v_a_5181_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
lean_dec_ref(v___x_5182_);
v___y_5086_ = v___y_5175_;
v___y_5087_ = v___y_5176_;
v___y_5088_ = v___y_5177_;
v___y_5089_ = v___y_5178_;
v_a_5090_ = v_a_5183_;
goto v___jp_5085_;
}
else
{
lean_object* v_a_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v_a_5184_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5184_);
lean_dec_ref(v___x_5182_);
v___x_5185_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8));
v___x_5186_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_5187_ = l_Lake_JsonObject_getJson_x3f(v_a_5184_, v___x_5186_);
if (lean_obj_tag(v___x_5187_) == 0)
{
v___y_5154_ = v___y_5174_;
v___y_5155_ = v___y_5175_;
v___y_5156_ = v___y_5176_;
v___y_5157_ = v___y_5177_;
v___y_5158_ = v___y_5178_;
v___y_5159_ = v_a_5184_;
v_msg_5160_ = v___x_5185_;
v___y_5161_ = v___y_5071_;
goto v___jp_5153_;
}
else
{
lean_object* v_val_5188_; lean_object* v___x_5189_; 
v_val_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_val_5188_);
lean_dec_ref(v___x_5187_);
v___x_5189_ = l_Lean_Json_getNat_x3f(v_val_5188_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_dec_ref(v___x_5189_);
v___y_5154_ = v___y_5174_;
v___y_5155_ = v___y_5175_;
v___y_5156_ = v___y_5176_;
v___y_5157_ = v___y_5177_;
v___y_5158_ = v___y_5178_;
v___y_5159_ = v_a_5184_;
v_msg_5160_ = v___x_5185_;
v___y_5161_ = v___y_5071_;
goto v___jp_5153_;
}
else
{
if (lean_obj_tag(v___x_5189_) == 1)
{
lean_object* v_a_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_a_5190_);
lean_dec_ref(v___x_5189_);
v___x_5191_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5192_ = l_Nat_reprFast(v_a_5190_);
v___x_5193_ = lean_string_append(v___x_5191_, v___x_5192_);
lean_dec_ref(v___x_5192_);
v___x_5194_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v___x_5195_ = lean_string_append(v___x_5193_, v___x_5194_);
v___y_5154_ = v___y_5174_;
v___y_5155_ = v___y_5175_;
v___y_5156_ = v___y_5176_;
v___y_5157_ = v___y_5177_;
v___y_5158_ = v___y_5178_;
v___y_5159_ = v_a_5184_;
v_msg_5160_ = v___x_5195_;
v___y_5161_ = v___y_5071_;
goto v___jp_5153_;
}
else
{
lean_dec_ref(v___x_5189_);
v___y_5154_ = v___y_5174_;
v___y_5155_ = v___y_5175_;
v___y_5156_ = v___y_5176_;
v___y_5157_ = v___y_5177_;
v___y_5158_ = v___y_5178_;
v___y_5159_ = v_a_5184_;
v_msg_5160_ = v___x_5185_;
v___y_5161_ = v___y_5071_;
goto v___jp_5153_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed(lean_object* v_infos_5338_, lean_object* v_url_5339_, lean_object* v_h_5340_, lean_object* v_path_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
lean_object* v_res_5344_; 
v_res_5344_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0(v_infos_5338_, v_url_5339_, v_h_5340_, v_path_5341_, v___y_5342_);
lean_dec_ref(v___y_5342_);
lean_dec_ref(v_path_5341_);
lean_dec(v_h_5340_);
return v_res_5344_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(lean_object* v_url_5345_, lean_object* v_infos_5346_, lean_object* v_a_5347_){
_start:
{
lean_object* v___f_5349_; lean_object* v___x_5350_; 
v___f_5349_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5349_, 0, v_infos_5346_);
lean_closure_set(v___f_5349_, 1, v_url_5345_);
v___x_5350_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5349_, v_a_5347_);
return v___x_5350_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___boxed(lean_object* v_url_5351_, lean_object* v_infos_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls(v_url_5351_, v_infos_5352_, v_a_5353_);
lean_dec_ref(v_a_5353_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(lean_object* v_a_5356_, lean_object* v___x_5357_, lean_object* v_n_5358_, lean_object* v_j_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_){
_start:
{
lean_object* v___x_5362_; 
v___x_5362_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5356_, v_n_5358_, v_j_5359_, v_a_5361_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___boxed(lean_object* v_a_5363_, lean_object* v___x_5364_, lean_object* v_n_5365_, lean_object* v_j_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_){
_start:
{
lean_object* v_res_5369_; 
v_res_5369_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2(v_a_5363_, v___x_5364_, v_n_5365_, v_j_5366_, v_a_5367_, v_a_5368_);
lean_dec(v_n_5365_);
lean_dec(v___x_5364_);
lean_dec_ref(v_a_5363_);
return v_res_5369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(lean_object* v_cfg_5370_, lean_object* v_h_5371_, lean_object* v_path_5372_, lean_object* v___y_5373_){
_start:
{
uint8_t v___y_5376_; uint8_t v___y_5382_; lean_object* v___y_5383_; uint32_t v___y_5384_; lean_object* v___y_5385_; uint8_t v_kind_5394_; lean_object* v_scope_5395_; lean_object* v_infos_5396_; lean_object* v_key_5397_; uint8_t v___y_5399_; uint32_t v___y_5400_; lean_object* v___y_5401_; lean_object* v___y_5406_; uint8_t v___y_5407_; lean_object* v___y_5408_; lean_object* v___y_5409_; uint32_t v___y_5410_; lean_object* v___y_5411_; lean_object* v___y_5412_; lean_object* v___y_5424_; uint8_t v___y_5425_; uint32_t v___y_5426_; lean_object* v___y_5427_; lean_object* v___y_5428_; lean_object* v___y_5433_; uint8_t v___y_5434_; lean_object* v___y_5435_; uint32_t v___y_5436_; lean_object* v___y_5437_; lean_object* v___y_5438_; lean_object* v___y_5448_; uint8_t v___y_5449_; uint32_t v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v_a_5455_; lean_object* v___y_5551_; lean_object* v___y_5581_; 
v_kind_5394_ = lean_ctor_get_uint8(v_cfg_5370_, sizeof(void*)*3);
v_scope_5395_ = lean_ctor_get(v_cfg_5370_, 0);
lean_inc_ref(v_scope_5395_);
v_infos_5396_ = lean_ctor_get(v_cfg_5370_, 1);
lean_inc_ref(v_infos_5396_);
v_key_5397_ = lean_ctor_get(v_cfg_5370_, 2);
if (v_kind_5394_ == 0)
{
lean_object* v___x_5582_; lean_object* v___x_5583_; uint8_t v___x_5584_; 
v___x_5582_ = lean_unsigned_to_nat(0u);
v___x_5583_ = lean_array_get_size(v_infos_5396_);
v___x_5584_ = lean_nat_dec_lt(v___x_5582_, v___x_5583_);
if (v___x_5584_ == 0)
{
goto v___jp_5531_;
}
else
{
lean_object* v___x_5585_; uint8_t v___x_5586_; 
v___x_5585_ = lean_box(0);
v___x_5586_ = lean_nat_dec_le(v___x_5583_, v___x_5583_);
if (v___x_5586_ == 0)
{
if (v___x_5584_ == 0)
{
goto v___jp_5531_;
}
else
{
size_t v___x_5587_; size_t v___x_5588_; lean_object* v___x_5589_; 
v___x_5587_ = ((size_t)0ULL);
v___x_5588_ = lean_usize_of_nat(v___x_5583_);
v___x_5589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_5371_, v_infos_5396_, v___x_5587_, v___x_5588_, v___x_5585_, v___y_5373_);
v___y_5551_ = v___x_5589_;
goto v___jp_5550_;
}
}
else
{
size_t v___x_5590_; size_t v___x_5591_; lean_object* v___x_5592_; 
v___x_5590_ = ((size_t)0ULL);
v___x_5591_ = lean_usize_of_nat(v___x_5583_);
v___x_5592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__0(v_h_5371_, v_infos_5396_, v___x_5590_, v___x_5591_, v___x_5585_, v___y_5373_);
v___y_5551_ = v___x_5592_;
goto v___jp_5550_;
}
}
}
else
{
lean_object* v___x_5593_; lean_object* v___x_5594_; uint8_t v___x_5595_; 
v___x_5593_ = lean_unsigned_to_nat(0u);
v___x_5594_ = lean_array_get_size(v_infos_5396_);
v___x_5595_ = lean_nat_dec_lt(v___x_5593_, v___x_5594_);
if (v___x_5595_ == 0)
{
goto v___jp_5552_;
}
else
{
lean_object* v___x_5596_; uint8_t v___x_5597_; 
v___x_5596_ = lean_box(0);
v___x_5597_ = lean_nat_dec_le(v___x_5594_, v___x_5594_);
if (v___x_5597_ == 0)
{
if (v___x_5595_ == 0)
{
goto v___jp_5552_;
}
else
{
size_t v___x_5598_; size_t v___x_5599_; lean_object* v___x_5600_; 
v___x_5598_ = ((size_t)0ULL);
v___x_5599_ = lean_usize_of_nat(v___x_5594_);
v___x_5600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_5371_, v_infos_5396_, v___x_5598_, v___x_5599_, v___x_5596_, v___y_5373_);
v___y_5581_ = v___x_5600_;
goto v___jp_5580_;
}
}
else
{
size_t v___x_5601_; size_t v___x_5602_; lean_object* v___x_5603_; 
v___x_5601_ = ((size_t)0ULL);
v___x_5602_ = lean_usize_of_nat(v___x_5594_);
v___x_5603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__1(v_h_5371_, v_infos_5396_, v___x_5601_, v___x_5602_, v___x_5596_, v___y_5373_);
v___y_5581_ = v___x_5603_;
goto v___jp_5580_;
}
}
}
v___jp_5375_:
{
if (v___y_5376_ == 0)
{
lean_object* v___x_5377_; lean_object* v___x_5378_; 
v___x_5377_ = lean_box(0);
v___x_5378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5378_, 0, v___x_5377_);
return v___x_5378_;
}
else
{
lean_object* v___x_5379_; lean_object* v___x_5380_; 
v___x_5379_ = lean_box(0);
v___x_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5379_);
return v___x_5380_;
}
}
v___jp_5381_:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5386_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__0));
v___x_5387_ = lean_string_append(v___y_5385_, v___x_5386_);
v___x_5388_ = lean_uint32_to_nat(v___y_5384_);
v___x_5389_ = l_Nat_reprFast(v___x_5388_);
v___x_5390_ = lean_string_append(v___x_5387_, v___x_5389_);
lean_dec_ref(v___x_5389_);
v___x_5391_ = 3;
v___x_5392_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5392_, 0, v___x_5390_);
lean_ctor_set_uint8(v___x_5392_, sizeof(void*)*1, v___x_5391_);
lean_inc_ref(v___y_5383_);
v___x_5393_ = lean_apply_2(v___y_5383_, v___x_5392_, lean_box(0));
v___y_5376_ = v___y_5382_;
goto v___jp_5375_;
}
v___jp_5398_:
{
uint32_t v___x_5402_; uint8_t v___x_5403_; 
v___x_5402_ = 0;
v___x_5403_ = lean_uint32_dec_eq(v___y_5400_, v___x_5402_);
if (v___x_5403_ == 0)
{
lean_object* v_s_5404_; 
v_s_5404_ = lean_ctor_get(v_scope_5395_, 0);
lean_inc_ref(v_s_5404_);
lean_dec_ref(v_scope_5395_);
v___y_5382_ = v___y_5399_;
v___y_5383_ = v___y_5401_;
v___y_5384_ = v___y_5400_;
v___y_5385_ = v_s_5404_;
goto v___jp_5381_;
}
else
{
lean_dec_ref(v_scope_5395_);
v___y_5376_ = v___y_5399_;
goto v___jp_5375_;
}
}
v___jp_5405_:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; uint8_t v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; 
v___x_5413_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__1));
v___x_5414_ = lean_string_append(v___y_5412_, v___x_5413_);
lean_inc(v___y_5408_);
lean_inc(v___y_5406_);
lean_inc_ref(v___y_5411_);
v___x_5415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5415_, 0, v___y_5411_);
lean_ctor_set(v___x_5415_, 1, v___y_5406_);
lean_ctor_set(v___x_5415_, 2, v___y_5408_);
v___x_5416_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5415_, v___y_5408_);
lean_dec_ref(v___x_5415_);
v___x_5417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5417_, 0, v___y_5411_);
lean_ctor_set(v___x_5417_, 1, v___y_5406_);
lean_ctor_set(v___x_5417_, 2, v___x_5416_);
v___x_5418_ = l_String_Slice_toString(v___x_5417_);
lean_dec_ref(v___x_5417_);
v___x_5419_ = lean_string_append(v___x_5414_, v___x_5418_);
lean_dec_ref(v___x_5418_);
v___x_5420_ = 2;
v___x_5421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5421_, 0, v___x_5419_);
lean_ctor_set_uint8(v___x_5421_, sizeof(void*)*1, v___x_5420_);
lean_inc_ref(v___y_5409_);
v___x_5422_ = lean_apply_2(v___y_5409_, v___x_5421_, lean_box(0));
v___y_5399_ = v___y_5407_;
v___y_5400_ = v___y_5410_;
v___y_5401_ = v___y_5409_;
goto v___jp_5398_;
}
v___jp_5423_:
{
lean_object* v___x_5429_; uint8_t v___x_5430_; 
v___x_5429_ = lean_string_utf8_byte_size(v___y_5427_);
v___x_5430_ = lean_nat_dec_eq(v___x_5429_, v___y_5424_);
if (v___x_5430_ == 0)
{
lean_object* v_s_5431_; 
v_s_5431_ = lean_ctor_get(v_scope_5395_, 0);
lean_inc_ref(v_s_5431_);
v___y_5406_ = v___y_5424_;
v___y_5407_ = v___y_5425_;
v___y_5408_ = v___x_5429_;
v___y_5409_ = v___y_5428_;
v___y_5410_ = v___y_5426_;
v___y_5411_ = v___y_5427_;
v___y_5412_ = v_s_5431_;
goto v___jp_5405_;
}
else
{
lean_dec_ref(v___y_5427_);
lean_dec(v___y_5424_);
v___y_5399_ = v___y_5425_;
v___y_5400_ = v___y_5426_;
v___y_5401_ = v___y_5428_;
goto v___jp_5398_;
}
}
v___jp_5432_:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; uint8_t v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v___x_5439_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__6));
v___x_5440_ = lean_string_append(v___y_5438_, v___x_5439_);
v___x_5441_ = lean_string_append(v___x_5440_, v___y_5435_);
v___x_5442_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__2));
v___x_5443_ = lean_string_append(v___x_5441_, v___x_5442_);
v___x_5444_ = 3;
v___x_5445_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5445_, 0, v___x_5443_);
lean_ctor_set_uint8(v___x_5445_, sizeof(void*)*1, v___x_5444_);
lean_inc_ref(v___y_5373_);
v___x_5446_ = lean_apply_2(v___y_5373_, v___x_5445_, lean_box(0));
v___y_5424_ = v___y_5433_;
v___y_5425_ = v___y_5434_;
v___y_5426_ = v___y_5436_;
v___y_5427_ = v___y_5437_;
v___y_5428_ = v___y_5373_;
goto v___jp_5423_;
}
v___jp_5447_:
{
lean_object* v_s_5453_; 
v_s_5453_ = lean_ctor_get(v_scope_5395_, 0);
lean_inc_ref(v_s_5453_);
v___y_5433_ = v___y_5448_;
v___y_5434_ = v___y_5449_;
v___y_5435_ = v___y_5452_;
v___y_5436_ = v___y_5450_;
v___y_5437_ = v___y_5451_;
v___y_5438_ = v_s_5453_;
goto v___jp_5432_;
}
v___jp_5454_:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; uint8_t v___x_5461_; uint8_t v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; 
v___x_5456_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_5457_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
v___x_5458_ = lean_box(0);
v___x_5459_ = lean_unsigned_to_nat(0u);
v___x_5460_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_5461_ = 1;
v___x_5462_ = 0;
v___x_5463_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_5463_, 0, v___x_5456_);
lean_ctor_set(v___x_5463_, 1, v___x_5457_);
lean_ctor_set(v___x_5463_, 2, v_a_5455_);
lean_ctor_set(v___x_5463_, 3, v___x_5458_);
lean_ctor_set(v___x_5463_, 4, v___x_5460_);
lean_ctor_set_uint8(v___x_5463_, sizeof(void*)*5, v___x_5461_);
lean_ctor_set_uint8(v___x_5463_, sizeof(void*)*5 + 1, v___x_5462_);
v___x_5464_ = lean_io_process_spawn(v___x_5463_);
if (lean_obj_tag(v___x_5464_) == 0)
{
lean_object* v_a_5465_; lean_object* v_stdout_5466_; lean_object* v_stderr_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v_a_5465_ = lean_ctor_get(v___x_5464_, 0);
lean_inc(v_a_5465_);
lean_dec_ref(v___x_5464_);
v_stdout_5466_ = lean_ctor_get(v_a_5465_, 1);
lean_inc_n(v_stdout_5466_, 2);
v_stderr_5467_ = lean_ctor_get(v_a_5465_, 2);
v___x_5468_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__4));
v___x_5469_ = l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer(v_cfg_5370_, v_stderr_5467_, v_stdout_5466_, v___x_5468_, v___y_5373_);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v_a_5470_; lean_object* v___x_5471_; 
v_a_5470_ = lean_ctor_get(v___x_5469_, 0);
lean_inc(v_a_5470_);
lean_dec_ref(v___x_5469_);
v___x_5471_ = lean_io_process_child_wait(v___x_5456_, v_a_5465_);
lean_dec(v_a_5465_);
if (lean_obj_tag(v___x_5471_) == 0)
{
lean_object* v_a_5472_; lean_object* v___x_5473_; 
v_a_5472_ = lean_ctor_get(v___x_5471_, 0);
lean_inc(v_a_5472_);
lean_dec_ref(v___x_5471_);
v___x_5473_ = l_IO_FS_Handle_readToEnd(v_stdout_5466_);
lean_dec(v_stdout_5466_);
if (lean_obj_tag(v___x_5473_) == 0)
{
lean_object* v_a_5474_; uint8_t v_didError_5475_; lean_object* v_numSuccesses_5476_; lean_object* v___x_5477_; uint8_t v___x_5478_; 
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
lean_inc(v_a_5474_);
lean_dec_ref(v___x_5473_);
v_didError_5475_ = lean_ctor_get_uint8(v_a_5470_, sizeof(void*)*1);
v_numSuccesses_5476_ = lean_ctor_get(v_a_5470_, 0);
lean_inc(v_numSuccesses_5476_);
lean_dec(v_a_5470_);
v___x_5477_ = lean_array_get_size(v_infos_5396_);
lean_dec_ref(v_infos_5396_);
v___x_5478_ = lean_nat_dec_lt(v_numSuccesses_5476_, v___x_5477_);
lean_dec(v_numSuccesses_5476_);
if (v___x_5478_ == 0)
{
uint32_t v___x_5479_; 
v___x_5479_ = lean_unbox_uint32(v_a_5472_);
lean_dec(v_a_5472_);
v___y_5424_ = v___x_5459_;
v___y_5425_ = v_didError_5475_;
v___y_5426_ = v___x_5479_;
v___y_5427_ = v_a_5474_;
v___y_5428_ = v___y_5373_;
goto v___jp_5423_;
}
else
{
if (v_kind_5394_ == 0)
{
lean_object* v___x_5480_; uint32_t v___x_5481_; 
v___x_5480_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__10));
v___x_5481_ = lean_unbox_uint32(v_a_5472_);
lean_dec(v_a_5472_);
v___y_5448_ = v___x_5459_;
v___y_5449_ = v_didError_5475_;
v___y_5450_ = v___x_5481_;
v___y_5451_ = v_a_5474_;
v___y_5452_ = v___x_5480_;
goto v___jp_5447_;
}
else
{
lean_object* v___x_5482_; uint32_t v___x_5483_; 
v___x_5482_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__11));
v___x_5483_ = lean_unbox_uint32(v_a_5472_);
lean_dec(v_a_5472_);
v___y_5448_ = v___x_5459_;
v___y_5449_ = v_didError_5475_;
v___y_5450_ = v___x_5483_;
v___y_5451_ = v_a_5474_;
v___y_5452_ = v___x_5482_;
goto v___jp_5447_;
}
}
}
else
{
lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5496_; 
lean_dec(v_a_5472_);
lean_dec(v_a_5470_);
lean_dec_ref(v_infos_5396_);
lean_dec_ref(v_scope_5395_);
v_a_5484_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5486_ = v___x_5473_;
v_isShared_5487_ = v_isSharedCheck_5496_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5473_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5496_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5488_; uint8_t v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5494_; 
v___x_5488_ = lean_io_error_to_string(v_a_5484_);
v___x_5489_ = 3;
v___x_5490_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5490_, 0, v___x_5488_);
lean_ctor_set_uint8(v___x_5490_, sizeof(void*)*1, v___x_5489_);
lean_inc_ref(v___y_5373_);
v___x_5491_ = lean_apply_2(v___y_5373_, v___x_5490_, lean_box(0));
v___x_5492_ = lean_box(0);
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 0, v___x_5492_);
v___x_5494_ = v___x_5486_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v___x_5492_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
}
else
{
lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_a_5470_);
lean_dec(v_stdout_5466_);
lean_dec_ref(v_infos_5396_);
lean_dec_ref(v_scope_5395_);
v_a_5497_ = lean_ctor_get(v___x_5471_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5471_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5499_ = v___x_5471_;
v_isShared_5500_ = v_isSharedCheck_5509_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_dec(v___x_5471_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5509_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5501_; uint8_t v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5507_; 
v___x_5501_ = lean_io_error_to_string(v_a_5497_);
v___x_5502_ = 3;
v___x_5503_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5503_, 0, v___x_5501_);
lean_ctor_set_uint8(v___x_5503_, sizeof(void*)*1, v___x_5502_);
lean_inc_ref(v___y_5373_);
v___x_5504_ = lean_apply_2(v___y_5373_, v___x_5503_, lean_box(0));
v___x_5505_ = lean_box(0);
if (v_isShared_5500_ == 0)
{
lean_ctor_set(v___x_5499_, 0, v___x_5505_);
v___x_5507_ = v___x_5499_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v___x_5505_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
lean_dec(v_stdout_5466_);
lean_dec(v_a_5465_);
lean_dec_ref(v_infos_5396_);
lean_dec_ref(v_scope_5395_);
v_a_5510_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5469_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5469_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5530_; 
lean_dec_ref(v_infos_5396_);
lean_dec_ref(v_scope_5395_);
lean_dec_ref(v_cfg_5370_);
v_a_5518_ = lean_ctor_get(v___x_5464_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5464_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5520_ = v___x_5464_;
v_isShared_5521_ = v_isSharedCheck_5530_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5464_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5530_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5522_; uint8_t v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5528_; 
v___x_5522_ = lean_io_error_to_string(v_a_5518_);
v___x_5523_ = 3;
v___x_5524_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5524_, 0, v___x_5522_);
lean_ctor_set_uint8(v___x_5524_, sizeof(void*)*1, v___x_5523_);
lean_inc_ref(v___y_5373_);
v___x_5525_ = lean_apply_2(v___y_5373_, v___x_5524_, lean_box(0));
v___x_5526_ = lean_box(0);
if (v_isShared_5521_ == 0)
{
lean_ctor_set(v___x_5520_, 0, v___x_5526_);
v___x_5528_ = v___x_5520_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5526_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
v___jp_5531_:
{
lean_object* v___x_5532_; 
v___x_5532_ = lean_io_prim_handle_flush(v_h_5371_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; 
lean_dec_ref(v___x_5532_);
v___x_5533_ = lean_unsigned_to_nat(11u);
v___x_5534_ = lean_mk_empty_array_with_capacity(v___x_5533_);
lean_dec_ref(v___x_5534_);
v___x_5535_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__20);
v___x_5536_ = lean_array_push(v___x_5535_, v_path_5372_);
v_a_5455_ = v___x_5536_;
goto v___jp_5454_;
}
else
{
lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5549_; 
lean_dec_ref(v_infos_5396_);
lean_dec_ref(v_scope_5395_);
lean_dec_ref(v_path_5372_);
lean_dec_ref(v_cfg_5370_);
v_a_5537_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5539_ = v___x_5532_;
v_isShared_5540_ = v_isSharedCheck_5549_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v___x_5532_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5549_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5541_; uint8_t v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5547_; 
v___x_5541_ = lean_io_error_to_string(v_a_5537_);
v___x_5542_ = 3;
v___x_5543_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5543_, 0, v___x_5541_);
lean_ctor_set_uint8(v___x_5543_, sizeof(void*)*1, v___x_5542_);
lean_inc_ref(v___y_5373_);
v___x_5544_ = lean_apply_2(v___y_5373_, v___x_5543_, lean_box(0));
v___x_5545_ = lean_box(0);
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 0, v___x_5545_);
v___x_5547_ = v___x_5539_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5545_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
v___jp_5550_:
{
if (lean_obj_tag(v___y_5551_) == 0)
{
lean_dec_ref(v___y_5551_);
goto v___jp_5531_;
}
else
{
lean_dec_ref(v_infos_5396_);
lean_dec_ref(v_scope_5395_);
lean_dec_ref(v_path_5372_);
lean_dec_ref(v_cfg_5370_);
return v___y_5551_;
}
}
v___jp_5552_:
{
lean_object* v___x_5553_; 
v___x_5553_ = lean_io_prim_handle_flush(v_h_5371_);
if (lean_obj_tag(v___x_5553_) == 0)
{
lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
lean_dec_ref(v___x_5553_);
v___x_5554_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_5555_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_5556_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_5557_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__10));
v___x_5558_ = lean_unsigned_to_nat(17u);
v___x_5559_ = lean_mk_empty_array_with_capacity(v___x_5558_);
lean_dec_ref(v___x_5559_);
v___x_5560_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32, &l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__32);
lean_inc_ref(v_key_5397_);
v___x_5561_ = lean_array_push(v___x_5560_, v_key_5397_);
v___x_5562_ = lean_array_push(v___x_5561_, v___x_5554_);
v___x_5563_ = lean_array_push(v___x_5562_, v___x_5555_);
v___x_5564_ = lean_array_push(v___x_5563_, v___x_5556_);
v___x_5565_ = lean_array_push(v___x_5564_, v___x_5557_);
v___x_5566_ = lean_array_push(v___x_5565_, v_path_5372_);
v_a_5455_ = v___x_5566_;
goto v___jp_5454_;
}
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5579_; 
lean_dec_ref(v_infos_5396_);
lean_dec_ref(v_scope_5395_);
lean_dec_ref(v_path_5372_);
lean_dec_ref(v_cfg_5370_);
v_a_5567_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5569_ = v___x_5553_;
v_isShared_5570_ = v_isSharedCheck_5579_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5553_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5579_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5571_; uint8_t v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5577_; 
v___x_5571_ = lean_io_error_to_string(v_a_5567_);
v___x_5572_ = 3;
v___x_5573_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5573_, 0, v___x_5571_);
lean_ctor_set_uint8(v___x_5573_, sizeof(void*)*1, v___x_5572_);
lean_inc_ref(v___y_5373_);
v___x_5574_ = lean_apply_2(v___y_5373_, v___x_5573_, lean_box(0));
v___x_5575_ = lean_box(0);
if (v_isShared_5570_ == 0)
{
lean_ctor_set(v___x_5569_, 0, v___x_5575_);
v___x_5577_ = v___x_5569_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5575_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
}
v___jp_5580_:
{
if (lean_obj_tag(v___y_5581_) == 0)
{
lean_dec_ref(v___y_5581_);
goto v___jp_5552_;
}
else
{
lean_dec_ref(v_infos_5396_);
lean_dec_ref(v_scope_5395_);
lean_dec_ref(v_path_5372_);
lean_dec_ref(v_cfg_5370_);
return v___y_5581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed(lean_object* v_cfg_5604_, lean_object* v_h_5605_, lean_object* v_path_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_){
_start:
{
lean_object* v_res_5609_; 
v_res_5609_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0(v_cfg_5604_, v_h_5605_, v_path_5606_, v___y_5607_);
lean_dec_ref(v___y_5607_);
lean_dec(v_h_5605_);
return v_res_5609_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(lean_object* v_a_5610_, lean_object* v_cfg_5611_){
_start:
{
lean_object* v___f_5613_; lean_object* v___x_5614_; 
v___f_5613_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___lam__0___boxed), 5, 1);
lean_closure_set(v___f_5613_, 0, v_cfg_5611_);
v___x_5614_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5613_, v_a_5610_);
return v___x_5614_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0___boxed(lean_object* v_a_5615_, lean_object* v_cfg_5616_, lean_object* v_a_5617_){
_start:
{
lean_object* v_res_5618_; 
v_res_5618_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_5615_, v_cfg_5616_);
lean_dec_ref(v_a_5615_);
return v_res_5618_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0(lean_object* v_infos_5619_, lean_object* v_url_5620_, lean_object* v_h_5621_, lean_object* v_path_5622_, lean_object* v___y_5623_){
_start:
{
uint32_t v___y_5626_; lean_object* v___y_5627_; lean_object* v___y_5638_; lean_object* v___y_5639_; uint32_t v___y_5640_; lean_object* v___y_5641_; lean_object* v_a_5642_; lean_object* v___y_5670_; uint32_t v___y_5671_; uint8_t v___y_5672_; lean_object* v___y_5673_; lean_object* v_msg_5674_; lean_object* v___y_5675_; lean_object* v___y_5689_; lean_object* v___y_5690_; uint32_t v___y_5691_; uint8_t v___y_5692_; lean_object* v___y_5693_; lean_object* v_msg_5694_; lean_object* v___y_5695_; lean_object* v___y_5706_; lean_object* v___y_5707_; uint32_t v___y_5708_; lean_object* v___y_5709_; uint8_t v___y_5710_; lean_object* v___y_5711_; lean_object* v_msg_5712_; lean_object* v___y_5713_; lean_object* v___y_5726_; lean_object* v___y_5727_; uint32_t v___y_5728_; uint8_t v___y_5729_; lean_object* v___y_5730_; size_t v_sz_5748_; size_t v___x_5749_; lean_object* v___x_5750_; lean_object* v_body_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; 
v_sz_5748_ = lean_array_size(v_infos_5619_);
v___x_5749_ = ((size_t)0ULL);
lean_inc_ref(v_infos_5619_);
v___x_5750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__0(v_sz_5748_, v___x_5749_, v_infos_5619_);
v_body_5751_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_body_5751_, 0, v___x_5750_);
v___x_5752_ = l_Lean_Json_compress(v_body_5751_);
v___x_5753_ = lean_io_prim_handle_put_str(v_h_5621_, v___x_5752_);
lean_dec_ref(v___x_5752_);
if (lean_obj_tag(v___x_5753_) == 0)
{
lean_object* v___x_5754_; 
lean_dec_ref(v___x_5753_);
v___x_5754_ = lean_io_prim_handle_flush(v_h_5621_);
if (lean_obj_tag(v___x_5754_) == 0)
{
lean_object* v___y_5756_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; uint8_t v___x_5860_; 
lean_dec_ref(v___x_5754_);
v___x_5839_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__16));
v___x_5840_ = lean_string_append(v___x_5839_, v_path_5622_);
v___x_5841_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__8));
v___x_5842_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__9));
v___x_5843_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__10));
v___x_5844_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__11));
v___x_5845_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__12));
v___x_5846_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__19));
v___x_5847_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__17));
v___x_5848_ = lean_unsigned_to_nat(12u);
v___x_5849_ = lean_mk_empty_array_with_capacity(v___x_5848_);
lean_dec_ref(v___x_5849_);
v___x_5850_ = lean_obj_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__21);
v___x_5851_ = lean_array_push(v___x_5850_, v___x_5840_);
v___x_5852_ = lean_array_push(v___x_5851_, v___x_5841_);
v___x_5853_ = lean_array_push(v___x_5852_, v___x_5842_);
v___x_5854_ = lean_array_push(v___x_5853_, v___x_5843_);
v___x_5855_ = lean_array_push(v___x_5854_, v___x_5844_);
v___x_5856_ = lean_array_push(v___x_5855_, v___x_5845_);
v___x_5857_ = lean_array_push(v___x_5856_, v___x_5846_);
v___x_5858_ = lean_array_push(v___x_5857_, v___x_5847_);
v___x_5859_ = l_Lake_Reservoir_lakeHeaders;
v___x_5860_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__23);
if (v___x_5860_ == 0)
{
v___y_5756_ = v___x_5858_;
goto v___jp_5755_;
}
else
{
uint8_t v___x_5861_; 
v___x_5861_ = lean_uint8_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__24);
if (v___x_5861_ == 0)
{
if (v___x_5860_ == 0)
{
v___y_5756_ = v___x_5858_;
goto v___jp_5755_;
}
else
{
size_t v___x_5862_; lean_object* v___x_5863_; 
v___x_5862_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_5863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5859_, v___x_5749_, v___x_5862_, v___x_5858_);
v___y_5756_ = v___x_5863_;
goto v___jp_5755_;
}
}
else
{
size_t v___x_5864_; lean_object* v___x_5865_; 
v___x_5864_ = lean_usize_once(&l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25, &l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25_once, _init_l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__25);
v___x_5865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__3(v___x_5859_, v___x_5749_, v___x_5864_, v___x_5858_);
v___y_5756_ = v___x_5865_;
goto v___jp_5755_;
}
}
v___jp_5755_:
{
lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; uint8_t v___x_5763_; uint8_t v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; uint8_t v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; 
v___x_5757_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___lam__0___closed__3));
v___x_5758_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__9));
lean_inc_ref(v_url_5620_);
v___x_5759_ = lean_array_push(v___y_5756_, v_url_5620_);
v___x_5760_ = lean_box(0);
v___x_5761_ = lean_unsigned_to_nat(0u);
v___x_5762_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__27));
v___x_5763_ = 1;
v___x_5764_ = 0;
v___x_5765_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_5765_, 0, v___x_5757_);
lean_ctor_set(v___x_5765_, 1, v___x_5758_);
lean_ctor_set(v___x_5765_, 2, v___x_5759_);
lean_ctor_set(v___x_5765_, 3, v___x_5760_);
lean_ctor_set(v___x_5765_, 4, v___x_5762_);
lean_ctor_set_uint8(v___x_5765_, sizeof(void*)*5, v___x_5763_);
lean_ctor_set_uint8(v___x_5765_, sizeof(void*)*5 + 1, v___x_5764_);
lean_inc_ref(v___x_5765_);
v___x_5766_ = l_Lake_mkCmdLog(v___x_5765_);
v___x_5767_ = 0;
v___x_5768_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5768_, 0, v___x_5766_);
lean_ctor_set_uint8(v___x_5768_, sizeof(void*)*1, v___x_5767_);
lean_inc_ref(v___y_5623_);
v___x_5769_ = lean_apply_2(v___y_5623_, v___x_5768_, lean_box(0));
v___x_5770_ = l_IO_Process_output(v___x_5765_, v___x_5760_);
if (lean_obj_tag(v___x_5770_) == 0)
{
lean_object* v_a_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5825_; 
v_a_5771_ = lean_ctor_get(v___x_5770_, 0);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___x_5770_);
if (v_isSharedCheck_5825_ == 0)
{
v___x_5773_ = v___x_5770_;
v_isShared_5774_ = v_isSharedCheck_5825_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_a_5771_);
lean_dec(v___x_5770_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5825_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
uint32_t v_exitCode_5775_; lean_object* v_stdout_5776_; lean_object* v_stderr_5777_; lean_object* v___x_5778_; 
v_exitCode_5775_ = lean_ctor_get_uint32(v_a_5771_, sizeof(void*)*2);
v_stdout_5776_ = lean_ctor_get(v_a_5771_, 0);
lean_inc_ref_n(v_stdout_5776_, 2);
v_stderr_5777_ = lean_ctor_get(v_a_5771_, 1);
lean_inc_ref(v_stderr_5777_);
lean_dec(v_a_5771_);
v___x_5778_ = l_Lean_Json_parse(v_stdout_5776_);
if (lean_obj_tag(v___x_5778_) == 0)
{
lean_dec_ref(v___x_5778_);
lean_del_object(v___x_5773_);
lean_dec_ref(v_infos_5619_);
v___y_5726_ = v_stdout_5776_;
v___y_5727_ = v_stderr_5777_;
v___y_5728_ = v_exitCode_5775_;
v___y_5729_ = v___x_5767_;
v___y_5730_ = v___x_5761_;
goto v___jp_5725_;
}
else
{
lean_object* v_a_5779_; lean_object* v___x_5780_; 
v_a_5779_ = lean_ctor_get(v___x_5778_, 0);
lean_inc(v_a_5779_);
lean_dec_ref(v___x_5778_);
v___x_5780_ = l_Lake_ReservoirResp_fromJson_x3f___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__1(v_a_5779_);
if (lean_obj_tag(v___x_5780_) == 0)
{
lean_dec_ref(v___x_5780_);
lean_del_object(v___x_5773_);
lean_dec_ref(v_infos_5619_);
v___y_5726_ = v_stdout_5776_;
v___y_5727_ = v_stderr_5777_;
v___y_5728_ = v_exitCode_5775_;
v___y_5729_ = v___x_5767_;
v___y_5730_ = v___x_5761_;
goto v___jp_5725_;
}
else
{
lean_object* v_a_5781_; 
lean_dec_ref(v_stderr_5777_);
lean_dec_ref(v_stdout_5776_);
v_a_5781_ = lean_ctor_get(v___x_5780_, 0);
lean_inc(v_a_5781_);
lean_dec_ref(v___x_5780_);
if (lean_obj_tag(v_a_5781_) == 0)
{
lean_object* v_a_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; uint8_t v___x_5785_; 
v_a_5782_ = lean_ctor_get(v_a_5781_, 0);
lean_inc(v_a_5782_);
lean_dec_ref(v_a_5781_);
v___x_5783_ = lean_array_get_size(v_infos_5619_);
v___x_5784_ = lean_array_get_size(v_a_5782_);
v___x_5785_ = lean_nat_dec_eq(v___x_5783_, v___x_5784_);
if (v___x_5785_ == 0)
{
lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; uint8_t v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5801_; 
lean_dec(v_a_5782_);
lean_dec_ref(v_infos_5619_);
v___x_5786_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5787_ = lean_string_append(v___x_5786_, v_url_5620_);
lean_dec_ref(v_url_5620_);
v___x_5788_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__10));
v___x_5789_ = lean_string_append(v___x_5787_, v___x_5788_);
v___x_5790_ = l_Nat_reprFast(v___x_5783_);
v___x_5791_ = lean_string_append(v___x_5789_, v___x_5790_);
lean_dec_ref(v___x_5790_);
v___x_5792_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__11));
v___x_5793_ = lean_string_append(v___x_5791_, v___x_5792_);
v___x_5794_ = l_Nat_reprFast(v___x_5784_);
v___x_5795_ = lean_string_append(v___x_5793_, v___x_5794_);
lean_dec_ref(v___x_5794_);
v___x_5796_ = 3;
v___x_5797_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5797_, 0, v___x_5795_);
lean_ctor_set_uint8(v___x_5797_, sizeof(void*)*1, v___x_5796_);
lean_inc_ref(v___y_5623_);
v___x_5798_ = lean_apply_2(v___y_5623_, v___x_5797_, lean_box(0));
v___x_5799_ = lean_box(0);
if (v_isShared_5774_ == 0)
{
lean_ctor_set_tag(v___x_5773_, 1);
lean_ctor_set(v___x_5773_, 0, v___x_5799_);
v___x_5801_ = v___x_5773_;
goto v_reusejp_5800_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v___x_5799_);
v___x_5801_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5800_;
}
v_reusejp_5800_:
{
return v___x_5801_;
}
}
else
{
lean_object* v___x_5803_; lean_object* v___x_5805_; 
lean_dec_ref(v_url_5620_);
v___x_5803_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls_spec__2___redArg(v_a_5782_, v___x_5783_, v___x_5783_, v_infos_5619_);
lean_dec(v_a_5782_);
if (v_isShared_5774_ == 0)
{
lean_ctor_set(v___x_5773_, 0, v___x_5803_);
v___x_5805_ = v___x_5773_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v___x_5803_);
v___x_5805_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
return v___x_5805_;
}
}
}
else
{
lean_object* v_status_5807_; lean_object* v_message_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; uint8_t v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5823_; 
lean_dec_ref(v_infos_5619_);
v_status_5807_ = lean_ctor_get(v_a_5781_, 0);
lean_inc(v_status_5807_);
v_message_5808_ = lean_ctor_get(v_a_5781_, 1);
lean_inc_ref(v_message_5808_);
lean_dec_ref(v_a_5781_);
v___x_5809_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5810_ = l_Nat_reprFast(v_status_5807_);
v___x_5811_ = lean_string_append(v___x_5809_, v___x_5810_);
lean_dec_ref(v___x_5810_);
v___x_5812_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__12));
v___x_5813_ = lean_string_append(v___x_5811_, v___x_5812_);
v___x_5814_ = lean_string_append(v___x_5813_, v_url_5620_);
lean_dec_ref(v_url_5620_);
v___x_5815_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__13));
v___x_5816_ = lean_string_append(v___x_5814_, v___x_5815_);
v___x_5817_ = lean_string_append(v___x_5816_, v_message_5808_);
lean_dec_ref(v_message_5808_);
v___x_5818_ = 3;
v___x_5819_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5819_, 0, v___x_5817_);
lean_ctor_set_uint8(v___x_5819_, sizeof(void*)*1, v___x_5818_);
lean_inc_ref(v___y_5623_);
v___x_5820_ = lean_apply_2(v___y_5623_, v___x_5819_, lean_box(0));
v___x_5821_ = lean_box(0);
if (v_isShared_5774_ == 0)
{
lean_ctor_set_tag(v___x_5773_, 1);
lean_ctor_set(v___x_5773_, 0, v___x_5821_);
v___x_5823_ = v___x_5773_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v___x_5821_);
v___x_5823_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
return v___x_5823_;
}
}
}
}
}
}
else
{
lean_object* v_a_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5838_; 
lean_dec_ref(v_url_5620_);
lean_dec_ref(v_infos_5619_);
v_a_5826_ = lean_ctor_get(v___x_5770_, 0);
v_isSharedCheck_5838_ = !lean_is_exclusive(v___x_5770_);
if (v_isSharedCheck_5838_ == 0)
{
v___x_5828_ = v___x_5770_;
v_isShared_5829_ = v_isSharedCheck_5838_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_a_5826_);
lean_dec(v___x_5770_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5838_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v___x_5830_; uint8_t v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5836_; 
v___x_5830_ = lean_io_error_to_string(v_a_5826_);
v___x_5831_ = 3;
v___x_5832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5832_, 0, v___x_5830_);
lean_ctor_set_uint8(v___x_5832_, sizeof(void*)*1, v___x_5831_);
lean_inc_ref(v___y_5623_);
v___x_5833_ = lean_apply_2(v___y_5623_, v___x_5832_, lean_box(0));
v___x_5834_ = lean_box(0);
if (v_isShared_5829_ == 0)
{
lean_ctor_set(v___x_5828_, 0, v___x_5834_);
v___x_5836_ = v___x_5828_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5834_);
v___x_5836_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
return v___x_5836_;
}
}
}
}
}
else
{
lean_object* v_a_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5878_; 
lean_dec_ref(v_url_5620_);
lean_dec_ref(v_infos_5619_);
v_a_5866_ = lean_ctor_get(v___x_5754_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5754_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5868_ = v___x_5754_;
v_isShared_5869_ = v_isSharedCheck_5878_;
goto v_resetjp_5867_;
}
else
{
lean_inc(v_a_5866_);
lean_dec(v___x_5754_);
v___x_5868_ = lean_box(0);
v_isShared_5869_ = v_isSharedCheck_5878_;
goto v_resetjp_5867_;
}
v_resetjp_5867_:
{
lean_object* v___x_5870_; uint8_t v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5876_; 
v___x_5870_ = lean_io_error_to_string(v_a_5866_);
v___x_5871_ = 3;
v___x_5872_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5872_, 0, v___x_5870_);
lean_ctor_set_uint8(v___x_5872_, sizeof(void*)*1, v___x_5871_);
lean_inc_ref(v___y_5623_);
v___x_5873_ = lean_apply_2(v___y_5623_, v___x_5872_, lean_box(0));
v___x_5874_ = lean_box(0);
if (v_isShared_5869_ == 0)
{
lean_ctor_set(v___x_5868_, 0, v___x_5874_);
v___x_5876_ = v___x_5868_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v___x_5874_);
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
lean_object* v_a_5879_; lean_object* v___x_5881_; uint8_t v_isShared_5882_; uint8_t v_isSharedCheck_5891_; 
lean_dec_ref(v_url_5620_);
lean_dec_ref(v_infos_5619_);
v_a_5879_ = lean_ctor_get(v___x_5753_, 0);
v_isSharedCheck_5891_ = !lean_is_exclusive(v___x_5753_);
if (v_isSharedCheck_5891_ == 0)
{
v___x_5881_ = v___x_5753_;
v_isShared_5882_ = v_isSharedCheck_5891_;
goto v_resetjp_5880_;
}
else
{
lean_inc(v_a_5879_);
lean_dec(v___x_5753_);
v___x_5881_ = lean_box(0);
v_isShared_5882_ = v_isSharedCheck_5891_;
goto v_resetjp_5880_;
}
v_resetjp_5880_:
{
lean_object* v___x_5883_; uint8_t v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5889_; 
v___x_5883_ = lean_io_error_to_string(v_a_5879_);
v___x_5884_ = 3;
v___x_5885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5885_, 0, v___x_5883_);
lean_ctor_set_uint8(v___x_5885_, sizeof(void*)*1, v___x_5884_);
lean_inc_ref(v___y_5623_);
v___x_5886_ = lean_apply_2(v___y_5623_, v___x_5885_, lean_box(0));
v___x_5887_ = lean_box(0);
if (v_isShared_5882_ == 0)
{
lean_ctor_set(v___x_5881_, 0, v___x_5887_);
v___x_5889_ = v___x_5881_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5890_; 
v_reuseFailAlloc_5890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5890_, 0, v___x_5887_);
v___x_5889_ = v_reuseFailAlloc_5890_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
return v___x_5889_;
}
}
}
v___jp_5625_:
{
lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; uint8_t v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; 
v___x_5628_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__0));
v___x_5629_ = lean_uint32_to_nat(v___y_5626_);
v___x_5630_ = l_Nat_reprFast(v___x_5629_);
v___x_5631_ = lean_string_append(v___x_5628_, v___x_5630_);
lean_dec_ref(v___x_5630_);
v___x_5632_ = 3;
v___x_5633_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5633_, 0, v___x_5631_);
lean_ctor_set_uint8(v___x_5633_, sizeof(void*)*1, v___x_5632_);
lean_inc_ref(v___y_5627_);
v___x_5634_ = lean_apply_2(v___y_5627_, v___x_5633_, lean_box(0));
v___x_5635_ = lean_box(0);
v___x_5636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5635_);
return v___x_5636_;
}
v___jp_5637_:
{
lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; uint8_t v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; uint8_t v___x_5659_; 
v___x_5643_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__1));
v___x_5644_ = lean_string_append(v___x_5643_, v_url_5620_);
lean_dec_ref(v_url_5620_);
v___x_5645_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__2));
v___x_5646_ = lean_string_append(v___x_5644_, v___x_5645_);
v___x_5647_ = lean_string_append(v___x_5646_, v_a_5642_);
lean_dec_ref(v_a_5642_);
v___x_5648_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_spec__0___closed__2));
v___x_5649_ = lean_string_append(v___x_5647_, v___x_5648_);
v___x_5650_ = lean_string_utf8_byte_size(v___y_5639_);
lean_inc(v___y_5641_);
v___x_5651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5651_, 0, v___y_5639_);
lean_ctor_set(v___x_5651_, 1, v___y_5641_);
lean_ctor_set(v___x_5651_, 2, v___x_5650_);
v___x_5652_ = l_String_Slice_trimAscii(v___x_5651_);
v___x_5653_ = l_String_Slice_toString(v___x_5652_);
lean_dec_ref(v___x_5652_);
v___x_5654_ = lean_string_append(v___x_5649_, v___x_5653_);
lean_dec_ref(v___x_5653_);
v___x_5655_ = 3;
v___x_5656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5656_, 0, v___x_5654_);
lean_ctor_set_uint8(v___x_5656_, sizeof(void*)*1, v___x_5655_);
lean_inc_ref(v___y_5623_);
v___x_5657_ = lean_apply_2(v___y_5623_, v___x_5656_, lean_box(0));
v___x_5658_ = lean_string_utf8_byte_size(v___y_5638_);
v___x_5659_ = lean_nat_dec_eq(v___x_5658_, v___y_5641_);
if (v___x_5659_ == 0)
{
lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; uint8_t v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; 
v___x_5660_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__3));
lean_inc(v___y_5641_);
lean_inc_ref(v___y_5638_);
v___x_5661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5661_, 0, v___y_5638_);
lean_ctor_set(v___x_5661_, 1, v___y_5641_);
lean_ctor_set(v___x_5661_, 2, v___x_5658_);
v___x_5662_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5661_, v___x_5658_);
lean_dec_ref(v___x_5661_);
v___x_5663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5663_, 0, v___y_5638_);
lean_ctor_set(v___x_5663_, 1, v___y_5641_);
lean_ctor_set(v___x_5663_, 2, v___x_5662_);
v___x_5664_ = l_String_Slice_toString(v___x_5663_);
lean_dec_ref(v___x_5663_);
v___x_5665_ = lean_string_append(v___x_5660_, v___x_5664_);
lean_dec_ref(v___x_5664_);
v___x_5666_ = 2;
v___x_5667_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5667_, 0, v___x_5665_);
lean_ctor_set_uint8(v___x_5667_, sizeof(void*)*1, v___x_5666_);
lean_inc_ref(v___y_5623_);
v___x_5668_ = lean_apply_2(v___y_5623_, v___x_5667_, lean_box(0));
v___y_5626_ = v___y_5640_;
v___y_5627_ = v___y_5623_;
goto v___jp_5625_;
}
else
{
lean_dec(v___y_5641_);
lean_dec_ref(v___y_5638_);
v___y_5626_ = v___y_5640_;
v___y_5627_ = v___y_5623_;
goto v___jp_5625_;
}
}
v___jp_5669_:
{
uint8_t v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; 
v___x_5676_ = 3;
v___x_5677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5677_, 0, v_msg_5674_);
lean_ctor_set_uint8(v___x_5677_, sizeof(void*)*1, v___x_5676_);
lean_inc_ref_n(v___y_5675_, 2);
v___x_5678_ = lean_apply_2(v___y_5675_, v___x_5677_, lean_box(0));
v___x_5679_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__4));
v___x_5680_ = lean_string_utf8_byte_size(v___y_5670_);
lean_inc(v___y_5673_);
lean_inc_ref(v___y_5670_);
v___x_5681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5681_, 0, v___y_5670_);
lean_ctor_set(v___x_5681_, 1, v___y_5673_);
lean_ctor_set(v___x_5681_, 2, v___x_5680_);
v___x_5682_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5681_, v___x_5680_);
lean_dec_ref(v___x_5681_);
v___x_5683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5683_, 0, v___y_5670_);
lean_ctor_set(v___x_5683_, 1, v___y_5673_);
lean_ctor_set(v___x_5683_, 2, v___x_5682_);
v___x_5684_ = l_String_Slice_toString(v___x_5683_);
lean_dec_ref(v___x_5683_);
v___x_5685_ = lean_string_append(v___x_5679_, v___x_5684_);
lean_dec_ref(v___x_5684_);
v___x_5686_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
lean_ctor_set_uint8(v___x_5686_, sizeof(void*)*1, v___y_5672_);
v___x_5687_ = lean_apply_2(v___y_5675_, v___x_5686_, lean_box(0));
v___y_5626_ = v___y_5671_;
v___y_5627_ = v___y_5675_;
goto v___jp_5625_;
}
v___jp_5688_:
{
lean_object* v___x_5696_; uint8_t v___x_5697_; 
v___x_5696_ = lean_string_utf8_byte_size(v___y_5689_);
v___x_5697_ = lean_nat_dec_eq(v___x_5696_, v___y_5693_);
if (v___x_5697_ == 0)
{
lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; 
v___x_5698_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__5));
v___x_5699_ = lean_string_append(v_msg_5694_, v___x_5698_);
lean_inc_n(v___y_5693_, 2);
lean_inc_ref(v___y_5689_);
v___x_5700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5700_, 0, v___y_5689_);
lean_ctor_set(v___x_5700_, 1, v___y_5693_);
lean_ctor_set(v___x_5700_, 2, v___x_5696_);
v___x_5701_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure_spec__0(v___x_5700_, v___x_5696_);
lean_dec_ref(v___x_5700_);
v___x_5702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5702_, 0, v___y_5689_);
lean_ctor_set(v___x_5702_, 1, v___y_5693_);
lean_ctor_set(v___x_5702_, 2, v___x_5701_);
v___x_5703_ = l_String_Slice_toString(v___x_5702_);
lean_dec_ref(v___x_5702_);
v___x_5704_ = lean_string_append(v___x_5699_, v___x_5703_);
lean_dec_ref(v___x_5703_);
v___y_5670_ = v___y_5690_;
v___y_5671_ = v___y_5691_;
v___y_5672_ = v___y_5692_;
v___y_5673_ = v___y_5693_;
v_msg_5674_ = v___x_5704_;
v___y_5675_ = v___y_5695_;
goto v___jp_5669_;
}
else
{
lean_dec_ref(v___y_5689_);
v___y_5670_ = v___y_5690_;
v___y_5671_ = v___y_5691_;
v___y_5672_ = v___y_5692_;
v___y_5673_ = v___y_5693_;
v_msg_5674_ = v_msg_5694_;
v___y_5675_ = v___y_5695_;
goto v___jp_5669_;
}
}
v___jp_5705_:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; 
v___x_5714_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__6));
v___x_5715_ = lean_string_append(v_msg_5712_, v___x_5714_);
v___x_5716_ = lean_string_append(v___x_5715_, v_url_5620_);
lean_dec_ref(v_url_5620_);
v___x_5717_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__4));
v___x_5718_ = l_Lake_JsonObject_getJson_x3f(v___y_5711_, v___x_5717_);
lean_dec(v___y_5711_);
if (lean_obj_tag(v___x_5718_) == 0)
{
v___y_5689_ = v___y_5706_;
v___y_5690_ = v___y_5707_;
v___y_5691_ = v___y_5708_;
v___y_5692_ = v___y_5710_;
v___y_5693_ = v___y_5709_;
v_msg_5694_ = v___x_5716_;
v___y_5695_ = v___y_5713_;
goto v___jp_5688_;
}
else
{
lean_object* v_val_5719_; lean_object* v___x_5720_; 
v_val_5719_ = lean_ctor_get(v___x_5718_, 0);
lean_inc(v_val_5719_);
lean_dec_ref(v___x_5718_);
v___x_5720_ = l_Lean_Json_getStr_x3f(v_val_5719_);
if (lean_obj_tag(v___x_5720_) == 0)
{
lean_dec_ref(v___x_5720_);
v___y_5689_ = v___y_5706_;
v___y_5690_ = v___y_5707_;
v___y_5691_ = v___y_5708_;
v___y_5692_ = v___y_5710_;
v___y_5693_ = v___y_5709_;
v_msg_5694_ = v___x_5716_;
v___y_5695_ = v___y_5713_;
goto v___jp_5688_;
}
else
{
if (lean_obj_tag(v___x_5720_) == 1)
{
lean_object* v_a_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; 
v_a_5721_ = lean_ctor_get(v___x_5720_, 0);
lean_inc(v_a_5721_);
lean_dec_ref(v___x_5720_);
v___x_5722_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__7));
v___x_5723_ = lean_string_append(v___x_5716_, v___x_5722_);
v___x_5724_ = lean_string_append(v___x_5723_, v_a_5721_);
lean_dec(v_a_5721_);
v___y_5689_ = v___y_5706_;
v___y_5690_ = v___y_5707_;
v___y_5691_ = v___y_5708_;
v___y_5692_ = v___y_5710_;
v___y_5693_ = v___y_5709_;
v_msg_5694_ = v___x_5724_;
v___y_5695_ = v___y_5713_;
goto v___jp_5688_;
}
else
{
lean_dec_ref(v___x_5720_);
v___y_5689_ = v___y_5706_;
v___y_5690_ = v___y_5707_;
v___y_5691_ = v___y_5708_;
v___y_5692_ = v___y_5710_;
v___y_5693_ = v___y_5709_;
v_msg_5694_ = v___x_5716_;
v___y_5695_ = v___y_5713_;
goto v___jp_5688_;
}
}
}
}
v___jp_5725_:
{
lean_object* v___x_5731_; 
lean_inc_ref(v___y_5727_);
v___x_5731_ = l_Lean_Json_parse(v___y_5727_);
if (lean_obj_tag(v___x_5731_) == 0)
{
lean_object* v_a_5732_; 
v_a_5732_ = lean_ctor_get(v___x_5731_, 0);
lean_inc(v_a_5732_);
lean_dec_ref(v___x_5731_);
v___y_5638_ = v___y_5726_;
v___y_5639_ = v___y_5727_;
v___y_5640_ = v___y_5728_;
v___y_5641_ = v___y_5730_;
v_a_5642_ = v_a_5732_;
goto v___jp_5637_;
}
else
{
lean_object* v_a_5733_; lean_object* v___x_5734_; 
v_a_5733_ = lean_ctor_get(v___x_5731_, 0);
lean_inc(v_a_5733_);
lean_dec_ref(v___x_5731_);
v___x_5734_ = l_Lean_Json_getObj_x3f(v_a_5733_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v_a_5735_; 
v_a_5735_ = lean_ctor_get(v___x_5734_, 0);
lean_inc(v_a_5735_);
lean_dec_ref(v___x_5734_);
v___y_5638_ = v___y_5726_;
v___y_5639_ = v___y_5727_;
v___y_5640_ = v___y_5728_;
v___y_5641_ = v___y_5730_;
v_a_5642_ = v_a_5735_;
goto v___jp_5637_;
}
else
{
lean_object* v_a_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; 
v_a_5736_ = lean_ctor_get(v___x_5734_, 0);
lean_inc(v_a_5736_);
lean_dec_ref(v___x_5734_);
v___x_5737_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__8));
v___x_5738_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_uploadS3___closed__5));
v___x_5739_ = l_Lake_JsonObject_getJson_x3f(v_a_5736_, v___x_5738_);
if (lean_obj_tag(v___x_5739_) == 0)
{
v___y_5706_ = v___y_5726_;
v___y_5707_ = v___y_5727_;
v___y_5708_ = v___y_5728_;
v___y_5709_ = v___y_5730_;
v___y_5710_ = v___y_5729_;
v___y_5711_ = v_a_5736_;
v_msg_5712_ = v___x_5737_;
v___y_5713_ = v___y_5623_;
goto v___jp_5705_;
}
else
{
lean_object* v_val_5740_; lean_object* v___x_5741_; 
v_val_5740_ = lean_ctor_get(v___x_5739_, 0);
lean_inc(v_val_5740_);
lean_dec_ref(v___x_5739_);
v___x_5741_ = l_Lean_Json_getNat_x3f(v_val_5740_);
if (lean_obj_tag(v___x_5741_) == 0)
{
lean_dec_ref(v___x_5741_);
v___y_5706_ = v___y_5726_;
v___y_5707_ = v___y_5727_;
v___y_5708_ = v___y_5728_;
v___y_5709_ = v___y_5730_;
v___y_5710_ = v___y_5729_;
v___y_5711_ = v_a_5736_;
v_msg_5712_ = v___x_5737_;
v___y_5713_ = v___y_5623_;
goto v___jp_5705_;
}
else
{
if (lean_obj_tag(v___x_5741_) == 1)
{
lean_object* v_a_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v_a_5742_ = lean_ctor_get(v___x_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref(v___x_5741_);
v___x_5743_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___lam__0___closed__9));
v___x_5744_ = l_Nat_reprFast(v_a_5742_);
v___x_5745_ = lean_string_append(v___x_5743_, v___x_5744_);
lean_dec_ref(v___x_5744_);
v___x_5746_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_monitorTransfer_handleFailure___closed__9));
v___x_5747_ = lean_string_append(v___x_5745_, v___x_5746_);
v___y_5706_ = v___y_5726_;
v___y_5707_ = v___y_5727_;
v___y_5708_ = v___y_5728_;
v___y_5709_ = v___y_5730_;
v___y_5710_ = v___y_5729_;
v___y_5711_ = v_a_5736_;
v_msg_5712_ = v___x_5747_;
v___y_5713_ = v___y_5623_;
goto v___jp_5705_;
}
else
{
lean_dec_ref(v___x_5741_);
v___y_5706_ = v___y_5726_;
v___y_5707_ = v___y_5727_;
v___y_5708_ = v___y_5728_;
v___y_5709_ = v___y_5730_;
v___y_5710_ = v___y_5729_;
v___y_5711_ = v_a_5736_;
v_msg_5712_ = v___x_5737_;
v___y_5713_ = v___y_5623_;
goto v___jp_5705_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0___boxed(lean_object* v_infos_5892_, lean_object* v_url_5893_, lean_object* v_h_5894_, lean_object* v_path_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_){
_start:
{
lean_object* v_res_5898_; 
v_res_5898_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0(v_infos_5892_, v_url_5893_, v_h_5894_, v_path_5895_, v___y_5896_);
lean_dec_ref(v___y_5896_);
lean_dec_ref(v_path_5895_);
lean_dec(v_h_5894_);
return v_res_5898_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(lean_object* v_a_5899_, lean_object* v_url_5900_, lean_object* v_infos_5901_){
_start:
{
lean_object* v___f_5903_; lean_object* v___x_5904_; 
v___f_5903_ = lean_alloc_closure((void*)(l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5903_, 0, v_infos_5901_);
lean_closure_set(v___f_5903_, 1, v_url_5900_);
v___x_5904_ = l_IO_FS_withTempFile___at___00__private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts_spec__2___redArg(v___f_5903_, v_a_5899_);
return v___x_5904_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1___boxed(lean_object* v_a_5905_, lean_object* v_url_5906_, lean_object* v_infos_5907_, lean_object* v_a_5908_){
_start:
{
lean_object* v_res_5909_; 
v_res_5909_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_5905_, v_url_5906_, v_infos_5907_);
lean_dec_ref(v_a_5905_);
return v_res_5909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(lean_object* v_cache_5910_, lean_object* v_service_5911_, lean_object* v_scope_5912_, uint8_t v_force_5913_, lean_object* v_as_5914_, size_t v_i_5915_, size_t v_stop_5916_, lean_object* v_b_5917_, lean_object* v___y_5918_){
_start:
{
lean_object* v_a_5921_; uint8_t v___x_5925_; 
v___x_5925_ = lean_usize_dec_eq(v_i_5915_, v_stop_5916_);
if (v___x_5925_ == 0)
{
lean_object* v___x_5926_; lean_object* v___y_5928_; lean_object* v___y_5934_; uint8_t v_a_5935_; uint64_t v_hash_5936_; lean_object* v_ext_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___y_5941_; lean_object* v___x_5984_; lean_object* v___x_5985_; uint8_t v___x_5986_; 
v___x_5926_ = lean_array_uget_borrowed(v_as_5914_, v_i_5915_);
v_hash_5936_ = lean_ctor_get_uint64(v___x_5926_, sizeof(void*)*1);
v_ext_5937_ = lean_ctor_get(v___x_5926_, 0);
v___x_5938_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
lean_inc_ref(v_cache_5910_);
v___x_5939_ = l_System_FilePath_join(v_cache_5910_, v___x_5938_);
v___x_5984_ = lean_string_utf8_byte_size(v_ext_5937_);
v___x_5985_ = lean_unsigned_to_nat(0u);
v___x_5986_ = lean_nat_dec_eq(v___x_5984_, v___x_5985_);
if (v___x_5986_ == 0)
{
lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; 
v___x_5987_ = l_Lake_lowerHexUInt64(v_hash_5936_);
v___x_5988_ = ((lean_object*)(l_Lake_Cache_artifactPath___closed__0));
v___x_5989_ = lean_string_append(v___x_5987_, v___x_5988_);
v___x_5990_ = lean_string_append(v___x_5989_, v_ext_5937_);
v___y_5941_ = v___x_5990_;
goto v___jp_5940_;
}
else
{
lean_object* v___x_5991_; 
v___x_5991_ = l_Lake_lowerHexUInt64(v_hash_5936_);
v___y_5941_ = v___x_5991_;
goto v___jp_5940_;
}
v___jp_5927_:
{
uint64_t v_hash_5929_; lean_object* v_url_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; 
v_hash_5929_ = lean_ctor_get_uint64(v___x_5926_, sizeof(void*)*1);
lean_inc_ref(v_scope_5912_);
lean_inc_ref(v_service_5911_);
v_url_5930_ = l_Lake_CacheService_artifactUrl(v_hash_5929_, v_service_5911_, v_scope_5912_);
lean_inc(v___x_5926_);
v___x_5931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5931_, 0, v_url_5930_);
lean_ctor_set(v___x_5931_, 1, v___y_5928_);
lean_ctor_set(v___x_5931_, 2, v___x_5926_);
v___x_5932_ = lean_array_push(v_b_5917_, v___x_5931_);
v_a_5921_ = v___x_5932_;
goto v___jp_5920_;
}
v___jp_5933_:
{
if (v_a_5935_ == 0)
{
v___y_5928_ = v___y_5934_;
goto v___jp_5927_;
}
else
{
lean_dec_ref(v___y_5934_);
v_a_5921_ = v_b_5917_;
goto v___jp_5920_;
}
}
v___jp_5940_:
{
lean_object* v_path_5942_; 
v_path_5942_ = l_System_FilePath_join(v___x_5939_, v___y_5941_);
if (v_force_5913_ == 0)
{
uint8_t v___x_5943_; lean_object* v___x_5944_; uint8_t v___x_5945_; 
v___x_5943_ = l_System_FilePath_pathExists(v_path_5942_);
v___x_5944_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_5945_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_5945_ == 0)
{
v___y_5934_ = v_path_5942_;
v_a_5935_ = v___x_5943_;
goto v___jp_5933_;
}
else
{
lean_object* v___x_5946_; uint8_t v___x_5947_; 
v___x_5946_ = lean_box(0);
v___x_5947_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_5947_ == 0)
{
if (v___x_5945_ == 0)
{
v___y_5934_ = v_path_5942_;
v_a_5935_ = v___x_5943_;
goto v___jp_5933_;
}
else
{
size_t v___x_5948_; size_t v___x_5949_; lean_object* v___x_5950_; 
v___x_5948_ = ((size_t)0ULL);
v___x_5949_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_5950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_5944_, v___x_5948_, v___x_5949_, v___x_5946_, v___y_5918_);
if (lean_obj_tag(v___x_5950_) == 0)
{
lean_dec_ref(v___x_5950_);
v___y_5934_ = v_path_5942_;
v_a_5935_ = v___x_5943_;
goto v___jp_5933_;
}
else
{
lean_object* v_a_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5958_; 
lean_dec_ref(v_path_5942_);
lean_dec_ref(v_b_5917_);
lean_dec_ref(v_scope_5912_);
lean_dec_ref(v_service_5911_);
lean_dec_ref(v_cache_5910_);
v_a_5951_ = lean_ctor_get(v___x_5950_, 0);
v_isSharedCheck_5958_ = !lean_is_exclusive(v___x_5950_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5953_ = v___x_5950_;
v_isShared_5954_ = v_isSharedCheck_5958_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_a_5951_);
lean_dec(v___x_5950_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5958_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v___x_5956_; 
if (v_isShared_5954_ == 0)
{
v___x_5956_ = v___x_5953_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_a_5951_);
v___x_5956_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
return v___x_5956_;
}
}
}
}
}
else
{
size_t v___x_5959_; size_t v___x_5960_; lean_object* v___x_5961_; 
v___x_5959_ = ((size_t)0ULL);
v___x_5960_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_5961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_5944_, v___x_5959_, v___x_5960_, v___x_5946_, v___y_5918_);
if (lean_obj_tag(v___x_5961_) == 0)
{
lean_dec_ref(v___x_5961_);
v___y_5934_ = v_path_5942_;
v_a_5935_ = v___x_5943_;
goto v___jp_5933_;
}
else
{
lean_object* v_a_5962_; lean_object* v___x_5964_; uint8_t v_isShared_5965_; uint8_t v_isSharedCheck_5969_; 
lean_dec_ref(v_path_5942_);
lean_dec_ref(v_b_5917_);
lean_dec_ref(v_scope_5912_);
lean_dec_ref(v_service_5911_);
lean_dec_ref(v_cache_5910_);
v_a_5962_ = lean_ctor_get(v___x_5961_, 0);
v_isSharedCheck_5969_ = !lean_is_exclusive(v___x_5961_);
if (v_isSharedCheck_5969_ == 0)
{
v___x_5964_ = v___x_5961_;
v_isShared_5965_ = v_isSharedCheck_5969_;
goto v_resetjp_5963_;
}
else
{
lean_inc(v_a_5962_);
lean_dec(v___x_5961_);
v___x_5964_ = lean_box(0);
v_isShared_5965_ = v_isSharedCheck_5969_;
goto v_resetjp_5963_;
}
v_resetjp_5963_:
{
lean_object* v___x_5967_; 
if (v_isShared_5965_ == 0)
{
v___x_5967_ = v___x_5964_;
goto v_reusejp_5966_;
}
else
{
lean_object* v_reuseFailAlloc_5968_; 
v_reuseFailAlloc_5968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5968_, 0, v_a_5962_);
v___x_5967_ = v_reuseFailAlloc_5968_;
goto v_reusejp_5966_;
}
v_reusejp_5966_:
{
return v___x_5967_;
}
}
}
}
}
}
else
{
lean_object* v___x_5970_; 
v___x_5970_ = l_Lake_removeFileIfExists(v_path_5942_);
if (lean_obj_tag(v___x_5970_) == 0)
{
lean_dec_ref(v___x_5970_);
v___y_5928_ = v_path_5942_;
goto v___jp_5927_;
}
else
{
lean_object* v_a_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5983_; 
lean_dec_ref(v_path_5942_);
lean_dec_ref(v_b_5917_);
lean_dec_ref(v_scope_5912_);
lean_dec_ref(v_service_5911_);
lean_dec_ref(v_cache_5910_);
v_a_5971_ = lean_ctor_get(v___x_5970_, 0);
v_isSharedCheck_5983_ = !lean_is_exclusive(v___x_5970_);
if (v_isSharedCheck_5983_ == 0)
{
v___x_5973_ = v___x_5970_;
v_isShared_5974_ = v_isSharedCheck_5983_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_a_5971_);
lean_dec(v___x_5970_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5983_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5975_; uint8_t v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5981_; 
v___x_5975_ = lean_io_error_to_string(v_a_5971_);
v___x_5976_ = 3;
v___x_5977_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5977_, 0, v___x_5975_);
lean_ctor_set_uint8(v___x_5977_, sizeof(void*)*1, v___x_5976_);
lean_inc_ref(v___y_5918_);
v___x_5978_ = lean_apply_2(v___y_5918_, v___x_5977_, lean_box(0));
v___x_5979_ = lean_box(0);
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 0, v___x_5979_);
v___x_5981_ = v___x_5973_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v___x_5979_);
v___x_5981_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
return v___x_5981_;
}
}
}
}
}
}
else
{
lean_object* v___x_5992_; 
lean_dec_ref(v_scope_5912_);
lean_dec_ref(v_service_5911_);
lean_dec_ref(v_cache_5910_);
v___x_5992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5992_, 0, v_b_5917_);
return v___x_5992_;
}
v___jp_5920_:
{
size_t v___x_5922_; size_t v___x_5923_; 
v___x_5922_ = ((size_t)1ULL);
v___x_5923_ = lean_usize_add(v_i_5915_, v___x_5922_);
v_i_5915_ = v___x_5923_;
v_b_5917_ = v_a_5921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2___boxed(lean_object* v_cache_5993_, lean_object* v_service_5994_, lean_object* v_scope_5995_, lean_object* v_force_5996_, lean_object* v_as_5997_, lean_object* v_i_5998_, lean_object* v_stop_5999_, lean_object* v_b_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_){
_start:
{
uint8_t v_force_boxed_6003_; size_t v_i_boxed_6004_; size_t v_stop_boxed_6005_; lean_object* v_res_6006_; 
v_force_boxed_6003_ = lean_unbox(v_force_5996_);
v_i_boxed_6004_ = lean_unbox_usize(v_i_5998_);
lean_dec(v_i_5998_);
v_stop_boxed_6005_ = lean_unbox_usize(v_stop_5999_);
lean_dec(v_stop_5999_);
v_res_6006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_5993_, v_service_5994_, v_scope_5995_, v_force_boxed_6003_, v_as_5997_, v_i_boxed_6004_, v_stop_boxed_6005_, v_b_6000_, v___y_6001_);
lean_dec_ref(v___y_6001_);
lean_dec_ref(v_as_5997_);
return v_res_6006_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts(lean_object* v_descrs_6013_, lean_object* v_cache_6014_, lean_object* v_service_6015_, lean_object* v_scope_6016_, uint8_t v_force_6017_, lean_object* v_a_6018_){
_start:
{
lean_object* v_a_6021_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v_a_6045_; lean_object* v___y_6063_; uint8_t v___x_6073_; 
v___x_6042_ = lean_array_get_size(v_descrs_6013_);
v___x_6043_ = lean_unsigned_to_nat(0u);
v___x_6073_ = lean_nat_dec_eq(v___x_6042_, v___x_6043_);
if (v___x_6073_ == 0)
{
lean_object* v___x_6074_; uint8_t v___x_6075_; 
v___x_6074_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_6075_ = lean_nat_dec_lt(v___x_6043_, v___x_6042_);
if (v___x_6075_ == 0)
{
v_a_6045_ = v___x_6074_;
goto v___jp_6044_;
}
else
{
uint8_t v___x_6076_; 
v___x_6076_ = lean_nat_dec_le(v___x_6042_, v___x_6042_);
if (v___x_6076_ == 0)
{
if (v___x_6075_ == 0)
{
v_a_6045_ = v___x_6074_;
goto v___jp_6044_;
}
else
{
size_t v___x_6077_; size_t v___x_6078_; lean_object* v___x_6079_; 
v___x_6077_ = ((size_t)0ULL);
v___x_6078_ = lean_usize_of_nat(v___x_6042_);
lean_inc_ref(v_scope_6016_);
lean_inc_ref(v_service_6015_);
lean_inc_ref(v_cache_6014_);
v___x_6079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_6014_, v_service_6015_, v_scope_6016_, v_force_6017_, v_descrs_6013_, v___x_6077_, v___x_6078_, v___x_6074_, v_a_6018_);
v___y_6063_ = v___x_6079_;
goto v___jp_6062_;
}
}
else
{
size_t v___x_6080_; size_t v___x_6081_; lean_object* v___x_6082_; 
v___x_6080_ = ((size_t)0ULL);
v___x_6081_ = lean_usize_of_nat(v___x_6042_);
lean_inc_ref(v_scope_6016_);
lean_inc_ref(v_service_6015_);
lean_inc_ref(v_cache_6014_);
v___x_6082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_6014_, v_service_6015_, v_scope_6016_, v_force_6017_, v_descrs_6013_, v___x_6080_, v___x_6081_, v___x_6074_, v_a_6018_);
v___y_6063_ = v___x_6082_;
goto v___jp_6062_;
}
}
}
else
{
lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
lean_dec_ref(v_scope_6016_);
lean_dec_ref(v_service_6015_);
lean_dec_ref(v_cache_6014_);
v___x_6083_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__2));
lean_inc_ref(v_a_6018_);
v___x_6084_ = lean_apply_2(v_a_6018_, v___x_6083_, lean_box(0));
v___x_6085_ = lean_box(0);
v___x_6086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6085_);
return v___x_6086_;
}
v___jp_6020_:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; 
v___x_6022_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_6023_ = l_System_FilePath_join(v_cache_6014_, v___x_6022_);
v___x_6024_ = l_IO_FS_createDirAll(v___x_6023_);
if (lean_obj_tag(v___x_6024_) == 0)
{
uint8_t v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
lean_dec_ref(v___x_6024_);
v___x_6025_ = 0;
v___x_6026_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6027_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6027_, 0, v_scope_6016_);
lean_ctor_set(v___x_6027_, 1, v_a_6021_);
lean_ctor_set(v___x_6027_, 2, v___x_6026_);
lean_ctor_set_uint8(v___x_6027_, sizeof(void*)*3, v___x_6025_);
v___x_6028_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6018_, v___x_6027_);
return v___x_6028_;
}
else
{
lean_object* v_a_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6041_; 
lean_dec_ref(v_a_6021_);
lean_dec_ref(v_scope_6016_);
v_a_6029_ = lean_ctor_get(v___x_6024_, 0);
v_isSharedCheck_6041_ = !lean_is_exclusive(v___x_6024_);
if (v_isSharedCheck_6041_ == 0)
{
v___x_6031_ = v___x_6024_;
v_isShared_6032_ = v_isSharedCheck_6041_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_a_6029_);
lean_dec(v___x_6024_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6041_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6033_; uint8_t v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6039_; 
v___x_6033_ = lean_io_error_to_string(v_a_6029_);
v___x_6034_ = 3;
v___x_6035_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6035_, 0, v___x_6033_);
lean_ctor_set_uint8(v___x_6035_, sizeof(void*)*1, v___x_6034_);
lean_inc_ref(v_a_6018_);
v___x_6036_ = lean_apply_2(v_a_6018_, v___x_6035_, lean_box(0));
v___x_6037_ = lean_box(0);
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 0, v___x_6037_);
v___x_6039_ = v___x_6031_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6040_; 
v_reuseFailAlloc_6040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6040_, 0, v___x_6037_);
v___x_6039_ = v_reuseFailAlloc_6040_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
return v___x_6039_;
}
}
}
}
v___jp_6044_:
{
lean_object* v___x_6046_; uint8_t v___x_6047_; 
v___x_6046_ = lean_array_get_size(v_a_6045_);
v___x_6047_ = lean_nat_dec_eq(v___x_6046_, v___x_6043_);
if (v___x_6047_ == 0)
{
uint8_t v_isReservoir_6048_; 
v_isReservoir_6048_ = lean_ctor_get_uint8(v_service_6015_, sizeof(void*)*5);
if (v_isReservoir_6048_ == 0)
{
lean_dec_ref(v_service_6015_);
v_a_6021_ = v_a_6045_;
goto v___jp_6020_;
}
else
{
lean_object* v___x_6049_; lean_object* v___x_6050_; 
lean_inc_ref(v_scope_6016_);
v___x_6049_ = l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(v_service_6015_, v_scope_6016_);
v___x_6050_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6018_, v___x_6049_, v_a_6045_);
if (lean_obj_tag(v___x_6050_) == 0)
{
lean_object* v_a_6051_; 
v_a_6051_ = lean_ctor_get(v___x_6050_, 0);
lean_inc(v_a_6051_);
lean_dec_ref(v___x_6050_);
v_a_6021_ = v_a_6051_;
goto v___jp_6020_;
}
else
{
lean_object* v_a_6052_; lean_object* v___x_6054_; uint8_t v_isShared_6055_; uint8_t v_isSharedCheck_6059_; 
lean_dec_ref(v_scope_6016_);
lean_dec_ref(v_cache_6014_);
v_a_6052_ = lean_ctor_get(v___x_6050_, 0);
v_isSharedCheck_6059_ = !lean_is_exclusive(v___x_6050_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_6054_ = v___x_6050_;
v_isShared_6055_ = v_isSharedCheck_6059_;
goto v_resetjp_6053_;
}
else
{
lean_inc(v_a_6052_);
lean_dec(v___x_6050_);
v___x_6054_ = lean_box(0);
v_isShared_6055_ = v_isSharedCheck_6059_;
goto v_resetjp_6053_;
}
v_resetjp_6053_:
{
lean_object* v___x_6057_; 
if (v_isShared_6055_ == 0)
{
v___x_6057_ = v___x_6054_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6058_; 
v_reuseFailAlloc_6058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6058_, 0, v_a_6052_);
v___x_6057_ = v_reuseFailAlloc_6058_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
return v___x_6057_;
}
}
}
}
}
else
{
lean_object* v___x_6060_; lean_object* v___x_6061_; 
lean_dec_ref(v_a_6045_);
lean_dec_ref(v_scope_6016_);
lean_dec_ref(v_service_6015_);
lean_dec_ref(v_cache_6014_);
v___x_6060_ = lean_box(0);
v___x_6061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
return v___x_6061_;
}
}
v___jp_6062_:
{
if (lean_obj_tag(v___y_6063_) == 0)
{
lean_object* v_a_6064_; 
v_a_6064_ = lean_ctor_get(v___y_6063_, 0);
lean_inc(v_a_6064_);
lean_dec_ref(v___y_6063_);
v_a_6045_ = v_a_6064_;
goto v___jp_6044_;
}
else
{
lean_object* v_a_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6072_; 
lean_dec_ref(v_scope_6016_);
lean_dec_ref(v_service_6015_);
lean_dec_ref(v_cache_6014_);
v_a_6065_ = lean_ctor_get(v___y_6063_, 0);
v_isSharedCheck_6072_ = !lean_is_exclusive(v___y_6063_);
if (v_isSharedCheck_6072_ == 0)
{
v___x_6067_ = v___y_6063_;
v_isShared_6068_ = v_isSharedCheck_6072_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_a_6065_);
lean_dec(v___y_6063_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6072_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6070_; 
if (v_isShared_6068_ == 0)
{
v___x_6070_ = v___x_6067_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6071_; 
v_reuseFailAlloc_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6071_, 0, v_a_6065_);
v___x_6070_ = v_reuseFailAlloc_6071_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
return v___x_6070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___boxed(lean_object* v_descrs_6087_, lean_object* v_cache_6088_, lean_object* v_service_6089_, lean_object* v_scope_6090_, lean_object* v_force_6091_, lean_object* v_a_6092_, lean_object* v_a_6093_){
_start:
{
uint8_t v_force_boxed_6094_; lean_object* v_res_6095_; 
v_force_boxed_6094_ = lean_unbox(v_force_6091_);
v_res_6095_ = l_Lake_CacheService_downloadArtifacts(v_descrs_6087_, v_cache_6088_, v_service_6089_, v_scope_6090_, v_force_boxed_6094_, v_a_6092_);
lean_dec_ref(v_a_6092_);
lean_dec_ref(v_descrs_6087_);
return v_res_6095_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(lean_object* v_a_6096_, lean_object* v_descrs_6097_, lean_object* v_cache_6098_, lean_object* v_service_6099_, lean_object* v_scope_6100_, uint8_t v_force_6101_){
_start:
{
lean_object* v_a_6104_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v_a_6128_; lean_object* v___y_6146_; uint8_t v___x_6156_; 
v___x_6125_ = lean_array_get_size(v_descrs_6097_);
v___x_6126_ = lean_unsigned_to_nat(0u);
v___x_6156_ = lean_nat_dec_eq(v___x_6125_, v___x_6126_);
if (v___x_6156_ == 0)
{
lean_object* v___x_6157_; uint8_t v___x_6158_; 
v___x_6157_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
v___x_6158_ = lean_nat_dec_lt(v___x_6126_, v___x_6125_);
if (v___x_6158_ == 0)
{
v_a_6128_ = v___x_6157_;
goto v___jp_6127_;
}
else
{
uint8_t v___x_6159_; 
v___x_6159_ = lean_nat_dec_le(v___x_6125_, v___x_6125_);
if (v___x_6159_ == 0)
{
if (v___x_6158_ == 0)
{
v_a_6128_ = v___x_6157_;
goto v___jp_6127_;
}
else
{
size_t v___x_6160_; size_t v___x_6161_; lean_object* v___x_6162_; 
v___x_6160_ = ((size_t)0ULL);
v___x_6161_ = lean_usize_of_nat(v___x_6125_);
lean_inc_ref(v_scope_6100_);
lean_inc_ref(v_service_6099_);
lean_inc_ref(v_cache_6098_);
v___x_6162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_6098_, v_service_6099_, v_scope_6100_, v_force_6101_, v_descrs_6097_, v___x_6160_, v___x_6161_, v___x_6157_, v_a_6096_);
v___y_6146_ = v___x_6162_;
goto v___jp_6145_;
}
}
else
{
size_t v___x_6163_; size_t v___x_6164_; lean_object* v___x_6165_; 
v___x_6163_ = ((size_t)0ULL);
v___x_6164_ = lean_usize_of_nat(v___x_6125_);
lean_inc_ref(v_scope_6100_);
lean_inc_ref(v_service_6099_);
lean_inc_ref(v_cache_6098_);
v___x_6165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheService_downloadArtifacts_spec__2(v_cache_6098_, v_service_6099_, v_scope_6100_, v_force_6101_, v_descrs_6097_, v___x_6163_, v___x_6164_, v___x_6157_, v_a_6096_);
v___y_6146_ = v___x_6165_;
goto v___jp_6145_;
}
}
}
else
{
lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; 
lean_dec_ref(v_scope_6100_);
lean_dec_ref(v_service_6099_);
lean_dec_ref(v_cache_6098_);
v___x_6166_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__2));
lean_inc_ref(v_a_6096_);
v___x_6167_ = lean_apply_2(v_a_6096_, v___x_6166_, lean_box(0));
v___x_6168_ = lean_box(0);
v___x_6169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6169_, 0, v___x_6168_);
return v___x_6169_;
}
v___jp_6103_:
{
lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___x_6105_ = ((lean_object*)(l_Lake_Cache_artifactDir___closed__0));
v___x_6106_ = l_System_FilePath_join(v_cache_6098_, v___x_6105_);
v___x_6107_ = l_IO_FS_createDirAll(v___x_6106_);
if (lean_obj_tag(v___x_6107_) == 0)
{
uint8_t v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; 
lean_dec_ref(v___x_6107_);
v___x_6108_ = 0;
v___x_6109_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6110_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6110_, 0, v_scope_6100_);
lean_ctor_set(v___x_6110_, 1, v_a_6104_);
lean_ctor_set(v___x_6110_, 2, v___x_6109_);
lean_ctor_set_uint8(v___x_6110_, sizeof(void*)*3, v___x_6108_);
v___x_6111_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6096_, v___x_6110_);
return v___x_6111_;
}
else
{
lean_object* v_a_6112_; lean_object* v___x_6114_; uint8_t v_isShared_6115_; uint8_t v_isSharedCheck_6124_; 
lean_dec_ref(v_a_6104_);
lean_dec_ref(v_scope_6100_);
v_a_6112_ = lean_ctor_get(v___x_6107_, 0);
v_isSharedCheck_6124_ = !lean_is_exclusive(v___x_6107_);
if (v_isSharedCheck_6124_ == 0)
{
v___x_6114_ = v___x_6107_;
v_isShared_6115_ = v_isSharedCheck_6124_;
goto v_resetjp_6113_;
}
else
{
lean_inc(v_a_6112_);
lean_dec(v___x_6107_);
v___x_6114_ = lean_box(0);
v_isShared_6115_ = v_isSharedCheck_6124_;
goto v_resetjp_6113_;
}
v_resetjp_6113_:
{
lean_object* v___x_6116_; uint8_t v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6122_; 
v___x_6116_ = lean_io_error_to_string(v_a_6112_);
v___x_6117_ = 3;
v___x_6118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6118_, 0, v___x_6116_);
lean_ctor_set_uint8(v___x_6118_, sizeof(void*)*1, v___x_6117_);
lean_inc_ref(v_a_6096_);
v___x_6119_ = lean_apply_2(v_a_6096_, v___x_6118_, lean_box(0));
v___x_6120_ = lean_box(0);
if (v_isShared_6115_ == 0)
{
lean_ctor_set(v___x_6114_, 0, v___x_6120_);
v___x_6122_ = v___x_6114_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6123_; 
v_reuseFailAlloc_6123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6123_, 0, v___x_6120_);
v___x_6122_ = v_reuseFailAlloc_6123_;
goto v_reusejp_6121_;
}
v_reusejp_6121_:
{
return v___x_6122_;
}
}
}
}
v___jp_6127_:
{
lean_object* v___x_6129_; uint8_t v___x_6130_; 
v___x_6129_ = lean_array_get_size(v_a_6128_);
v___x_6130_ = lean_nat_dec_eq(v___x_6129_, v___x_6126_);
if (v___x_6130_ == 0)
{
uint8_t v_isReservoir_6131_; 
v_isReservoir_6131_ = lean_ctor_get_uint8(v_service_6099_, sizeof(void*)*5);
if (v_isReservoir_6131_ == 0)
{
lean_dec_ref(v_service_6099_);
v_a_6104_ = v_a_6128_;
goto v___jp_6103_;
}
else
{
lean_object* v___x_6132_; lean_object* v___x_6133_; 
lean_inc_ref(v_scope_6100_);
v___x_6132_ = l___private_Lake_Config_Cache_0__Lake_CacheService_reservoirArtifactsUrl(v_service_6099_, v_scope_6100_);
v___x_6133_ = l___private_Lake_Config_Cache_0__Lake_CacheService_downloadArtifacts_fetchUrls___at___00Lake_CacheService_downloadArtifacts_spec__1(v_a_6096_, v___x_6132_, v_a_6128_);
if (lean_obj_tag(v___x_6133_) == 0)
{
lean_object* v_a_6134_; 
v_a_6134_ = lean_ctor_get(v___x_6133_, 0);
lean_inc(v_a_6134_);
lean_dec_ref(v___x_6133_);
v_a_6104_ = v_a_6134_;
goto v___jp_6103_;
}
else
{
lean_object* v_a_6135_; lean_object* v___x_6137_; uint8_t v_isShared_6138_; uint8_t v_isSharedCheck_6142_; 
lean_dec_ref(v_scope_6100_);
lean_dec_ref(v_cache_6098_);
v_a_6135_ = lean_ctor_get(v___x_6133_, 0);
v_isSharedCheck_6142_ = !lean_is_exclusive(v___x_6133_);
if (v_isSharedCheck_6142_ == 0)
{
v___x_6137_ = v___x_6133_;
v_isShared_6138_ = v_isSharedCheck_6142_;
goto v_resetjp_6136_;
}
else
{
lean_inc(v_a_6135_);
lean_dec(v___x_6133_);
v___x_6137_ = lean_box(0);
v_isShared_6138_ = v_isSharedCheck_6142_;
goto v_resetjp_6136_;
}
v_resetjp_6136_:
{
lean_object* v___x_6140_; 
if (v_isShared_6138_ == 0)
{
v___x_6140_ = v___x_6137_;
goto v_reusejp_6139_;
}
else
{
lean_object* v_reuseFailAlloc_6141_; 
v_reuseFailAlloc_6141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6141_, 0, v_a_6135_);
v___x_6140_ = v_reuseFailAlloc_6141_;
goto v_reusejp_6139_;
}
v_reusejp_6139_:
{
return v___x_6140_;
}
}
}
}
}
else
{
lean_object* v___x_6143_; lean_object* v___x_6144_; 
lean_dec_ref(v_a_6128_);
lean_dec_ref(v_scope_6100_);
lean_dec_ref(v_service_6099_);
lean_dec_ref(v_cache_6098_);
v___x_6143_ = lean_box(0);
v___x_6144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6143_);
return v___x_6144_;
}
}
v___jp_6145_:
{
if (lean_obj_tag(v___y_6146_) == 0)
{
lean_object* v_a_6147_; 
v_a_6147_ = lean_ctor_get(v___y_6146_, 0);
lean_inc(v_a_6147_);
lean_dec_ref(v___y_6146_);
v_a_6128_ = v_a_6147_;
goto v___jp_6127_;
}
else
{
lean_object* v_a_6148_; lean_object* v___x_6150_; uint8_t v_isShared_6151_; uint8_t v_isSharedCheck_6155_; 
lean_dec_ref(v_scope_6100_);
lean_dec_ref(v_service_6099_);
lean_dec_ref(v_cache_6098_);
v_a_6148_ = lean_ctor_get(v___y_6146_, 0);
v_isSharedCheck_6155_ = !lean_is_exclusive(v___y_6146_);
if (v_isSharedCheck_6155_ == 0)
{
v___x_6150_ = v___y_6146_;
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
else
{
lean_inc(v_a_6148_);
lean_dec(v___y_6146_);
v___x_6150_ = lean_box(0);
v_isShared_6151_ = v_isSharedCheck_6155_;
goto v_resetjp_6149_;
}
v_resetjp_6149_:
{
lean_object* v___x_6153_; 
if (v_isShared_6151_ == 0)
{
v___x_6153_ = v___x_6150_;
goto v_reusejp_6152_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
v___x_6153_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6152_;
}
v_reusejp_6152_:
{
return v___x_6153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0___boxed(lean_object* v_a_6170_, lean_object* v_descrs_6171_, lean_object* v_cache_6172_, lean_object* v_service_6173_, lean_object* v_scope_6174_, lean_object* v_force_6175_, lean_object* v_a_6176_){
_start:
{
uint8_t v_force_boxed_6177_; lean_object* v_res_6178_; 
v_force_boxed_6177_ = lean_unbox(v_force_6175_);
v_res_6178_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6170_, v_descrs_6171_, v_cache_6172_, v_service_6173_, v_scope_6174_, v_force_boxed_6177_);
lean_dec_ref(v_descrs_6171_);
lean_dec_ref(v_a_6170_);
return v_res_6178_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts(lean_object* v_map_6179_, lean_object* v_cache_6180_, lean_object* v_service_6181_, lean_object* v_localScope_6182_, lean_object* v_remoteScope_6183_, uint8_t v_force_6184_, lean_object* v_a_6185_){
_start:
{
lean_object* v_name_x3f_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; 
v_name_x3f_6190_ = lean_ctor_get(v_service_6181_, 0);
lean_inc_ref(v_remoteScope_6183_);
v___x_6191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6191_, 0, v_remoteScope_6183_);
lean_inc(v_name_x3f_6190_);
lean_inc_ref(v_cache_6180_);
v___x_6192_ = l_Lake_Cache_writeMap(v_cache_6180_, v_localScope_6182_, v_map_6179_, v_name_x3f_6190_, v___x_6191_);
if (lean_obj_tag(v___x_6192_) == 0)
{
lean_object* v___x_6194_; uint8_t v_isShared_6195_; uint8_t v_isSharedCheck_6230_; 
v_isSharedCheck_6230_ = !lean_is_exclusive(v___x_6192_);
if (v_isSharedCheck_6230_ == 0)
{
lean_object* v_unused_6231_; 
v_unused_6231_ = lean_ctor_get(v___x_6192_, 0);
lean_dec(v_unused_6231_);
v___x_6194_ = v___x_6192_;
v_isShared_6195_ = v_isSharedCheck_6230_;
goto v_resetjp_6193_;
}
else
{
lean_dec(v___x_6192_);
v___x_6194_ = lean_box(0);
v_isShared_6195_ = v_isSharedCheck_6230_;
goto v_resetjp_6193_;
}
v_resetjp_6193_:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; 
v___x_6196_ = lean_unsigned_to_nat(0u);
v___x_6197_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6198_ = l_Lake_CacheMap_collectOutputDescrs(v_map_6179_, v___x_6197_);
if (lean_obj_tag(v___x_6198_) == 0)
{
lean_object* v_a_6199_; lean_object* v_a_6200_; lean_object* v___x_6201_; uint8_t v___x_6202_; 
lean_del_object(v___x_6194_);
v_a_6199_ = lean_ctor_get(v___x_6198_, 0);
lean_inc(v_a_6199_);
v_a_6200_ = lean_ctor_get(v___x_6198_, 1);
lean_inc(v_a_6200_);
lean_dec_ref(v___x_6198_);
v___x_6201_ = lean_array_get_size(v_a_6200_);
v___x_6202_ = lean_nat_dec_lt(v___x_6196_, v___x_6201_);
if (v___x_6202_ == 0)
{
lean_object* v___x_6203_; 
lean_dec(v_a_6200_);
v___x_6203_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6185_, v_a_6199_, v_cache_6180_, v_service_6181_, v_remoteScope_6183_, v_force_6184_);
lean_dec(v_a_6199_);
return v___x_6203_;
}
else
{
lean_object* v___x_6204_; uint8_t v___x_6205_; 
v___x_6204_ = lean_box(0);
v___x_6205_ = lean_nat_dec_le(v___x_6201_, v___x_6201_);
if (v___x_6205_ == 0)
{
if (v___x_6202_ == 0)
{
lean_object* v___x_6206_; 
lean_dec(v_a_6200_);
v___x_6206_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6185_, v_a_6199_, v_cache_6180_, v_service_6181_, v_remoteScope_6183_, v_force_6184_);
lean_dec(v_a_6199_);
return v___x_6206_;
}
else
{
size_t v___x_6207_; size_t v___x_6208_; lean_object* v___x_6209_; 
v___x_6207_ = ((size_t)0ULL);
v___x_6208_ = lean_usize_of_nat(v___x_6201_);
v___x_6209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6200_, v___x_6207_, v___x_6208_, v___x_6204_, v_a_6185_);
lean_dec(v_a_6200_);
if (lean_obj_tag(v___x_6209_) == 0)
{
lean_object* v___x_6210_; 
lean_dec_ref(v___x_6209_);
v___x_6210_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6185_, v_a_6199_, v_cache_6180_, v_service_6181_, v_remoteScope_6183_, v_force_6184_);
lean_dec(v_a_6199_);
return v___x_6210_;
}
else
{
lean_dec(v_a_6199_);
lean_dec_ref(v_remoteScope_6183_);
lean_dec_ref(v_service_6181_);
lean_dec_ref(v_cache_6180_);
return v___x_6209_;
}
}
}
else
{
size_t v___x_6211_; size_t v___x_6212_; lean_object* v___x_6213_; 
v___x_6211_ = ((size_t)0ULL);
v___x_6212_ = lean_usize_of_nat(v___x_6201_);
v___x_6213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6200_, v___x_6211_, v___x_6212_, v___x_6204_, v_a_6185_);
lean_dec(v_a_6200_);
if (lean_obj_tag(v___x_6213_) == 0)
{
lean_object* v___x_6214_; 
lean_dec_ref(v___x_6213_);
v___x_6214_ = l_Lake_CacheService_downloadArtifacts___at___00Lake_CacheService_downloadOutputArtifacts_spec__0(v_a_6185_, v_a_6199_, v_cache_6180_, v_service_6181_, v_remoteScope_6183_, v_force_6184_);
lean_dec(v_a_6199_);
return v___x_6214_;
}
else
{
lean_dec(v_a_6199_);
lean_dec_ref(v_remoteScope_6183_);
lean_dec_ref(v_service_6181_);
lean_dec_ref(v_cache_6180_);
return v___x_6213_;
}
}
}
}
else
{
lean_object* v_a_6215_; lean_object* v___x_6216_; uint8_t v___x_6217_; 
lean_dec_ref(v_remoteScope_6183_);
lean_dec_ref(v_service_6181_);
lean_dec_ref(v_cache_6180_);
v_a_6215_ = lean_ctor_get(v___x_6198_, 1);
lean_inc(v_a_6215_);
lean_dec_ref(v___x_6198_);
v___x_6216_ = lean_array_get_size(v_a_6215_);
v___x_6217_ = lean_nat_dec_lt(v___x_6196_, v___x_6216_);
if (v___x_6217_ == 0)
{
lean_object* v___x_6218_; lean_object* v___x_6220_; 
lean_dec(v_a_6215_);
v___x_6218_ = lean_box(0);
if (v_isShared_6195_ == 0)
{
lean_ctor_set_tag(v___x_6194_, 1);
lean_ctor_set(v___x_6194_, 0, v___x_6218_);
v___x_6220_ = v___x_6194_;
goto v_reusejp_6219_;
}
else
{
lean_object* v_reuseFailAlloc_6221_; 
v_reuseFailAlloc_6221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6221_, 0, v___x_6218_);
v___x_6220_ = v_reuseFailAlloc_6221_;
goto v_reusejp_6219_;
}
v_reusejp_6219_:
{
return v___x_6220_;
}
}
else
{
lean_object* v___x_6222_; uint8_t v___x_6223_; 
lean_del_object(v___x_6194_);
v___x_6222_ = lean_box(0);
v___x_6223_ = lean_nat_dec_le(v___x_6216_, v___x_6216_);
if (v___x_6223_ == 0)
{
if (v___x_6217_ == 0)
{
lean_dec(v_a_6215_);
goto v___jp_6187_;
}
else
{
size_t v___x_6224_; size_t v___x_6225_; lean_object* v___x_6226_; 
v___x_6224_ = ((size_t)0ULL);
v___x_6225_ = lean_usize_of_nat(v___x_6216_);
v___x_6226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6215_, v___x_6224_, v___x_6225_, v___x_6222_, v_a_6185_);
lean_dec(v_a_6215_);
if (lean_obj_tag(v___x_6226_) == 0)
{
lean_dec_ref(v___x_6226_);
goto v___jp_6187_;
}
else
{
return v___x_6226_;
}
}
}
else
{
size_t v___x_6227_; size_t v___x_6228_; lean_object* v___x_6229_; 
v___x_6227_ = ((size_t)0ULL);
v___x_6228_ = lean_usize_of_nat(v___x_6216_);
v___x_6229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6215_, v___x_6227_, v___x_6228_, v___x_6222_, v_a_6185_);
lean_dec(v_a_6215_);
if (lean_obj_tag(v___x_6229_) == 0)
{
lean_dec_ref(v___x_6229_);
goto v___jp_6187_;
}
else
{
return v___x_6229_;
}
}
}
}
}
}
else
{
lean_object* v_a_6232_; lean_object* v___x_6234_; uint8_t v_isShared_6235_; uint8_t v_isSharedCheck_6244_; 
lean_dec_ref(v_remoteScope_6183_);
lean_dec_ref(v_service_6181_);
lean_dec_ref(v_cache_6180_);
lean_dec_ref(v_map_6179_);
v_a_6232_ = lean_ctor_get(v___x_6192_, 0);
v_isSharedCheck_6244_ = !lean_is_exclusive(v___x_6192_);
if (v_isSharedCheck_6244_ == 0)
{
v___x_6234_ = v___x_6192_;
v_isShared_6235_ = v_isSharedCheck_6244_;
goto v_resetjp_6233_;
}
else
{
lean_inc(v_a_6232_);
lean_dec(v___x_6192_);
v___x_6234_ = lean_box(0);
v_isShared_6235_ = v_isSharedCheck_6244_;
goto v_resetjp_6233_;
}
v_resetjp_6233_:
{
lean_object* v___x_6236_; uint8_t v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6242_; 
v___x_6236_ = lean_io_error_to_string(v_a_6232_);
v___x_6237_ = 3;
v___x_6238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6238_, 0, v___x_6236_);
lean_ctor_set_uint8(v___x_6238_, sizeof(void*)*1, v___x_6237_);
lean_inc_ref(v_a_6185_);
v___x_6239_ = lean_apply_2(v_a_6185_, v___x_6238_, lean_box(0));
v___x_6240_ = lean_box(0);
if (v_isShared_6235_ == 0)
{
lean_ctor_set(v___x_6234_, 0, v___x_6240_);
v___x_6242_ = v___x_6234_;
goto v_reusejp_6241_;
}
else
{
lean_object* v_reuseFailAlloc_6243_; 
v_reuseFailAlloc_6243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6243_, 0, v___x_6240_);
v___x_6242_ = v_reuseFailAlloc_6243_;
goto v_reusejp_6241_;
}
v_reusejp_6241_:
{
return v___x_6242_;
}
}
}
v___jp_6187_:
{
lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6188_ = lean_box(0);
v___x_6189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6188_);
return v___x_6189_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadOutputArtifacts___boxed(lean_object* v_map_6245_, lean_object* v_cache_6246_, lean_object* v_service_6247_, lean_object* v_localScope_6248_, lean_object* v_remoteScope_6249_, lean_object* v_force_6250_, lean_object* v_a_6251_, lean_object* v_a_6252_){
_start:
{
uint8_t v_force_boxed_6253_; lean_object* v_res_6254_; 
v_force_boxed_6253_ = lean_unbox(v_force_6250_);
v_res_6254_ = l_Lake_CacheService_downloadOutputArtifacts(v_map_6245_, v_cache_6246_, v_service_6247_, v_localScope_6248_, v_remoteScope_6249_, v_force_boxed_6253_, v_a_6251_);
lean_dec_ref(v_a_6251_);
return v_res_6254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(lean_object* v_descrs_6255_, lean_object* v_service_6256_, lean_object* v_scope_6257_, lean_object* v_paths_6258_, lean_object* v_n_6259_, lean_object* v_i_6260_, lean_object* v_a_6261_){
_start:
{
lean_object* v_zero_6263_; uint8_t v_isZero_6264_; 
v_zero_6263_ = lean_unsigned_to_nat(0u);
v_isZero_6264_ = lean_nat_dec_eq(v_i_6260_, v_zero_6263_);
if (v_isZero_6264_ == 1)
{
lean_object* v___x_6265_; 
lean_dec(v_i_6260_);
lean_dec_ref(v_scope_6257_);
lean_dec_ref(v_service_6256_);
v___x_6265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6265_, 0, v_a_6261_);
return v___x_6265_;
}
else
{
lean_object* v_one_6266_; lean_object* v_n_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; uint64_t v_hash_6271_; lean_object* v_url_6272_; lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; 
v_one_6266_ = lean_unsigned_to_nat(1u);
v_n_6267_ = lean_nat_sub(v_i_6260_, v_one_6266_);
lean_dec(v_i_6260_);
v___x_6268_ = lean_nat_sub(v_n_6259_, v_n_6267_);
v___x_6269_ = lean_nat_sub(v___x_6268_, v_one_6266_);
lean_dec(v___x_6268_);
v___x_6270_ = lean_array_fget_borrowed(v_descrs_6255_, v___x_6269_);
v_hash_6271_ = lean_ctor_get_uint64(v___x_6270_, sizeof(void*)*1);
lean_inc_ref(v_scope_6257_);
lean_inc_ref(v_service_6256_);
v_url_6272_ = l_Lake_CacheService_artifactUrl(v_hash_6271_, v_service_6256_, v_scope_6257_);
v___x_6273_ = lean_array_fget_borrowed(v_paths_6258_, v___x_6269_);
lean_dec(v___x_6269_);
lean_inc(v___x_6270_);
lean_inc(v___x_6273_);
v___x_6274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6274_, 0, v_url_6272_);
lean_ctor_set(v___x_6274_, 1, v___x_6273_);
lean_ctor_set(v___x_6274_, 2, v___x_6270_);
v___x_6275_ = lean_array_push(v_a_6261_, v___x_6274_);
v_i_6260_ = v_n_6267_;
v_a_6261_ = v___x_6275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg___boxed(lean_object* v_descrs_6277_, lean_object* v_service_6278_, lean_object* v_scope_6279_, lean_object* v_paths_6280_, lean_object* v_n_6281_, lean_object* v_i_6282_, lean_object* v_a_6283_, lean_object* v___y_6284_){
_start:
{
lean_object* v_res_6285_; 
v_res_6285_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_descrs_6277_, v_service_6278_, v_scope_6279_, v_paths_6280_, v_n_6281_, v_i_6282_, v_a_6283_);
lean_dec(v_n_6281_);
lean_dec_ref(v_paths_6280_);
lean_dec_ref(v_descrs_6277_);
return v_res_6285_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts(lean_object* v_n_6290_, lean_object* v_descrs_6291_, lean_object* v_paths_6292_, lean_object* v_service_6293_, lean_object* v_scope_6294_, lean_object* v_a_6295_){
_start:
{
lean_object* v___x_6297_; uint8_t v___x_6298_; 
v___x_6297_ = lean_unsigned_to_nat(0u);
v___x_6298_ = lean_nat_dec_eq(v_n_6290_, v___x_6297_);
if (v___x_6298_ == 0)
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v_a_6301_; lean_object* v_key_6302_; uint8_t v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; 
v___x_6299_ = ((lean_object*)(l_Lake_CacheService_downloadArtifacts___closed__0));
lean_inc(v_n_6290_);
lean_inc_ref(v_scope_6294_);
lean_inc_ref(v_service_6293_);
v___x_6300_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_descrs_6291_, v_service_6293_, v_scope_6294_, v_paths_6292_, v_n_6290_, v_n_6290_, v___x_6299_);
lean_dec(v_n_6290_);
v_a_6301_ = lean_ctor_get(v___x_6300_, 0);
lean_inc(v_a_6301_);
lean_dec_ref(v___x_6300_);
v_key_6302_ = lean_ctor_get(v_service_6293_, 1);
lean_inc_ref(v_key_6302_);
lean_dec_ref(v_service_6293_);
v___x_6303_ = 1;
v___x_6304_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_6304_, 0, v_scope_6294_);
lean_ctor_set(v___x_6304_, 1, v_a_6301_);
lean_ctor_set(v___x_6304_, 2, v_key_6302_);
lean_ctor_set_uint8(v___x_6304_, sizeof(void*)*3, v___x_6303_);
v___x_6305_ = l___private_Lake_Config_Cache_0__Lake_CacheService_transferArtifacts___at___00Lake_CacheService_downloadArtifacts_spec__0(v_a_6295_, v___x_6304_);
return v___x_6305_;
}
else
{
lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; 
lean_dec_ref(v_scope_6294_);
lean_dec_ref(v_service_6293_);
lean_dec(v_n_6290_);
v___x_6306_ = ((lean_object*)(l_Lake_CacheService_uploadArtifacts___closed__1));
lean_inc_ref(v_a_6295_);
v___x_6307_ = lean_apply_2(v_a_6295_, v___x_6306_, lean_box(0));
v___x_6308_ = lean_box(0);
v___x_6309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6309_, 0, v___x_6308_);
return v___x_6309_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadArtifacts___boxed(lean_object* v_n_6310_, lean_object* v_descrs_6311_, lean_object* v_paths_6312_, lean_object* v_service_6313_, lean_object* v_scope_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_){
_start:
{
lean_object* v_res_6317_; 
v_res_6317_ = l_Lake_CacheService_uploadArtifacts(v_n_6310_, v_descrs_6311_, v_paths_6312_, v_service_6313_, v_scope_6314_, v_a_6315_);
lean_dec_ref(v_a_6315_);
lean_dec_ref(v_paths_6312_);
lean_dec_ref(v_descrs_6311_);
return v_res_6317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(lean_object* v_descrs_6318_, lean_object* v_service_6319_, lean_object* v_scope_6320_, lean_object* v_paths_6321_, lean_object* v_n_6322_, lean_object* v_i_6323_, lean_object* v_a_6324_, lean_object* v_a_6325_, lean_object* v___y_6326_){
_start:
{
lean_object* v___x_6328_; 
v___x_6328_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___redArg(v_descrs_6318_, v_service_6319_, v_scope_6320_, v_paths_6321_, v_n_6322_, v_i_6323_, v_a_6325_);
return v___x_6328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0___boxed(lean_object* v_descrs_6329_, lean_object* v_service_6330_, lean_object* v_scope_6331_, lean_object* v_paths_6332_, lean_object* v_n_6333_, lean_object* v_i_6334_, lean_object* v_a_6335_, lean_object* v_a_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_){
_start:
{
lean_object* v_res_6339_; 
v_res_6339_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lake_CacheService_uploadArtifacts_spec__0(v_descrs_6329_, v_service_6330_, v_scope_6331_, v_paths_6332_, v_n_6333_, v_i_6334_, v_a_6335_, v_a_6336_, v___y_6337_);
lean_dec_ref(v___y_6337_);
lean_dec(v_n_6333_);
lean_dec_ref(v_paths_6332_);
lean_dec_ref(v_descrs_6329_);
return v_res_6339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(lean_object* v_rev_6344_, lean_object* v_service_6345_, lean_object* v_scope_6346_, lean_object* v_platform_6347_, lean_object* v_toolchain_6348_){
_start:
{
lean_object* v_url_6350_; lean_object* v_url_6357_; 
if (lean_obj_tag(v_scope_6346_) == 0)
{
lean_object* v_s_6366_; lean_object* v_revisionEndpoint_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
lean_dec_ref(v_platform_6347_);
v_s_6366_ = lean_ctor_get(v_scope_6346_, 0);
lean_inc_ref(v_s_6366_);
lean_dec_ref(v_scope_6346_);
v_revisionEndpoint_6367_ = lean_ctor_get(v_service_6345_, 3);
lean_inc_ref(v_revisionEndpoint_6367_);
lean_dec_ref(v_service_6345_);
v___x_6368_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_6367_, v_s_6366_);
v___x_6369_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_6370_ = lean_string_append(v___x_6369_, v_rev_6344_);
v___x_6371_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_6372_ = lean_string_append(v___x_6370_, v___x_6371_);
v___x_6373_ = lean_string_append(v___x_6368_, v___x_6372_);
lean_dec_ref(v___x_6372_);
return v___x_6373_;
}
else
{
lean_object* v_s_6374_; lean_object* v_revisionEndpoint_6375_; lean_object* v_url_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; uint8_t v___x_6379_; 
v_s_6374_ = lean_ctor_get(v_scope_6346_, 0);
lean_inc_ref(v_s_6374_);
lean_dec_ref(v_scope_6346_);
v_revisionEndpoint_6375_ = lean_ctor_get(v_service_6345_, 3);
lean_inc_ref(v_revisionEndpoint_6375_);
lean_dec_ref(v_service_6345_);
v_url_6376_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v_revisionEndpoint_6375_, v_s_6374_);
v___x_6377_ = lean_string_utf8_byte_size(v_platform_6347_);
v___x_6378_ = lean_unsigned_to_nat(0u);
v___x_6379_ = lean_nat_dec_eq(v___x_6377_, v___x_6378_);
if (v___x_6379_ == 0)
{
lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v_url_6382_; 
v___x_6380_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__1));
v___x_6381_ = lean_string_append(v_url_6376_, v___x_6380_);
v_url_6382_ = l_Lake_uriEncode(v_platform_6347_, v___x_6381_);
v_url_6357_ = v_url_6382_;
goto v___jp_6356_;
}
else
{
lean_dec_ref(v_platform_6347_);
v_url_6357_ = v_url_6376_;
goto v___jp_6356_;
}
}
v___jp_6349_:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; 
v___x_6351_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3ArtifactUrl___closed__0));
v___x_6352_ = lean_string_append(v_url_6350_, v___x_6351_);
v___x_6353_ = lean_string_append(v___x_6352_, v_rev_6344_);
v___x_6354_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
v___x_6355_ = lean_string_append(v___x_6353_, v___x_6354_);
return v___x_6355_;
}
v___jp_6356_:
{
lean_object* v___x_6358_; lean_object* v___x_6359_; uint8_t v___x_6360_; 
v___x_6358_ = lean_string_utf8_byte_size(v_toolchain_6348_);
v___x_6359_ = lean_unsigned_to_nat(0u);
v___x_6360_ = lean_nat_dec_eq(v___x_6358_, v___x_6359_);
if (v___x_6360_ == 0)
{
lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v_url_6365_; 
v___x_6361_ = ((lean_object*)(l_Lake_instInhabitedCache_default___closed__0));
v___x_6362_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(v_toolchain_6348_, v___x_6361_, v___x_6359_);
v___x_6363_ = ((lean_object*)(l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___closed__0));
v___x_6364_ = lean_string_append(v_url_6357_, v___x_6363_);
v_url_6365_ = l_Lake_uriEncode(v___x_6362_, v___x_6364_);
v_url_6350_ = v_url_6365_;
goto v___jp_6349_;
}
else
{
v_url_6350_ = v_url_6357_;
goto v___jp_6349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl___boxed(lean_object* v_rev_6383_, lean_object* v_service_6384_, lean_object* v_scope_6385_, lean_object* v_platform_6386_, lean_object* v_toolchain_6387_){
_start:
{
lean_object* v_res_6388_; 
v_res_6388_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_6383_, v_service_6384_, v_scope_6385_, v_platform_6386_, v_toolchain_6387_);
lean_dec_ref(v_toolchain_6387_);
lean_dec_ref(v_rev_6383_);
return v_res_6388_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl(lean_object* v_rev_6392_, lean_object* v_service_6393_, lean_object* v_scope_6394_, lean_object* v_platform_6395_, lean_object* v_toolchain_6396_){
_start:
{
lean_object* v_url_6398_; lean_object* v___y_6406_; uint8_t v_isReservoir_6416_; 
v_isReservoir_6416_ = lean_ctor_get_uint8(v_service_6393_, sizeof(void*)*5);
if (v_isReservoir_6416_ == 0)
{
lean_object* v___x_6417_; 
v___x_6417_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_6392_, v_service_6393_, v_scope_6394_, v_platform_6395_, v_toolchain_6396_);
lean_dec_ref(v_toolchain_6396_);
return v___x_6417_;
}
else
{
if (lean_obj_tag(v_scope_6394_) == 0)
{
lean_object* v_apiEndpoint_6418_; lean_object* v_s_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; lean_object* v___x_6422_; 
v_apiEndpoint_6418_ = lean_ctor_get(v_service_6393_, 4);
lean_inc_ref(v_apiEndpoint_6418_);
lean_dec_ref(v_service_6393_);
v_s_6419_ = lean_ctor_get(v_scope_6394_, 0);
lean_inc_ref(v_s_6419_);
lean_dec_ref(v_scope_6394_);
v___x_6420_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__1));
v___x_6421_ = lean_string_append(v_apiEndpoint_6418_, v___x_6420_);
v___x_6422_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_6421_, v_s_6419_);
v___y_6406_ = v___x_6422_;
goto v___jp_6405_;
}
else
{
lean_object* v_apiEndpoint_6423_; lean_object* v_s_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; 
v_apiEndpoint_6423_ = lean_ctor_get(v_service_6393_, 4);
lean_inc_ref(v_apiEndpoint_6423_);
lean_dec_ref(v_service_6393_);
v_s_6424_ = lean_ctor_get(v_scope_6394_, 0);
lean_inc_ref(v_s_6424_);
lean_dec_ref(v_scope_6394_);
v___x_6425_ = ((lean_object*)(l_Lake_CacheService_artifactUrl___closed__2));
v___x_6426_ = lean_string_append(v_apiEndpoint_6423_, v___x_6425_);
v___x_6427_ = l___private_Lake_Config_Cache_0__Lake_CacheService_appendScope(v___x_6426_, v_s_6424_);
v___y_6406_ = v___x_6427_;
goto v___jp_6405_;
}
}
v___jp_6397_:
{
lean_object* v___x_6399_; lean_object* v___x_6400_; uint8_t v___x_6401_; 
v___x_6399_ = lean_string_utf8_byte_size(v_toolchain_6396_);
v___x_6400_ = lean_unsigned_to_nat(0u);
v___x_6401_ = lean_nat_dec_eq(v___x_6399_, v___x_6400_);
if (v___x_6401_ == 0)
{
lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v_url_6404_; 
v___x_6402_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__0));
v___x_6403_ = lean_string_append(v_url_6398_, v___x_6402_);
v_url_6404_ = l_Lake_uriEncode(v_toolchain_6396_, v___x_6403_);
return v_url_6404_;
}
else
{
lean_dec_ref(v_toolchain_6396_);
return v_url_6398_;
}
}
v___jp_6405_:
{
lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v_url_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; uint8_t v___x_6412_; 
v___x_6407_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__1));
v___x_6408_ = lean_string_append(v___y_6406_, v___x_6407_);
v_url_6409_ = lean_string_append(v___x_6408_, v_rev_6392_);
v___x_6410_ = lean_string_utf8_byte_size(v_platform_6395_);
v___x_6411_ = lean_unsigned_to_nat(0u);
v___x_6412_ = lean_nat_dec_eq(v___x_6410_, v___x_6411_);
if (v___x_6412_ == 0)
{
lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v_url_6415_; 
v___x_6413_ = ((lean_object*)(l_Lake_CacheService_revisionUrl___closed__2));
v___x_6414_ = lean_string_append(v_url_6409_, v___x_6413_);
v_url_6415_ = l_Lake_uriEncode(v_platform_6395_, v___x_6414_);
v_url_6398_ = v_url_6415_;
goto v___jp_6397_;
}
else
{
lean_dec_ref(v_platform_6395_);
v_url_6398_ = v_url_6409_;
goto v___jp_6397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_revisionUrl___boxed(lean_object* v_rev_6428_, lean_object* v_service_6429_, lean_object* v_scope_6430_, lean_object* v_platform_6431_, lean_object* v_toolchain_6432_){
_start:
{
lean_object* v_res_6433_; 
v_res_6433_ = l_Lake_CacheService_revisionUrl(v_rev_6428_, v_service_6429_, v_scope_6430_, v_platform_6431_, v_toolchain_6432_);
lean_dec_ref(v_rev_6428_);
return v_res_6433_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object* v_rev_6438_, lean_object* v_cache_6439_, lean_object* v_service_6440_, lean_object* v_localScope_6441_, lean_object* v_remoteScope_6442_, lean_object* v_platform_6443_, lean_object* v_toolchain_6444_, uint8_t v_force_6445_, lean_object* v_a_6446_){
_start:
{
lean_object* v_a_6452_; lean_object* v_a_6459_; lean_object* v___y_6463_; lean_object* v___y_6464_; lean_object* v_a_6472_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v_path_6481_; lean_object* v_a_6483_; lean_object* v___y_6585_; lean_object* v___y_6586_; uint8_t v___x_6635_; lean_object* v___x_6699_; uint8_t v___x_6700_; 
v___x_6476_ = ((lean_object*)(l_Lake_Cache_revisionDir___closed__0));
v___x_6477_ = l_System_FilePath_join(v_cache_6439_, v___x_6476_);
lean_inc_ref(v_localScope_6441_);
v___x_6478_ = l_System_FilePath_join(v___x_6477_, v_localScope_6441_);
v___x_6479_ = ((lean_object*)(l_Lake_Cache_revisionPath___closed__0));
lean_inc_ref(v_rev_6438_);
v___x_6480_ = lean_string_append(v_rev_6438_, v___x_6479_);
v_path_6481_ = l_System_FilePath_join(v___x_6478_, v___x_6480_);
v___x_6635_ = l_System_FilePath_pathExists(v_path_6481_);
v___x_6699_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6700_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__4, &l_Lake_CacheService_downloadArtifact___closed__4_once, _init_l_Lake_CacheService_downloadArtifact___closed__4);
if (v___x_6700_ == 0)
{
goto v___jp_6636_;
}
else
{
lean_object* v___x_6701_; uint8_t v___x_6702_; 
v___x_6701_ = lean_box(0);
v___x_6702_ = lean_uint8_once(&l_Lake_CacheService_downloadArtifact___closed__5, &l_Lake_CacheService_downloadArtifact___closed__5_once, _init_l_Lake_CacheService_downloadArtifact___closed__5);
if (v___x_6702_ == 0)
{
if (v___x_6700_ == 0)
{
goto v___jp_6636_;
}
else
{
size_t v___x_6703_; size_t v___x_6704_; lean_object* v___x_6705_; 
v___x_6703_ = ((size_t)0ULL);
v___x_6704_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6699_, v___x_6703_, v___x_6704_, v___x_6701_, v_a_6446_);
if (lean_obj_tag(v___x_6705_) == 0)
{
lean_dec_ref(v___x_6705_);
goto v___jp_6636_;
}
else
{
lean_object* v_a_6706_; lean_object* v___x_6708_; uint8_t v_isShared_6709_; uint8_t v_isSharedCheck_6713_; 
lean_dec_ref(v_path_6481_);
lean_dec_ref(v_toolchain_6444_);
lean_dec_ref(v_platform_6443_);
lean_dec_ref(v_remoteScope_6442_);
lean_dec_ref(v_localScope_6441_);
lean_dec_ref(v_service_6440_);
lean_dec_ref(v_rev_6438_);
v_a_6706_ = lean_ctor_get(v___x_6705_, 0);
v_isSharedCheck_6713_ = !lean_is_exclusive(v___x_6705_);
if (v_isSharedCheck_6713_ == 0)
{
v___x_6708_ = v___x_6705_;
v_isShared_6709_ = v_isSharedCheck_6713_;
goto v_resetjp_6707_;
}
else
{
lean_inc(v_a_6706_);
lean_dec(v___x_6705_);
v___x_6708_ = lean_box(0);
v_isShared_6709_ = v_isSharedCheck_6713_;
goto v_resetjp_6707_;
}
v_resetjp_6707_:
{
lean_object* v___x_6711_; 
if (v_isShared_6709_ == 0)
{
v___x_6711_ = v___x_6708_;
goto v_reusejp_6710_;
}
else
{
lean_object* v_reuseFailAlloc_6712_; 
v_reuseFailAlloc_6712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_a_6706_);
v___x_6711_ = v_reuseFailAlloc_6712_;
goto v_reusejp_6710_;
}
v_reusejp_6710_:
{
return v___x_6711_;
}
}
}
}
}
else
{
size_t v___x_6714_; size_t v___x_6715_; lean_object* v___x_6716_; 
v___x_6714_ = ((size_t)0ULL);
v___x_6715_ = lean_usize_once(&l_Lake_CacheService_downloadArtifact___closed__6, &l_Lake_CacheService_downloadArtifact___closed__6_once, _init_l_Lake_CacheService_downloadArtifact___closed__6);
v___x_6716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v___x_6699_, v___x_6714_, v___x_6715_, v___x_6701_, v_a_6446_);
if (lean_obj_tag(v___x_6716_) == 0)
{
lean_dec_ref(v___x_6716_);
goto v___jp_6636_;
}
else
{
lean_object* v_a_6717_; lean_object* v___x_6719_; uint8_t v_isShared_6720_; uint8_t v_isSharedCheck_6724_; 
lean_dec_ref(v_path_6481_);
lean_dec_ref(v_toolchain_6444_);
lean_dec_ref(v_platform_6443_);
lean_dec_ref(v_remoteScope_6442_);
lean_dec_ref(v_localScope_6441_);
lean_dec_ref(v_service_6440_);
lean_dec_ref(v_rev_6438_);
v_a_6717_ = lean_ctor_get(v___x_6716_, 0);
v_isSharedCheck_6724_ = !lean_is_exclusive(v___x_6716_);
if (v_isSharedCheck_6724_ == 0)
{
v___x_6719_ = v___x_6716_;
v_isShared_6720_ = v_isSharedCheck_6724_;
goto v_resetjp_6718_;
}
else
{
lean_inc(v_a_6717_);
lean_dec(v___x_6716_);
v___x_6719_ = lean_box(0);
v_isShared_6720_ = v_isSharedCheck_6724_;
goto v_resetjp_6718_;
}
v_resetjp_6718_:
{
lean_object* v___x_6722_; 
if (v_isShared_6720_ == 0)
{
v___x_6722_ = v___x_6719_;
goto v_reusejp_6721_;
}
else
{
lean_object* v_reuseFailAlloc_6723_; 
v_reuseFailAlloc_6723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6723_, 0, v_a_6717_);
v___x_6722_ = v_reuseFailAlloc_6723_;
goto v_reusejp_6721_;
}
v_reusejp_6721_:
{
return v___x_6722_;
}
}
}
}
}
v___jp_6448_:
{
lean_object* v___x_6449_; lean_object* v___x_6450_; 
v___x_6449_ = lean_box(0);
v___x_6450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6450_, 0, v___x_6449_);
return v___x_6450_;
}
v___jp_6451_:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; 
v___x_6453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6453_, 0, v_a_6452_);
v___x_6454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6454_, 0, v___x_6453_);
return v___x_6454_;
}
v___jp_6455_:
{
lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6456_ = lean_box(0);
v___x_6457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6457_, 0, v___x_6456_);
return v___x_6457_;
}
v___jp_6458_:
{
lean_object* v___x_6460_; lean_object* v___x_6461_; 
v___x_6460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6460_, 0, v_a_6459_);
v___x_6461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6461_, 0, v___x_6460_);
return v___x_6461_;
}
v___jp_6462_:
{
lean_object* v___x_6465_; lean_object* v___x_6466_; uint8_t v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; lean_object* v___x_6470_; 
v___x_6465_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__0));
v___x_6466_ = lean_string_append(v___y_6464_, v___x_6465_);
v___x_6467_ = 3;
v___x_6468_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6468_, 0, v___x_6466_);
lean_ctor_set_uint8(v___x_6468_, sizeof(void*)*1, v___x_6467_);
lean_inc_ref(v_a_6446_);
v___x_6469_ = lean_apply_2(v_a_6446_, v___x_6468_, lean_box(0));
v___x_6470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6470_, 0, v___y_6463_);
return v___x_6470_;
}
v___jp_6471_:
{
lean_object* v_s_6473_; 
v_s_6473_ = lean_ctor_get(v_remoteScope_6442_, 0);
lean_inc_ref(v_s_6473_);
lean_dec_ref(v_remoteScope_6442_);
v___y_6463_ = v_a_6472_;
v___y_6464_ = v_s_6473_;
goto v___jp_6462_;
}
v___jp_6474_:
{
lean_object* v___x_6475_; 
v___x_6475_ = lean_box(0);
v_a_6472_ = v___x_6475_;
goto v___jp_6471_;
}
v___jp_6482_:
{
if (lean_obj_tag(v_a_6483_) == 1)
{
lean_object* v_val_6484_; lean_object* v___x_6485_; 
v_val_6484_ = lean_ctor_get(v_a_6483_, 0);
lean_inc(v_val_6484_);
lean_dec_ref(v_a_6483_);
lean_inc_ref(v_path_6481_);
v___x_6485_ = l_Lake_createParentDirs(v_path_6481_);
if (lean_obj_tag(v___x_6485_) == 0)
{
lean_object* v___x_6486_; 
lean_dec_ref(v___x_6485_);
v___x_6486_ = l_IO_FS_writeFile(v_path_6481_, v_val_6484_);
lean_dec(v_val_6484_);
if (lean_obj_tag(v___x_6486_) == 0)
{
lean_object* v___x_6488_; uint8_t v_isShared_6489_; uint8_t v_isSharedCheck_6554_; 
v_isSharedCheck_6554_ = !lean_is_exclusive(v___x_6486_);
if (v_isSharedCheck_6554_ == 0)
{
lean_object* v_unused_6555_; 
v_unused_6555_ = lean_ctor_get(v___x_6486_, 0);
lean_dec(v_unused_6555_);
v___x_6488_ = v___x_6486_;
v_isShared_6489_ = v_isSharedCheck_6554_;
goto v_resetjp_6487_;
}
else
{
lean_dec(v___x_6486_);
v___x_6488_ = lean_box(0);
v_isShared_6489_ = v_isSharedCheck_6554_;
goto v_resetjp_6487_;
}
v_resetjp_6487_:
{
lean_object* v___x_6490_; lean_object* v___x_6491_; uint8_t v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6490_ = lean_string_utf8_byte_size(v_platform_6443_);
lean_dec_ref(v_platform_6443_);
v___x_6491_ = lean_unsigned_to_nat(0u);
v___x_6492_ = lean_nat_dec_eq(v___x_6490_, v___x_6491_);
v___x_6493_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6494_ = l_Lake_CacheMap_load(v_path_6481_, v___x_6492_, v___x_6493_);
if (lean_obj_tag(v___x_6494_) == 0)
{
lean_object* v_a_6495_; lean_object* v_a_6496_; lean_object* v___x_6497_; uint8_t v___x_6498_; 
lean_del_object(v___x_6488_);
v_a_6495_ = lean_ctor_get(v___x_6494_, 0);
lean_inc(v_a_6495_);
v_a_6496_ = lean_ctor_get(v___x_6494_, 1);
lean_inc(v_a_6496_);
lean_dec_ref(v___x_6494_);
v___x_6497_ = lean_array_get_size(v_a_6496_);
v___x_6498_ = lean_nat_dec_lt(v___x_6491_, v___x_6497_);
if (v___x_6498_ == 0)
{
lean_dec(v_a_6496_);
v_a_6459_ = v_a_6495_;
goto v___jp_6458_;
}
else
{
lean_object* v___x_6499_; uint8_t v___x_6500_; 
v___x_6499_ = lean_box(0);
v___x_6500_ = lean_nat_dec_le(v___x_6497_, v___x_6497_);
if (v___x_6500_ == 0)
{
if (v___x_6498_ == 0)
{
lean_dec(v_a_6496_);
v_a_6459_ = v_a_6495_;
goto v___jp_6458_;
}
else
{
size_t v___x_6501_; size_t v___x_6502_; lean_object* v___x_6503_; 
v___x_6501_ = ((size_t)0ULL);
v___x_6502_ = lean_usize_of_nat(v___x_6497_);
v___x_6503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6496_, v___x_6501_, v___x_6502_, v___x_6499_, v_a_6446_);
lean_dec(v_a_6496_);
if (lean_obj_tag(v___x_6503_) == 0)
{
lean_dec_ref(v___x_6503_);
v_a_6459_ = v_a_6495_;
goto v___jp_6458_;
}
else
{
lean_object* v_a_6504_; lean_object* v___x_6506_; uint8_t v_isShared_6507_; uint8_t v_isSharedCheck_6511_; 
lean_dec(v_a_6495_);
v_a_6504_ = lean_ctor_get(v___x_6503_, 0);
v_isSharedCheck_6511_ = !lean_is_exclusive(v___x_6503_);
if (v_isSharedCheck_6511_ == 0)
{
v___x_6506_ = v___x_6503_;
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
else
{
lean_inc(v_a_6504_);
lean_dec(v___x_6503_);
v___x_6506_ = lean_box(0);
v_isShared_6507_ = v_isSharedCheck_6511_;
goto v_resetjp_6505_;
}
v_resetjp_6505_:
{
lean_object* v___x_6509_; 
if (v_isShared_6507_ == 0)
{
v___x_6509_ = v___x_6506_;
goto v_reusejp_6508_;
}
else
{
lean_object* v_reuseFailAlloc_6510_; 
v_reuseFailAlloc_6510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_a_6504_);
v___x_6509_ = v_reuseFailAlloc_6510_;
goto v_reusejp_6508_;
}
v_reusejp_6508_:
{
return v___x_6509_;
}
}
}
}
}
else
{
size_t v___x_6512_; size_t v___x_6513_; lean_object* v___x_6514_; 
v___x_6512_ = ((size_t)0ULL);
v___x_6513_ = lean_usize_of_nat(v___x_6497_);
v___x_6514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6496_, v___x_6512_, v___x_6513_, v___x_6499_, v_a_6446_);
lean_dec(v_a_6496_);
if (lean_obj_tag(v___x_6514_) == 0)
{
lean_dec_ref(v___x_6514_);
v_a_6459_ = v_a_6495_;
goto v___jp_6458_;
}
else
{
lean_object* v_a_6515_; lean_object* v___x_6517_; uint8_t v_isShared_6518_; uint8_t v_isSharedCheck_6522_; 
lean_dec(v_a_6495_);
v_a_6515_ = lean_ctor_get(v___x_6514_, 0);
v_isSharedCheck_6522_ = !lean_is_exclusive(v___x_6514_);
if (v_isSharedCheck_6522_ == 0)
{
v___x_6517_ = v___x_6514_;
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
else
{
lean_inc(v_a_6515_);
lean_dec(v___x_6514_);
v___x_6517_ = lean_box(0);
v_isShared_6518_ = v_isSharedCheck_6522_;
goto v_resetjp_6516_;
}
v_resetjp_6516_:
{
lean_object* v___x_6520_; 
if (v_isShared_6518_ == 0)
{
v___x_6520_ = v___x_6517_;
goto v_reusejp_6519_;
}
else
{
lean_object* v_reuseFailAlloc_6521_; 
v_reuseFailAlloc_6521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6521_, 0, v_a_6515_);
v___x_6520_ = v_reuseFailAlloc_6521_;
goto v_reusejp_6519_;
}
v_reusejp_6519_:
{
return v___x_6520_;
}
}
}
}
}
}
else
{
lean_object* v_a_6523_; lean_object* v___x_6524_; uint8_t v___x_6525_; 
v_a_6523_ = lean_ctor_get(v___x_6494_, 1);
lean_inc(v_a_6523_);
lean_dec_ref(v___x_6494_);
v___x_6524_ = lean_array_get_size(v_a_6523_);
v___x_6525_ = lean_nat_dec_lt(v___x_6491_, v___x_6524_);
if (v___x_6525_ == 0)
{
lean_object* v___x_6526_; lean_object* v___x_6528_; 
lean_dec(v_a_6523_);
v___x_6526_ = lean_box(0);
if (v_isShared_6489_ == 0)
{
lean_ctor_set_tag(v___x_6488_, 1);
lean_ctor_set(v___x_6488_, 0, v___x_6526_);
v___x_6528_ = v___x_6488_;
goto v_reusejp_6527_;
}
else
{
lean_object* v_reuseFailAlloc_6529_; 
v_reuseFailAlloc_6529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6529_, 0, v___x_6526_);
v___x_6528_ = v_reuseFailAlloc_6529_;
goto v_reusejp_6527_;
}
v_reusejp_6527_:
{
return v___x_6528_;
}
}
else
{
lean_object* v___x_6530_; uint8_t v___x_6531_; 
lean_del_object(v___x_6488_);
v___x_6530_ = lean_box(0);
v___x_6531_ = lean_nat_dec_le(v___x_6524_, v___x_6524_);
if (v___x_6531_ == 0)
{
if (v___x_6525_ == 0)
{
lean_dec(v_a_6523_);
goto v___jp_6455_;
}
else
{
size_t v___x_6532_; size_t v___x_6533_; lean_object* v___x_6534_; 
v___x_6532_ = ((size_t)0ULL);
v___x_6533_ = lean_usize_of_nat(v___x_6524_);
v___x_6534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6523_, v___x_6532_, v___x_6533_, v___x_6530_, v_a_6446_);
lean_dec(v_a_6523_);
if (lean_obj_tag(v___x_6534_) == 0)
{
lean_dec_ref(v___x_6534_);
goto v___jp_6455_;
}
else
{
lean_object* v_a_6535_; lean_object* v___x_6537_; uint8_t v_isShared_6538_; uint8_t v_isSharedCheck_6542_; 
v_a_6535_ = lean_ctor_get(v___x_6534_, 0);
v_isSharedCheck_6542_ = !lean_is_exclusive(v___x_6534_);
if (v_isSharedCheck_6542_ == 0)
{
v___x_6537_ = v___x_6534_;
v_isShared_6538_ = v_isSharedCheck_6542_;
goto v_resetjp_6536_;
}
else
{
lean_inc(v_a_6535_);
lean_dec(v___x_6534_);
v___x_6537_ = lean_box(0);
v_isShared_6538_ = v_isSharedCheck_6542_;
goto v_resetjp_6536_;
}
v_resetjp_6536_:
{
lean_object* v___x_6540_; 
if (v_isShared_6538_ == 0)
{
v___x_6540_ = v___x_6537_;
goto v_reusejp_6539_;
}
else
{
lean_object* v_reuseFailAlloc_6541_; 
v_reuseFailAlloc_6541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6541_, 0, v_a_6535_);
v___x_6540_ = v_reuseFailAlloc_6541_;
goto v_reusejp_6539_;
}
v_reusejp_6539_:
{
return v___x_6540_;
}
}
}
}
}
else
{
size_t v___x_6543_; size_t v___x_6544_; lean_object* v___x_6545_; 
v___x_6543_ = ((size_t)0ULL);
v___x_6544_ = lean_usize_of_nat(v___x_6524_);
v___x_6545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6523_, v___x_6543_, v___x_6544_, v___x_6530_, v_a_6446_);
lean_dec(v_a_6523_);
if (lean_obj_tag(v___x_6545_) == 0)
{
lean_dec_ref(v___x_6545_);
goto v___jp_6455_;
}
else
{
lean_object* v_a_6546_; lean_object* v___x_6548_; uint8_t v_isShared_6549_; uint8_t v_isSharedCheck_6553_; 
v_a_6546_ = lean_ctor_get(v___x_6545_, 0);
v_isSharedCheck_6553_ = !lean_is_exclusive(v___x_6545_);
if (v_isSharedCheck_6553_ == 0)
{
v___x_6548_ = v___x_6545_;
v_isShared_6549_ = v_isSharedCheck_6553_;
goto v_resetjp_6547_;
}
else
{
lean_inc(v_a_6546_);
lean_dec(v___x_6545_);
v___x_6548_ = lean_box(0);
v_isShared_6549_ = v_isSharedCheck_6553_;
goto v_resetjp_6547_;
}
v_resetjp_6547_:
{
lean_object* v___x_6551_; 
if (v_isShared_6549_ == 0)
{
v___x_6551_ = v___x_6548_;
goto v_reusejp_6550_;
}
else
{
lean_object* v_reuseFailAlloc_6552_; 
v_reuseFailAlloc_6552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6552_, 0, v_a_6546_);
v___x_6551_ = v_reuseFailAlloc_6552_;
goto v_reusejp_6550_;
}
v_reusejp_6550_:
{
return v___x_6551_;
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
lean_object* v_a_6556_; lean_object* v___x_6558_; uint8_t v_isShared_6559_; uint8_t v_isSharedCheck_6568_; 
lean_dec_ref(v_path_6481_);
lean_dec_ref(v_platform_6443_);
v_a_6556_ = lean_ctor_get(v___x_6486_, 0);
v_isSharedCheck_6568_ = !lean_is_exclusive(v___x_6486_);
if (v_isSharedCheck_6568_ == 0)
{
v___x_6558_ = v___x_6486_;
v_isShared_6559_ = v_isSharedCheck_6568_;
goto v_resetjp_6557_;
}
else
{
lean_inc(v_a_6556_);
lean_dec(v___x_6486_);
v___x_6558_ = lean_box(0);
v_isShared_6559_ = v_isSharedCheck_6568_;
goto v_resetjp_6557_;
}
v_resetjp_6557_:
{
lean_object* v___x_6560_; uint8_t v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6566_; 
v___x_6560_ = lean_io_error_to_string(v_a_6556_);
v___x_6561_ = 3;
v___x_6562_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6562_, 0, v___x_6560_);
lean_ctor_set_uint8(v___x_6562_, sizeof(void*)*1, v___x_6561_);
lean_inc_ref(v_a_6446_);
v___x_6563_ = lean_apply_2(v_a_6446_, v___x_6562_, lean_box(0));
v___x_6564_ = lean_box(0);
if (v_isShared_6559_ == 0)
{
lean_ctor_set(v___x_6558_, 0, v___x_6564_);
v___x_6566_ = v___x_6558_;
goto v_reusejp_6565_;
}
else
{
lean_object* v_reuseFailAlloc_6567_; 
v_reuseFailAlloc_6567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6567_, 0, v___x_6564_);
v___x_6566_ = v_reuseFailAlloc_6567_;
goto v_reusejp_6565_;
}
v_reusejp_6565_:
{
return v___x_6566_;
}
}
}
}
else
{
lean_object* v_a_6569_; lean_object* v___x_6571_; uint8_t v_isShared_6572_; uint8_t v_isSharedCheck_6581_; 
lean_dec(v_val_6484_);
lean_dec_ref(v_path_6481_);
lean_dec_ref(v_platform_6443_);
v_a_6569_ = lean_ctor_get(v___x_6485_, 0);
v_isSharedCheck_6581_ = !lean_is_exclusive(v___x_6485_);
if (v_isSharedCheck_6581_ == 0)
{
v___x_6571_ = v___x_6485_;
v_isShared_6572_ = v_isSharedCheck_6581_;
goto v_resetjp_6570_;
}
else
{
lean_inc(v_a_6569_);
lean_dec(v___x_6485_);
v___x_6571_ = lean_box(0);
v_isShared_6572_ = v_isSharedCheck_6581_;
goto v_resetjp_6570_;
}
v_resetjp_6570_:
{
lean_object* v___x_6573_; uint8_t v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; lean_object* v___x_6579_; 
v___x_6573_ = lean_io_error_to_string(v_a_6569_);
v___x_6574_ = 3;
v___x_6575_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6575_, 0, v___x_6573_);
lean_ctor_set_uint8(v___x_6575_, sizeof(void*)*1, v___x_6574_);
lean_inc_ref(v_a_6446_);
v___x_6576_ = lean_apply_2(v_a_6446_, v___x_6575_, lean_box(0));
v___x_6577_ = lean_box(0);
if (v_isShared_6572_ == 0)
{
lean_ctor_set(v___x_6571_, 0, v___x_6577_);
v___x_6579_ = v___x_6571_;
goto v_reusejp_6578_;
}
else
{
lean_object* v_reuseFailAlloc_6580_; 
v_reuseFailAlloc_6580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6580_, 0, v___x_6577_);
v___x_6579_ = v_reuseFailAlloc_6580_;
goto v_reusejp_6578_;
}
v_reusejp_6578_:
{
return v___x_6579_;
}
}
}
}
else
{
lean_object* v___x_6582_; lean_object* v___x_6583_; 
lean_dec(v_a_6483_);
lean_dec_ref(v_path_6481_);
lean_dec_ref(v_platform_6443_);
v___x_6582_ = lean_box(0);
v___x_6583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6583_, 0, v___x_6582_);
return v___x_6583_;
}
}
v___jp_6584_:
{
lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; 
v___x_6587_ = lean_unsigned_to_nat(0u);
v___x_6588_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6589_ = l_Lake_getUrl_x3f(v___y_6585_, v___y_6586_, v___x_6588_);
if (lean_obj_tag(v___x_6589_) == 0)
{
lean_object* v_a_6590_; lean_object* v_a_6591_; lean_object* v___x_6592_; uint8_t v___x_6593_; 
v_a_6590_ = lean_ctor_get(v___x_6589_, 0);
lean_inc(v_a_6590_);
v_a_6591_ = lean_ctor_get(v___x_6589_, 1);
lean_inc(v_a_6591_);
lean_dec_ref(v___x_6589_);
v___x_6592_ = lean_array_get_size(v_a_6591_);
v___x_6593_ = lean_nat_dec_lt(v___x_6587_, v___x_6592_);
if (v___x_6593_ == 0)
{
lean_dec(v_a_6591_);
lean_dec_ref(v_remoteScope_6442_);
v_a_6483_ = v_a_6590_;
goto v___jp_6482_;
}
else
{
lean_object* v___x_6594_; uint8_t v___x_6595_; 
v___x_6594_ = lean_box(0);
v___x_6595_ = lean_nat_dec_le(v___x_6592_, v___x_6592_);
if (v___x_6595_ == 0)
{
if (v___x_6593_ == 0)
{
lean_dec(v_a_6591_);
lean_dec_ref(v_remoteScope_6442_);
v_a_6483_ = v_a_6590_;
goto v___jp_6482_;
}
else
{
size_t v___x_6596_; size_t v___x_6597_; lean_object* v___x_6598_; 
v___x_6596_ = ((size_t)0ULL);
v___x_6597_ = lean_usize_of_nat(v___x_6592_);
v___x_6598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6591_, v___x_6596_, v___x_6597_, v___x_6594_, v_a_6446_);
lean_dec(v_a_6591_);
if (lean_obj_tag(v___x_6598_) == 0)
{
lean_dec_ref(v___x_6598_);
lean_dec_ref(v_remoteScope_6442_);
v_a_6483_ = v_a_6590_;
goto v___jp_6482_;
}
else
{
lean_object* v_a_6599_; 
lean_dec(v_a_6590_);
lean_dec_ref(v_path_6481_);
lean_dec_ref(v_platform_6443_);
v_a_6599_ = lean_ctor_get(v___x_6598_, 0);
lean_inc(v_a_6599_);
lean_dec_ref(v___x_6598_);
v_a_6472_ = v_a_6599_;
goto v___jp_6471_;
}
}
}
else
{
size_t v___x_6600_; size_t v___x_6601_; lean_object* v___x_6602_; 
v___x_6600_ = ((size_t)0ULL);
v___x_6601_ = lean_usize_of_nat(v___x_6592_);
v___x_6602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6591_, v___x_6600_, v___x_6601_, v___x_6594_, v_a_6446_);
lean_dec(v_a_6591_);
if (lean_obj_tag(v___x_6602_) == 0)
{
lean_dec_ref(v___x_6602_);
lean_dec_ref(v_remoteScope_6442_);
v_a_6483_ = v_a_6590_;
goto v___jp_6482_;
}
else
{
lean_object* v_a_6603_; 
lean_dec(v_a_6590_);
lean_dec_ref(v_path_6481_);
lean_dec_ref(v_platform_6443_);
v_a_6603_ = lean_ctor_get(v___x_6602_, 0);
lean_inc(v_a_6603_);
lean_dec_ref(v___x_6602_);
v_a_6472_ = v_a_6603_;
goto v___jp_6471_;
}
}
}
}
else
{
lean_object* v_a_6604_; lean_object* v___x_6605_; uint8_t v___x_6606_; 
lean_dec_ref(v_path_6481_);
lean_dec_ref(v_platform_6443_);
v_a_6604_ = lean_ctor_get(v___x_6589_, 1);
lean_inc(v_a_6604_);
lean_dec_ref(v___x_6589_);
v___x_6605_ = lean_array_get_size(v_a_6604_);
v___x_6606_ = lean_nat_dec_lt(v___x_6587_, v___x_6605_);
if (v___x_6606_ == 0)
{
lean_object* v___x_6607_; 
lean_dec(v_a_6604_);
v___x_6607_ = lean_box(0);
v_a_6472_ = v___x_6607_;
goto v___jp_6471_;
}
else
{
lean_object* v___x_6608_; uint8_t v___x_6609_; 
v___x_6608_ = lean_box(0);
v___x_6609_ = lean_nat_dec_le(v___x_6605_, v___x_6605_);
if (v___x_6609_ == 0)
{
if (v___x_6606_ == 0)
{
lean_dec(v_a_6604_);
goto v___jp_6474_;
}
else
{
size_t v___x_6610_; size_t v___x_6611_; lean_object* v___x_6612_; 
v___x_6610_ = ((size_t)0ULL);
v___x_6611_ = lean_usize_of_nat(v___x_6605_);
v___x_6612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6604_, v___x_6610_, v___x_6611_, v___x_6608_, v_a_6446_);
lean_dec(v_a_6604_);
if (lean_obj_tag(v___x_6612_) == 0)
{
lean_dec_ref(v___x_6612_);
goto v___jp_6474_;
}
else
{
lean_object* v_a_6613_; 
v_a_6613_ = lean_ctor_get(v___x_6612_, 0);
lean_inc(v_a_6613_);
lean_dec_ref(v___x_6612_);
v_a_6472_ = v_a_6613_;
goto v___jp_6471_;
}
}
}
else
{
size_t v___x_6614_; size_t v___x_6615_; lean_object* v___x_6616_; 
v___x_6614_ = ((size_t)0ULL);
v___x_6615_ = lean_usize_of_nat(v___x_6605_);
v___x_6616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6604_, v___x_6614_, v___x_6615_, v___x_6608_, v_a_6446_);
lean_dec(v_a_6604_);
if (lean_obj_tag(v___x_6616_) == 0)
{
lean_dec_ref(v___x_6616_);
goto v___jp_6474_;
}
else
{
lean_object* v_a_6617_; 
v_a_6617_ = lean_ctor_get(v___x_6616_, 0);
lean_inc(v_a_6617_);
lean_dec_ref(v___x_6616_);
v_a_6472_ = v_a_6617_;
goto v___jp_6471_;
}
}
}
}
}
v___jp_6618_:
{
lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; uint8_t v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6631_; uint8_t v_isReservoir_6632_; 
lean_inc_ref(v_platform_6443_);
lean_inc_ref(v_remoteScope_6442_);
lean_inc_ref(v_service_6440_);
v___x_6619_ = l_Lake_CacheService_revisionUrl(v_rev_6438_, v_service_6440_, v_remoteScope_6442_, v_platform_6443_, v_toolchain_6444_);
v___x_6620_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__1));
v___x_6621_ = lean_string_append(v_localScope_6441_, v___x_6620_);
v___x_6622_ = lean_string_append(v___x_6621_, v_rev_6438_);
lean_dec_ref(v_rev_6438_);
v___x_6623_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_6624_ = lean_string_append(v___x_6622_, v___x_6623_);
v___x_6625_ = lean_string_append(v___x_6624_, v_path_6481_);
v___x_6626_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_6627_ = lean_string_append(v___x_6625_, v___x_6626_);
v___x_6628_ = lean_string_append(v___x_6627_, v___x_6619_);
v___x_6629_ = 1;
v___x_6630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6630_, 0, v___x_6628_);
lean_ctor_set_uint8(v___x_6630_, sizeof(void*)*1, v___x_6629_);
lean_inc_ref(v_a_6446_);
v___x_6631_ = lean_apply_2(v_a_6446_, v___x_6630_, lean_box(0));
v_isReservoir_6632_ = lean_ctor_get_uint8(v_service_6440_, sizeof(void*)*5);
lean_dec_ref(v_service_6440_);
if (v_isReservoir_6632_ == 0)
{
lean_object* v___x_6633_; 
v___x_6633_ = ((lean_object*)(l_Lake_CacheService_downloadRevisionOutputs_x3f___closed__2));
v___y_6585_ = v___x_6619_;
v___y_6586_ = v___x_6633_;
goto v___jp_6584_;
}
else
{
lean_object* v___x_6634_; 
v___x_6634_ = l_Lake_Reservoir_lakeHeaders;
v___y_6585_ = v___x_6619_;
v___y_6586_ = v___x_6634_;
goto v___jp_6584_;
}
}
v___jp_6636_:
{
if (v___x_6635_ == 0)
{
goto v___jp_6618_;
}
else
{
if (v_force_6445_ == 0)
{
lean_object* v___x_6637_; lean_object* v___x_6638_; uint8_t v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
lean_dec_ref(v_toolchain_6444_);
lean_dec_ref(v_remoteScope_6442_);
lean_dec_ref(v_localScope_6441_);
lean_dec_ref(v_service_6440_);
lean_dec_ref(v_rev_6438_);
v___x_6637_ = lean_string_utf8_byte_size(v_platform_6443_);
lean_dec_ref(v_platform_6443_);
v___x_6638_ = lean_unsigned_to_nat(0u);
v___x_6639_ = lean_nat_dec_eq(v___x_6637_, v___x_6638_);
v___x_6640_ = ((lean_object*)(l_Lake_CacheMap_parse___closed__1));
v___x_6641_ = l_Lake_CacheMap_load(v_path_6481_, v___x_6639_, v___x_6640_);
if (lean_obj_tag(v___x_6641_) == 0)
{
lean_object* v_a_6642_; lean_object* v_a_6643_; lean_object* v___x_6644_; uint8_t v___x_6645_; 
v_a_6642_ = lean_ctor_get(v___x_6641_, 0);
lean_inc(v_a_6642_);
v_a_6643_ = lean_ctor_get(v___x_6641_, 1);
lean_inc(v_a_6643_);
lean_dec_ref(v___x_6641_);
v___x_6644_ = lean_array_get_size(v_a_6643_);
v___x_6645_ = lean_nat_dec_lt(v___x_6638_, v___x_6644_);
if (v___x_6645_ == 0)
{
lean_dec(v_a_6643_);
v_a_6452_ = v_a_6642_;
goto v___jp_6451_;
}
else
{
lean_object* v___x_6646_; uint8_t v___x_6647_; 
v___x_6646_ = lean_box(0);
v___x_6647_ = lean_nat_dec_le(v___x_6644_, v___x_6644_);
if (v___x_6647_ == 0)
{
if (v___x_6645_ == 0)
{
lean_dec(v_a_6643_);
v_a_6452_ = v_a_6642_;
goto v___jp_6451_;
}
else
{
size_t v___x_6648_; size_t v___x_6649_; lean_object* v___x_6650_; 
v___x_6648_ = ((size_t)0ULL);
v___x_6649_ = lean_usize_of_nat(v___x_6644_);
v___x_6650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6643_, v___x_6648_, v___x_6649_, v___x_6646_, v_a_6446_);
lean_dec(v_a_6643_);
if (lean_obj_tag(v___x_6650_) == 0)
{
lean_dec_ref(v___x_6650_);
v_a_6452_ = v_a_6642_;
goto v___jp_6451_;
}
else
{
lean_object* v_a_6651_; lean_object* v___x_6653_; uint8_t v_isShared_6654_; uint8_t v_isSharedCheck_6658_; 
lean_dec(v_a_6642_);
v_a_6651_ = lean_ctor_get(v___x_6650_, 0);
v_isSharedCheck_6658_ = !lean_is_exclusive(v___x_6650_);
if (v_isSharedCheck_6658_ == 0)
{
v___x_6653_ = v___x_6650_;
v_isShared_6654_ = v_isSharedCheck_6658_;
goto v_resetjp_6652_;
}
else
{
lean_inc(v_a_6651_);
lean_dec(v___x_6650_);
v___x_6653_ = lean_box(0);
v_isShared_6654_ = v_isSharedCheck_6658_;
goto v_resetjp_6652_;
}
v_resetjp_6652_:
{
lean_object* v___x_6656_; 
if (v_isShared_6654_ == 0)
{
v___x_6656_ = v___x_6653_;
goto v_reusejp_6655_;
}
else
{
lean_object* v_reuseFailAlloc_6657_; 
v_reuseFailAlloc_6657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6657_, 0, v_a_6651_);
v___x_6656_ = v_reuseFailAlloc_6657_;
goto v_reusejp_6655_;
}
v_reusejp_6655_:
{
return v___x_6656_;
}
}
}
}
}
else
{
size_t v___x_6659_; size_t v___x_6660_; lean_object* v___x_6661_; 
v___x_6659_ = ((size_t)0ULL);
v___x_6660_ = lean_usize_of_nat(v___x_6644_);
v___x_6661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6643_, v___x_6659_, v___x_6660_, v___x_6646_, v_a_6446_);
lean_dec(v_a_6643_);
if (lean_obj_tag(v___x_6661_) == 0)
{
lean_dec_ref(v___x_6661_);
v_a_6452_ = v_a_6642_;
goto v___jp_6451_;
}
else
{
lean_object* v_a_6662_; lean_object* v___x_6664_; uint8_t v_isShared_6665_; uint8_t v_isSharedCheck_6669_; 
lean_dec(v_a_6642_);
v_a_6662_ = lean_ctor_get(v___x_6661_, 0);
v_isSharedCheck_6669_ = !lean_is_exclusive(v___x_6661_);
if (v_isSharedCheck_6669_ == 0)
{
v___x_6664_ = v___x_6661_;
v_isShared_6665_ = v_isSharedCheck_6669_;
goto v_resetjp_6663_;
}
else
{
lean_inc(v_a_6662_);
lean_dec(v___x_6661_);
v___x_6664_ = lean_box(0);
v_isShared_6665_ = v_isSharedCheck_6669_;
goto v_resetjp_6663_;
}
v_resetjp_6663_:
{
lean_object* v___x_6667_; 
if (v_isShared_6665_ == 0)
{
v___x_6667_ = v___x_6664_;
goto v_reusejp_6666_;
}
else
{
lean_object* v_reuseFailAlloc_6668_; 
v_reuseFailAlloc_6668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6668_, 0, v_a_6662_);
v___x_6667_ = v_reuseFailAlloc_6668_;
goto v_reusejp_6666_;
}
v_reusejp_6666_:
{
return v___x_6667_;
}
}
}
}
}
}
else
{
lean_object* v_a_6670_; lean_object* v___x_6671_; uint8_t v___x_6672_; 
v_a_6670_ = lean_ctor_get(v___x_6641_, 1);
lean_inc(v_a_6670_);
lean_dec_ref(v___x_6641_);
v___x_6671_ = lean_array_get_size(v_a_6670_);
v___x_6672_ = lean_nat_dec_lt(v___x_6638_, v___x_6671_);
if (v___x_6672_ == 0)
{
lean_object* v___x_6673_; lean_object* v___x_6674_; 
lean_dec(v_a_6670_);
v___x_6673_ = lean_box(0);
v___x_6674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6674_, 0, v___x_6673_);
return v___x_6674_;
}
else
{
lean_object* v___x_6675_; uint8_t v___x_6676_; 
v___x_6675_ = lean_box(0);
v___x_6676_ = lean_nat_dec_le(v___x_6671_, v___x_6671_);
if (v___x_6676_ == 0)
{
if (v___x_6672_ == 0)
{
lean_dec(v_a_6670_);
goto v___jp_6448_;
}
else
{
size_t v___x_6677_; size_t v___x_6678_; lean_object* v___x_6679_; 
v___x_6677_ = ((size_t)0ULL);
v___x_6678_ = lean_usize_of_nat(v___x_6671_);
v___x_6679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6670_, v___x_6677_, v___x_6678_, v___x_6675_, v_a_6446_);
lean_dec(v_a_6670_);
if (lean_obj_tag(v___x_6679_) == 0)
{
lean_dec_ref(v___x_6679_);
goto v___jp_6448_;
}
else
{
lean_object* v_a_6680_; lean_object* v___x_6682_; uint8_t v_isShared_6683_; uint8_t v_isSharedCheck_6687_; 
v_a_6680_ = lean_ctor_get(v___x_6679_, 0);
v_isSharedCheck_6687_ = !lean_is_exclusive(v___x_6679_);
if (v_isSharedCheck_6687_ == 0)
{
v___x_6682_ = v___x_6679_;
v_isShared_6683_ = v_isSharedCheck_6687_;
goto v_resetjp_6681_;
}
else
{
lean_inc(v_a_6680_);
lean_dec(v___x_6679_);
v___x_6682_ = lean_box(0);
v_isShared_6683_ = v_isSharedCheck_6687_;
goto v_resetjp_6681_;
}
v_resetjp_6681_:
{
lean_object* v___x_6685_; 
if (v_isShared_6683_ == 0)
{
v___x_6685_ = v___x_6682_;
goto v_reusejp_6684_;
}
else
{
lean_object* v_reuseFailAlloc_6686_; 
v_reuseFailAlloc_6686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_a_6680_);
v___x_6685_ = v_reuseFailAlloc_6686_;
goto v_reusejp_6684_;
}
v_reusejp_6684_:
{
return v___x_6685_;
}
}
}
}
}
else
{
size_t v___x_6688_; size_t v___x_6689_; lean_object* v___x_6690_; 
v___x_6688_ = ((size_t)0ULL);
v___x_6689_ = lean_usize_of_nat(v___x_6671_);
v___x_6690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_CacheMap_parse_spec__0(v_a_6670_, v___x_6688_, v___x_6689_, v___x_6675_, v_a_6446_);
lean_dec(v_a_6670_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_dec_ref(v___x_6690_);
goto v___jp_6448_;
}
else
{
lean_object* v_a_6691_; lean_object* v___x_6693_; uint8_t v_isShared_6694_; uint8_t v_isSharedCheck_6698_; 
v_a_6691_ = lean_ctor_get(v___x_6690_, 0);
v_isSharedCheck_6698_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6698_ == 0)
{
v___x_6693_ = v___x_6690_;
v_isShared_6694_ = v_isSharedCheck_6698_;
goto v_resetjp_6692_;
}
else
{
lean_inc(v_a_6691_);
lean_dec(v___x_6690_);
v___x_6693_ = lean_box(0);
v_isShared_6694_ = v_isSharedCheck_6698_;
goto v_resetjp_6692_;
}
v_resetjp_6692_:
{
lean_object* v___x_6696_; 
if (v_isShared_6694_ == 0)
{
v___x_6696_ = v___x_6693_;
goto v_reusejp_6695_;
}
else
{
lean_object* v_reuseFailAlloc_6697_; 
v_reuseFailAlloc_6697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6697_, 0, v_a_6691_);
v___x_6696_ = v_reuseFailAlloc_6697_;
goto v_reusejp_6695_;
}
v_reusejp_6695_:
{
return v___x_6696_;
}
}
}
}
}
}
}
else
{
goto v___jp_6618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f___boxed(lean_object* v_rev_6725_, lean_object* v_cache_6726_, lean_object* v_service_6727_, lean_object* v_localScope_6728_, lean_object* v_remoteScope_6729_, lean_object* v_platform_6730_, lean_object* v_toolchain_6731_, lean_object* v_force_6732_, lean_object* v_a_6733_, lean_object* v_a_6734_){
_start:
{
uint8_t v_force_boxed_6735_; lean_object* v_res_6736_; 
v_force_boxed_6735_ = lean_unbox(v_force_6732_);
v_res_6736_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_rev_6725_, v_cache_6726_, v_service_6727_, v_localScope_6728_, v_remoteScope_6729_, v_platform_6730_, v_toolchain_6731_, v_force_boxed_6735_, v_a_6733_);
lean_dec_ref(v_a_6733_);
return v_res_6736_;
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs(lean_object* v_rev_6738_, lean_object* v_outputs_6739_, lean_object* v_service_6740_, lean_object* v_scope_6741_, lean_object* v_platform_6742_, lean_object* v_toolchain_6743_, lean_object* v_a_6744_){
_start:
{
lean_object* v_url_6746_; lean_object* v___y_6748_; lean_object* v_s_6764_; 
lean_inc_ref(v_scope_6741_);
lean_inc_ref(v_service_6740_);
v_url_6746_ = l___private_Lake_Config_Cache_0__Lake_CacheService_s3RevisionUrl(v_rev_6738_, v_service_6740_, v_scope_6741_, v_platform_6742_, v_toolchain_6743_);
v_s_6764_ = lean_ctor_get(v_scope_6741_, 0);
lean_inc_ref(v_s_6764_);
lean_dec_ref(v_scope_6741_);
v___y_6748_ = v_s_6764_;
goto v___jp_6747_;
v___jp_6747_:
{
lean_object* v___x_6749_; lean_object* v___x_6750_; lean_object* v___x_6751_; lean_object* v___x_6752_; lean_object* v___x_6753_; lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; lean_object* v___x_6757_; uint8_t v___x_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; lean_object* v_key_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; 
v___x_6749_ = ((lean_object*)(l_Lake_CacheService_uploadRevisionOutputs___closed__0));
v___x_6750_ = lean_string_append(v___y_6748_, v___x_6749_);
v___x_6751_ = lean_string_append(v___x_6750_, v_rev_6738_);
v___x_6752_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__1));
v___x_6753_ = lean_string_append(v___x_6751_, v___x_6752_);
v___x_6754_ = lean_string_append(v___x_6753_, v_outputs_6739_);
v___x_6755_ = ((lean_object*)(l_Lake_CacheService_downloadArtifact___closed__2));
v___x_6756_ = lean_string_append(v___x_6754_, v___x_6755_);
v___x_6757_ = lean_string_append(v___x_6756_, v_url_6746_);
v___x_6758_ = 1;
v___x_6759_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6759_, 0, v___x_6757_);
lean_ctor_set_uint8(v___x_6759_, sizeof(void*)*1, v___x_6758_);
lean_inc_ref(v_a_6744_);
v___x_6760_ = lean_apply_2(v_a_6744_, v___x_6759_, lean_box(0));
v_key_6761_ = lean_ctor_get(v_service_6740_, 1);
lean_inc_ref(v_key_6761_);
lean_dec_ref(v_service_6740_);
v___x_6762_ = ((lean_object*)(l_Lake_CacheService_mapContentType___closed__0));
v___x_6763_ = l___private_Lake_Config_Cache_0__Lake_uploadS3___at___00Lake_CacheService_uploadArtifact_spec__0(v_a_6744_, v_outputs_6739_, v___x_6762_, v_url_6746_, v_key_6761_);
return v___x_6763_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_CacheService_uploadRevisionOutputs___boxed(lean_object* v_rev_6765_, lean_object* v_outputs_6766_, lean_object* v_service_6767_, lean_object* v_scope_6768_, lean_object* v_platform_6769_, lean_object* v_toolchain_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_){
_start:
{
lean_object* v_res_6773_; 
v_res_6773_ = l_Lake_CacheService_uploadRevisionOutputs(v_rev_6765_, v_outputs_6766_, v_service_6767_, v_scope_6768_, v_platform_6769_, v_toolchain_6770_, v_a_6771_);
lean_dec_ref(v_a_6771_);
lean_dec_ref(v_toolchain_6770_);
lean_dec_ref(v_rev_6765_);
return v_res_6773_;
}
}
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Artifact(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Reservoir(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Cache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_CachePlatform_system = _init_l_Lake_CachePlatform_system();
lean_mark_persistent(l_Lake_CachePlatform_system);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Cache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Util_Version(uint8_t builtin);
lean_object* initialize_Lake_Config_Artifact(uint8_t builtin);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
lean_object* initialize_Lake_Util_Url(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Lake_Util_Reservoir(uint8_t builtin);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Cache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Artifact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Url(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Cache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Cache(builtin);
}
#ifdef __cplusplus
}
#endif
