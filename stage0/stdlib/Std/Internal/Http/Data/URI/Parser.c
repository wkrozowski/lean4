// Lean compiler output
// Module: Std.Internal.Http.Data.URI.Parser
// Imports: import Init.While public import Init.Data.String.Basic public import Std.Internal.Parsec public import Std.Internal.Parsec.ByteArray public import Std.Internal.Http.Data.URI.Basic public import Std.Internal.Http.Data.URI.Config import Init.Data.String.Search
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
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_Std_Http_URI_EncodedString_empty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_ByteSlice_toByteArray(lean_object*);
lean_object* l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(lean_object*);
lean_object* l_ByteSlice_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
extern lean_object* l_Std_Http_URI_Query_empty;
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_URI_EncodedQueryParam_fromString_x3f(lean_object*);
lean_object* l_Std_Http_URI_Query_insertEncoded(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_Std_Http_Internal_instDecidableIsLowerCase(lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_URI_isValidDomainLabel(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_uv_pton_v4(lean_object*);
lean_object* lean_uv_pton_v6(lean_object*);
lean_object* l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(lean_object*);
lean_object* l_Std_Http_URI_EncodedFragment_decode(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_peekIs(lean_object*, lean_object*);
static const lean_string_object l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "invalid scheme"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected at least one char"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__8_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "scheme length limit is 0 (no scheme allowed)"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__10_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__11 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__11_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "port number too large: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid port number: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "invalid percent encoding in user info"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1;
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid IPv6 address: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expected: '"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid IPv4 address: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "invalid domain name: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid host"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2_value;
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid port number"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "too many path segments (limit: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "path too long (limit: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " bytes)"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid percent encoding in path segment"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__6_value)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Parser_parsePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "require '/' in path"};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__0 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parsePath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__0_value)}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__1 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__1_value;
static const lean_string_object l_Std_Http_URI_Parser_parsePath___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "need a path"};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__2 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parsePath___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__2_value)}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__3 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__3_value;
static const lean_array_object l_Std_Http_URI_Parser_parsePath___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__4 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__4_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parsePath___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_URI_Parser_parsePath___closed__5 = (const lean_object*)&l_Std_Http_URI_Parser_parsePath___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid query string"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__1_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "too many query parameters (limit: "};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "invalid percent encoding in fragment"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0_value;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__0;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__1;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__2;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__3;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__4;
static const lean_string_object l_Std_Http_URI_Parser_parseURI___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "invalid fragment parse encoding"};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__5 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__5_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseURI___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__5_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseURI___closed__6 = (const lean_object*)&l_Std_Http_URI_Parser_parseURI___closed__6_value;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__7;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__8;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__9;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__10;
static lean_once_cell_t l_Std_Http_URI_Parser_parseURI___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_URI_Parser_parseURI___closed__11;
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3;
static lean_once_cell_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not origin"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "not http absolute uri with path"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__0_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "not http absolute uri"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value;
static const lean_ctor_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__2_value)}};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "http"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4_value;
static const lean_string_object l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "https"};
static const lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5 = (const lean_object*)&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_URI_Parser_parseHostHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid host header port"};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__0 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__0_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseHostHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__0_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__1 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__1_value;
static const lean_string_object l_Std_Http_URI_Parser_parseHostHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid host header"};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__2 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__2_value;
static const lean_ctor_object l_Std_Http_URI_Parser_parseHostHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__2_value)}};
static const lean_object* l_Std_Http_URI_Parser_parseHostHeader___closed__3 = (const lean_object*)&l_Std_Http_URI_Parser_parseHostHeader___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt___redArg(lean_object* v_p_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; 
lean_inc_ref(v_a_2_);
v___x_3_ = lean_apply_1(v_p_1_, v_a_2_);
if (lean_obj_tag(v___x_3_) == 0)
{
lean_object* v_pos_4_; lean_object* v_res_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_13_; 
lean_dec_ref(v_a_2_);
v_pos_4_ = lean_ctor_get(v___x_3_, 0);
v_res_5_ = lean_ctor_get(v___x_3_, 1);
v_isSharedCheck_13_ = !lean_is_exclusive(v___x_3_);
if (v_isSharedCheck_13_ == 0)
{
v___x_7_ = v___x_3_;
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_res_5_);
lean_inc(v_pos_4_);
lean_dec(v___x_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_res_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_9_);
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_pos_4_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
else
{
lean_object* v_err_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_27_; 
v_err_14_ = lean_ctor_get(v___x_3_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_3_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v___x_3_, 0);
lean_dec(v_unused_28_);
v___x_16_ = v___x_3_;
v_isShared_17_ = v_isSharedCheck_27_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_err_14_);
lean_dec(v___x_3_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_27_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_idx_18_; uint8_t v___x_19_; 
v_idx_18_ = lean_ctor_get(v_a_2_, 1);
v___x_19_ = lean_nat_dec_eq(v_idx_18_, v_idx_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_21_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v_a_2_);
v___x_21_ = v___x_16_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_a_2_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_err_14_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
else
{
lean_object* v___x_23_; lean_object* v___x_25_; 
lean_dec(v_err_14_);
v___x_23_ = lean_box(0);
if (v_isShared_17_ == 0)
{
lean_ctor_set_tag(v___x_16_, 0);
lean_ctor_set(v___x_16_, 1, v___x_23_);
lean_ctor_set(v___x_16_, 0, v_a_2_);
v___x_25_ = v___x_16_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_2_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_tryOpt(lean_object* v_00_u03b1_29_, lean_object* v_p_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; 
lean_inc_ref(v_a_31_);
v___x_32_ = lean_apply_1(v_p_30_, v_a_31_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v_pos_33_; lean_object* v_res_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
lean_dec_ref(v_a_31_);
v_pos_33_ = lean_ctor_get(v___x_32_, 0);
v_res_34_ = lean_ctor_get(v___x_32_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_32_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_res_34_);
lean_inc(v_pos_33_);
lean_dec(v___x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_38_, 0, v_res_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_pos_33_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
else
{
lean_object* v_err_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_56_; 
v_err_43_ = lean_ctor_get(v___x_32_, 1);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_56_ == 0)
{
lean_object* v_unused_57_; 
v_unused_57_ = lean_ctor_get(v___x_32_, 0);
lean_dec(v_unused_57_);
v___x_45_ = v___x_32_;
v_isShared_46_ = v_isSharedCheck_56_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_err_43_);
lean_dec(v___x_32_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_56_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v_idx_47_; uint8_t v___x_48_; 
v_idx_47_ = lean_ctor_get(v_a_31_, 1);
v___x_48_ = lean_nat_dec_eq(v_idx_47_, v_idx_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_50_; 
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v_a_31_);
v___x_50_ = v___x_45_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_31_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_err_43_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
else
{
lean_object* v___x_52_; lean_object* v___x_54_; 
lean_dec(v_err_43_);
v___x_52_ = lean_box(0);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 0);
lean_ctor_set(v___x_45_, 1, v___x_52_);
lean_ctor_set(v___x_45_, 0, v_a_31_);
v___x_54_ = v___x_45_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_31_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_peekIs(lean_object* v_p_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_pos_61_; lean_object* v_array_65_; lean_object* v_idx_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_array_65_ = lean_ctor_get(v_a_59_, 0);
v_idx_66_ = lean_ctor_get(v_a_59_, 1);
v___x_67_ = lean_byte_array_size(v_array_65_);
v___x_68_ = lean_nat_dec_lt(v_idx_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_dec_ref(v_p_58_);
v_pos_61_ = v_a_59_;
goto v___jp_60_;
}
else
{
uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_69_ = lean_byte_array_fget(v_array_65_, v_idx_66_);
v___x_70_ = lean_box(v___x_69_);
v___x_71_ = lean_apply_1(v_p_58_, v___x_70_);
v___x_72_ = lean_unbox(v___x_71_);
if (v___x_72_ == 0)
{
v_pos_61_ = v_a_59_;
goto v___jp_60_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_a_59_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
return v___x_73_;
}
}
v___jp_60_:
{
uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = 0;
v___x_63_ = lean_box(v___x_62_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v_pos_61_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(lean_object* v_msg_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2___closed__0));
v___x_77_ = lean_panic_fn_borrowed(v___x_76_, v_msg_75_);
return v___x_77_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0(void){
_start:
{
uint32_t v___x_78_; uint8_t v___x_79_; 
v___x_78_ = 97;
v___x_79_ = lean_uint32_to_uint8(v___x_78_);
return v___x_79_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1(void){
_start:
{
uint32_t v___x_80_; uint8_t v___x_81_; 
v___x_80_ = 122;
v___x_81_ = lean_uint32_to_uint8(v___x_80_);
return v___x_81_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2(void){
_start:
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 65;
v___x_83_ = lean_uint32_to_uint8(v___x_82_);
return v___x_83_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3(void){
_start:
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 90;
v___x_85_ = lean_uint32_to_uint8(v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(uint8_t v___y_86_){
_start:
{
uint8_t v___y_88_; uint8_t v___x_93_; uint8_t v___x_94_; 
v___x_93_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_94_ = lean_uint8_dec_le(v___x_93_, v___y_86_);
if (v___x_94_ == 0)
{
v___y_88_ = v___x_94_;
goto v___jp_87_;
}
else
{
uint8_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_96_ = lean_uint8_dec_le(v___y_86_, v___x_95_);
v___y_88_ = v___x_96_;
goto v___jp_87_;
}
v___jp_87_:
{
if (v___y_88_ == 0)
{
uint8_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_90_ = lean_uint8_dec_le(v___x_89_, v___y_86_);
if (v___x_90_ == 0)
{
return v___x_90_;
}
else
{
uint8_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_92_ = lean_uint8_dec_le(v___y_86_, v___x_91_);
return v___x_92_;
}
}
else
{
return v___y_88_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___boxed(lean_object* v___y_97_){
_start:
{
uint8_t v___y_2727__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v___y_2727__boxed_98_ = lean_unbox(v___y_97_);
v_res_99_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0(v___y_2727__boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0(void){
_start:
{
uint32_t v___x_101_; uint8_t v___x_102_; 
v___x_101_ = 43;
v___x_102_ = lean_uint32_to_uint8(v___x_101_);
return v___x_102_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1(void){
_start:
{
uint32_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = 45;
v___x_104_ = lean_uint32_to_uint8(v___x_103_);
return v___x_104_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2(void){
_start:
{
uint32_t v___x_105_; uint8_t v___x_106_; 
v___x_105_ = 46;
v___x_106_ = lean_uint32_to_uint8(v___x_105_);
return v___x_106_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3(void){
_start:
{
uint32_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 48;
v___x_108_ = lean_uint32_to_uint8(v___x_107_);
return v___x_108_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4(void){
_start:
{
uint32_t v___x_109_; uint8_t v___x_110_; 
v___x_109_ = 57;
v___x_110_ = lean_uint32_to_uint8(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1(uint8_t v_c_111_){
_start:
{
uint8_t v___y_113_; uint8_t v___y_121_; uint8_t v___y_127_; uint8_t v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_133_ = lean_uint8_dec_le(v___x_132_, v_c_111_);
if (v___x_133_ == 0)
{
v___y_127_ = v___x_133_;
goto v___jp_126_;
}
else
{
uint8_t v___x_134_; uint8_t v___x_135_; 
v___x_134_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_135_ = lean_uint8_dec_le(v_c_111_, v___x_134_);
v___y_127_ = v___x_135_;
goto v___jp_126_;
}
v___jp_112_:
{
if (v___y_113_ == 0)
{
uint8_t v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_115_ = lean_uint8_dec_eq(v_c_111_, v___x_114_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_117_ = lean_uint8_dec_eq(v_c_111_, v___x_116_);
if (v___x_117_ == 0)
{
uint8_t v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_119_ = lean_uint8_dec_eq(v_c_111_, v___x_118_);
if (v___x_119_ == 0)
{
return v___y_113_;
}
else
{
return v___x_119_;
}
}
else
{
return v___x_117_;
}
}
else
{
return v___x_115_;
}
}
else
{
return v___y_113_;
}
}
v___jp_120_:
{
if (v___y_121_ == 0)
{
uint8_t v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_123_ = lean_uint8_dec_le(v___x_122_, v_c_111_);
if (v___x_123_ == 0)
{
v___y_113_ = v___x_123_;
goto v___jp_112_;
}
else
{
uint8_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_125_ = lean_uint8_dec_le(v_c_111_, v___x_124_);
v___y_113_ = v___x_125_;
goto v___jp_112_;
}
}
else
{
return v___y_121_;
}
}
v___jp_126_:
{
if (v___y_127_ == 0)
{
uint8_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_129_ = lean_uint8_dec_le(v___x_128_, v_c_111_);
if (v___x_129_ == 0)
{
v___y_121_ = v___x_129_;
goto v___jp_120_;
}
else
{
uint8_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_131_ = lean_uint8_dec_le(v_c_111_, v___x_130_);
v___y_121_ = v___x_131_;
goto v___jp_120_;
}
}
else
{
return v___y_127_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___boxed(lean_object* v_c_136_){
_start:
{
uint8_t v_c_boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_c_boxed_137_ = lean_unbox(v_c_136_);
v_res_138_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1(v_c_boxed_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 1;
return v___x_141_;
}
else
{
lean_object* v_head_142_; lean_object* v_tail_143_; uint8_t v___y_145_; uint32_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; uint8_t v___y_171_; 
v_head_142_ = lean_ctor_get(v_x_140_, 0);
v_tail_143_ = lean_ctor_get(v_x_140_, 1);
v___x_166_ = lean_unbox_uint32(v_head_142_);
v___x_167_ = lean_uint32_to_nat(v___x_166_);
v___x_168_ = lean_unsigned_to_nat(128u);
v___x_169_ = lean_nat_dec_lt(v___x_167_, v___x_168_);
lean_dec(v___x_167_);
if (v___x_169_ == 0)
{
v___y_145_ = v___x_169_;
goto v___jp_144_;
}
else
{
uint32_t v___x_179_; uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_179_ = 48;
v___x_180_ = lean_unbox_uint32(v_head_142_);
v___x_181_ = lean_uint32_dec_le(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
v___y_171_ = v___x_181_;
goto v___jp_170_;
}
else
{
uint32_t v___x_182_; uint32_t v___x_183_; uint8_t v___x_184_; 
v___x_182_ = 57;
v___x_183_ = lean_unbox_uint32(v_head_142_);
v___x_184_ = lean_uint32_dec_le(v___x_183_, v___x_182_);
v___y_171_ = v___x_184_;
goto v___jp_170_;
}
}
v___jp_144_:
{
if (v___y_145_ == 0)
{
uint32_t v___x_146_; uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_146_ = 43;
v___x_147_ = lean_unbox_uint32(v_head_142_);
v___x_148_ = lean_uint32_dec_eq(v___x_147_, v___x_146_);
if (v___x_148_ == 0)
{
uint32_t v___x_149_; uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_149_ = 45;
v___x_150_ = lean_unbox_uint32(v_head_142_);
v___x_151_ = lean_uint32_dec_eq(v___x_150_, v___x_149_);
if (v___x_151_ == 0)
{
uint32_t v___x_152_; uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_152_ = 46;
v___x_153_ = lean_unbox_uint32(v_head_142_);
v___x_154_ = lean_uint32_dec_eq(v___x_153_, v___x_152_);
if (v___x_154_ == 0)
{
return v___y_145_;
}
else
{
v_x_140_ = v_tail_143_;
goto _start;
}
}
else
{
v_x_140_ = v_tail_143_;
goto _start;
}
}
else
{
v_x_140_ = v_tail_143_;
goto _start;
}
}
else
{
v_x_140_ = v_tail_143_;
goto _start;
}
}
v___jp_159_:
{
uint32_t v___x_160_; uint32_t v___x_161_; uint8_t v___x_162_; 
v___x_160_ = 97;
v___x_161_ = lean_unbox_uint32(v_head_142_);
v___x_162_ = lean_uint32_dec_le(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
v___y_145_ = v___x_162_;
goto v___jp_144_;
}
else
{
uint32_t v___x_163_; uint32_t v___x_164_; uint8_t v___x_165_; 
v___x_163_ = 122;
v___x_164_ = lean_unbox_uint32(v_head_142_);
v___x_165_ = lean_uint32_dec_le(v___x_164_, v___x_163_);
v___y_145_ = v___x_165_;
goto v___jp_144_;
}
}
v___jp_170_:
{
if (v___y_171_ == 0)
{
uint32_t v___x_172_; uint32_t v___x_173_; uint8_t v___x_174_; 
v___x_172_ = 65;
v___x_173_ = lean_unbox_uint32(v_head_142_);
v___x_174_ = lean_uint32_dec_le(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
goto v___jp_159_;
}
else
{
uint32_t v___x_175_; uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_175_ = 90;
v___x_176_ = lean_unbox_uint32(v_head_142_);
v___x_177_ = lean_uint32_dec_le(v___x_176_, v___x_175_);
if (v___x_177_ == 0)
{
goto v___jp_159_;
}
else
{
v___y_145_ = v___x_169_;
goto v___jp_144_;
}
}
}
else
{
v_x_140_ = v_tail_143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1___boxed(lean_object* v_x_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_List_all___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v_x_185_);
lean_dec(v_x_185_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(lean_object* v_s_188_, lean_object* v_p_189_){
_start:
{
uint32_t v___y_191_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_string_utf8_byte_size(v_s_188_);
v___x_197_ = lean_nat_dec_eq(v_p_189_, v___x_196_);
if (v___x_197_ == 0)
{
uint32_t v___x_198_; uint32_t v___x_199_; uint8_t v___x_200_; 
v___x_198_ = lean_string_utf8_get_fast(v_s_188_, v_p_189_);
v___x_199_ = 65;
v___x_200_ = lean_uint32_dec_le(v___x_199_, v___x_198_);
if (v___x_200_ == 0)
{
v___y_191_ = v___x_198_;
goto v___jp_190_;
}
else
{
uint32_t v___x_201_; uint8_t v___x_202_; 
v___x_201_ = 90;
v___x_202_ = lean_uint32_dec_le(v___x_198_, v___x_201_);
if (v___x_202_ == 0)
{
v___y_191_ = v___x_198_;
goto v___jp_190_;
}
else
{
uint32_t v___x_203_; uint32_t v___x_204_; 
v___x_203_ = 32;
v___x_204_ = lean_uint32_add(v___x_198_, v___x_203_);
v___y_191_ = v___x_204_;
goto v___jp_190_;
}
}
}
else
{
lean_dec(v_p_189_);
return v_s_188_;
}
v___jp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_inc(v_p_189_);
v___x_192_ = lean_string_utf8_set(v_s_188_, v_p_189_, v___y_191_);
v___x_193_ = l_Char_utf8Size(v___y_191_);
v___x_194_ = lean_nat_add(v_p_189_, v___x_193_);
lean_dec(v___x_193_);
lean_dec(v_p_189_);
v_s_188_ = v___x_192_;
v_p_189_ = v___x_194_;
goto _start;
}
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_212_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__5));
v___x_213_ = lean_unsigned_to_nat(46u);
v___x_214_ = lean_unsigned_to_nat(193u);
v___x_215_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__4));
v___x_216_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__3));
v___x_217_ = l_mkPanicMessageWithDecl(v___x_216_, v___x_215_, v___x_214_, v___x_213_, v___x_212_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(lean_object* v_config_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___y_228_; lean_object* v___y_232_; lean_object* v___y_233_; uint8_t v_val_234_; uint32_t v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v_maxSchemeLength_244_; lean_object* v___x_245_; lean_object* v___y_247_; lean_object* v___y_248_; uint8_t v___x_263_; 
v_maxSchemeLength_244_ = lean_ctor_get(v_config_225_, 0);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_eq(v_maxSchemeLength_244_, v___x_245_);
if (v___x_263_ == 0)
{
lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_fst_267_; lean_object* v_snd_268_; uint8_t v___x_269_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v_lower_274_; lean_object* v_upper_275_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; 
v___f_264_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__2));
v___x_265_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_a_226_);
v___x_266_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_264_, v___x_265_, v___x_245_, v_a_226_);
v_fst_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_fst_267_);
v_snd_268_ = lean_ctor_get(v___x_266_, 1);
lean_inc(v_snd_268_);
lean_dec_ref(v___x_266_);
v___x_269_ = lean_nat_dec_eq(v_fst_267_, v___x_245_);
if (v___x_269_ == 0)
{
lean_object* v_array_294_; lean_object* v_idx_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_326_; 
v_array_294_ = lean_ctor_get(v_a_226_, 0);
v_idx_295_ = lean_ctor_get(v_a_226_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_a_226_);
if (v_isSharedCheck_326_ == 0)
{
v___x_297_ = v_a_226_;
v_isShared_298_ = v_isSharedCheck_326_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_idx_295_);
lean_inc(v_array_294_);
lean_dec(v_a_226_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_326_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___f_299_; lean_object* v___y_301_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___y_317_; uint8_t v___x_325_; 
v___f_299_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__7));
v___x_314_ = lean_nat_add(v_idx_295_, v_fst_267_);
lean_dec(v_fst_267_);
v___x_315_ = lean_byte_array_size(v_array_294_);
v___x_325_ = lean_nat_dec_le(v_idx_295_, v___x_245_);
if (v___x_325_ == 0)
{
v___y_317_ = v_idx_295_;
goto v___jp_316_;
}
else
{
lean_dec(v_idx_295_);
v___y_317_ = v___x_245_;
goto v___jp_316_;
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v_lower_306_; lean_object* v_upper_307_; lean_object* v_array_308_; lean_object* v_idx_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_302_ = lean_nat_sub(v_maxSchemeLength_244_, v___x_265_);
lean_inc(v_snd_268_);
v___x_303_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_299_, v___x_302_, v___x_245_, v_snd_268_);
lean_dec(v___x_302_);
v_fst_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_fst_304_);
v_snd_305_ = lean_ctor_get(v___x_303_, 1);
lean_inc(v_snd_305_);
lean_dec_ref(v___x_303_);
v_lower_306_ = lean_ctor_get(v___y_301_, 0);
lean_inc(v_lower_306_);
v_upper_307_ = lean_ctor_get(v___y_301_, 1);
lean_inc(v_upper_307_);
lean_dec_ref(v___y_301_);
v_array_308_ = lean_ctor_get(v_snd_268_, 0);
lean_inc_ref(v_array_308_);
v_idx_309_ = lean_ctor_get(v_snd_268_, 1);
lean_inc(v_idx_309_);
lean_dec(v_snd_268_);
v___x_310_ = l_ByteArray_toByteSlice(v_array_294_, v_lower_306_, v_upper_307_);
v___x_311_ = lean_nat_add(v_idx_309_, v_fst_304_);
lean_dec(v_fst_304_);
v___x_312_ = lean_byte_array_size(v_array_308_);
v___x_313_ = lean_nat_dec_le(v_idx_309_, v___x_245_);
if (v___x_313_ == 0)
{
v___y_287_ = v___x_310_;
v___y_288_ = v_snd_305_;
v___y_289_ = v___x_312_;
v___y_290_ = v_array_308_;
v___y_291_ = v___x_311_;
v___y_292_ = v_idx_309_;
goto v___jp_286_;
}
else
{
lean_dec(v_idx_309_);
v___y_287_ = v___x_310_;
v___y_288_ = v_snd_305_;
v___y_289_ = v___x_312_;
v___y_290_ = v_array_308_;
v___y_291_ = v___x_311_;
v___y_292_ = v___x_245_;
goto v___jp_286_;
}
}
v___jp_316_:
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_le(v___x_314_, v___x_315_);
if (v___x_318_ == 0)
{
lean_object* v___x_320_; 
lean_dec(v___x_314_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_315_);
lean_ctor_set(v___x_297_, 0, v___y_317_);
v___x_320_ = v___x_297_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___y_317_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
v___y_301_ = v___x_320_;
goto v___jp_300_;
}
}
else
{
lean_object* v___x_323_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_314_);
lean_ctor_set(v___x_297_, 0, v___y_317_);
v___x_323_ = v___x_297_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___y_317_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_314_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
v___y_301_ = v___x_323_;
goto v___jp_300_;
}
}
}
}
}
else
{
lean_object* v_array_327_; lean_object* v_idx_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_fst_267_);
v_array_327_ = lean_ctor_get(v_snd_268_, 0);
v_idx_328_ = lean_ctor_get(v_snd_268_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_snd_268_);
if (v_isSharedCheck_342_ == 0)
{
v___x_330_ = v_snd_268_;
v_isShared_331_ = v_isSharedCheck_342_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_idx_328_);
lean_inc(v_array_327_);
lean_dec(v_snd_268_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_342_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_byte_array_size(v_array_327_);
lean_dec_ref(v_array_327_);
v___x_333_ = lean_nat_dec_le(v___x_332_, v_idx_328_);
lean_dec(v_idx_328_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9));
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 1);
lean_ctor_set(v___x_330_, 1, v___x_334_);
lean_ctor_set(v___x_330_, 0, v_a_226_);
v___x_336_ = v___x_330_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_226_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_box(0);
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 1);
lean_ctor_set(v___x_330_, 1, v___x_338_);
lean_ctor_set(v___x_330_, 0, v_a_226_);
v___x_340_ = v___x_330_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_226_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
v___jp_270_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_276_ = l_ByteArray_toByteSlice(v___y_273_, v_lower_274_, v_upper_275_);
v___x_277_ = l_ByteSlice_toByteArray(v___y_272_);
v___x_278_ = l_ByteSlice_toByteArray(v___x_276_);
v___x_279_ = lean_byte_array_size(v___x_277_);
v___x_280_ = lean_byte_array_size(v___x_278_);
v___x_281_ = lean_byte_array_copy_slice(v___x_278_, v___x_245_, v___x_277_, v___x_279_, v___x_280_, v___x_269_);
lean_dec_ref(v___x_278_);
v___x_282_ = lean_string_validate_utf8(v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref(v___x_281_);
v___x_283_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6);
v___x_284_ = l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_283_);
v___y_247_ = v___y_271_;
v___y_248_ = v___x_284_;
goto v___jp_246_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_string_from_utf8_unchecked(v___x_281_);
v___y_247_ = v___y_271_;
v___y_248_ = v___x_285_;
goto v___jp_246_;
}
}
v___jp_286_:
{
uint8_t v___x_293_; 
v___x_293_ = lean_nat_dec_le(v___y_291_, v___y_289_);
if (v___x_293_ == 0)
{
lean_dec(v___y_291_);
v___y_271_ = v___y_288_;
v___y_272_ = v___y_287_;
v___y_273_ = v___y_290_;
v_lower_274_ = v___y_292_;
v_upper_275_ = v___y_289_;
goto v___jp_270_;
}
else
{
lean_dec(v___y_289_);
v___y_271_ = v___y_288_;
v___y_272_ = v___y_287_;
v___y_273_ = v___y_290_;
v_lower_274_ = v___y_292_;
v_upper_275_ = v___y_291_;
goto v___jp_270_;
}
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__11));
v___x_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_344_, 0, v_a_226_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
return v___x_344_;
}
v___jp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__1));
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v___y_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
return v___x_230_;
}
v___jp_231_:
{
if (v_val_234_ == 0)
{
lean_dec_ref(v___y_233_);
v___y_228_ = v___y_232_;
goto v___jp_227_;
}
else
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v___y_232_);
lean_ctor_set(v___x_235_, 1, v___y_233_);
return v___x_235_;
}
}
v___jp_236_:
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 97;
v___x_241_ = lean_uint32_dec_le(v___x_240_, v___y_237_);
if (v___x_241_ == 0)
{
v___y_232_ = v___y_238_;
v___y_233_ = v___y_239_;
v_val_234_ = v___x_241_;
goto v___jp_231_;
}
else
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 122;
v___x_243_ = lean_uint32_dec_le(v___y_237_, v___x_242_);
v___y_232_ = v___y_238_;
v___y_233_ = v___y_239_;
v_val_234_ = v___x_243_;
goto v___jp_231_;
}
}
v___jp_246_:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___y_248_, v___x_245_);
lean_inc_ref(v___x_249_);
v___x_250_ = l_Std_Http_Internal_instDecidableIsLowerCase(v___x_249_);
if (v___x_250_ == 0)
{
lean_dec_ref(v___x_249_);
v___y_228_ = v___y_247_;
goto v___jp_227_;
}
else
{
lean_object* v___x_251_; uint8_t v___x_252_; 
lean_inc_ref(v___x_249_);
v___x_251_ = lean_string_data(v___x_249_);
v___x_252_ = l_List_all___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__1(v___x_251_);
if (v___x_252_ == 0)
{
lean_dec(v___x_251_);
lean_dec_ref(v___x_249_);
v___y_228_ = v___y_247_;
goto v___jp_227_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = l_List_head_x3f___redArg(v___x_251_);
lean_dec(v___x_251_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_dec_ref(v___x_249_);
v___y_228_ = v___y_247_;
goto v___jp_227_;
}
else
{
lean_object* v_val_254_; uint32_t v___x_255_; uint32_t v___x_256_; uint8_t v___x_257_; 
v_val_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_val_254_);
lean_dec_ref(v___x_253_);
v___x_255_ = 65;
v___x_256_ = lean_unbox_uint32(v_val_254_);
v___x_257_ = lean_uint32_dec_le(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
uint32_t v___x_258_; 
v___x_258_ = lean_unbox_uint32(v_val_254_);
lean_dec(v_val_254_);
v___y_237_ = v___x_258_;
v___y_238_ = v___y_247_;
v___y_239_ = v___x_249_;
goto v___jp_236_;
}
else
{
uint32_t v___x_259_; uint32_t v___x_260_; uint8_t v___x_261_; 
v___x_259_ = 90;
v___x_260_ = lean_unbox_uint32(v_val_254_);
v___x_261_ = lean_uint32_dec_le(v___x_260_, v___x_259_);
if (v___x_261_ == 0)
{
uint32_t v___x_262_; 
v___x_262_ = lean_unbox_uint32(v_val_254_);
lean_dec(v_val_254_);
v___y_237_ = v___x_262_;
v___y_238_ = v___y_247_;
v___y_239_ = v___x_249_;
goto v___jp_236_;
}
else
{
lean_dec(v_val_254_);
v___y_232_ = v___y_247_;
v___y_233_ = v___x_249_;
v_val_234_ = v___x_252_;
goto v___jp_231_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___boxed(lean_object* v_config_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_345_, v_a_346_);
lean_dec_ref(v_config_345_);
return v_res_347_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(uint8_t v___y_348_){
_start:
{
uint8_t v___x_349_; uint8_t v___x_350_; 
v___x_349_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_350_ = lean_uint8_dec_le(v___x_349_, v___y_348_);
if (v___x_350_ == 0)
{
return v___x_350_;
}
else
{
uint8_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_352_ = lean_uint8_dec_le(v___y_348_, v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0___boxed(lean_object* v___y_353_){
_start:
{
uint8_t v___y_600__boxed_354_; uint8_t v_res_355_; lean_object* v_r_356_; 
v___y_600__boxed_354_ = lean_unbox(v___y_353_);
v_res_355_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___lam__0(v___y_600__boxed_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(lean_object* v_a_360_){
_start:
{
lean_object* v___f_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_fst_365_; lean_object* v_snd_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_436_; 
v___f_361_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__0));
v___x_362_ = lean_unsigned_to_nat(5u);
v___x_363_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_360_);
v___x_364_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_361_, v___x_362_, v___x_363_, v_a_360_);
v_fst_365_ = lean_ctor_get(v___x_364_, 0);
v_snd_366_ = lean_ctor_get(v___x_364_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_436_ == 0)
{
v___x_368_ = v___x_364_;
v_isShared_369_ = v_isSharedCheck_436_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_snd_366_);
lean_inc(v_fst_365_);
lean_dec(v___x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_436_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___y_371_; uint8_t v___x_402_; 
v___x_402_ = lean_nat_dec_eq(v_fst_365_, v___x_363_);
if (v___x_402_ == 0)
{
lean_object* v_array_403_; lean_object* v_idx_404_; lean_object* v_lower_406_; lean_object* v_upper_407_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___y_417_; uint8_t v___x_419_; 
v_array_403_ = lean_ctor_get(v_a_360_, 0);
lean_inc_ref(v_array_403_);
v_idx_404_ = lean_ctor_get(v_a_360_, 1);
lean_inc(v_idx_404_);
lean_dec_ref(v_a_360_);
v___x_414_ = lean_nat_add(v_idx_404_, v_fst_365_);
lean_dec(v_fst_365_);
v___x_415_ = lean_byte_array_size(v_array_403_);
v___x_419_ = lean_nat_dec_le(v_idx_404_, v___x_363_);
if (v___x_419_ == 0)
{
v___y_417_ = v_idx_404_;
goto v___jp_416_;
}
else
{
lean_dec(v_idx_404_);
v___y_417_ = v___x_363_;
goto v___jp_416_;
}
v___jp_405_:
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = l_ByteArray_toByteSlice(v_array_403_, v_lower_406_, v_upper_407_);
v___x_409_ = l_ByteSlice_toByteArray(v___x_408_);
v___x_410_ = lean_string_validate_utf8(v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___x_409_);
v___x_411_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6);
v___x_412_ = l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_411_);
v___y_371_ = v___x_412_;
goto v___jp_370_;
}
else
{
lean_object* v___x_413_; 
v___x_413_ = lean_string_from_utf8_unchecked(v___x_409_);
v___y_371_ = v___x_413_;
goto v___jp_370_;
}
}
v___jp_416_:
{
uint8_t v___x_418_; 
v___x_418_ = lean_nat_dec_le(v___x_414_, v___x_415_);
if (v___x_418_ == 0)
{
lean_dec(v___x_414_);
v_lower_406_ = v___y_417_;
v_upper_407_ = v___x_415_;
goto v___jp_405_;
}
else
{
v_lower_406_ = v___y_417_;
v_upper_407_ = v___x_414_;
goto v___jp_405_;
}
}
}
else
{
lean_object* v_array_420_; lean_object* v_idx_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_435_; 
lean_del_object(v___x_368_);
lean_dec(v_fst_365_);
v_array_420_ = lean_ctor_get(v_snd_366_, 0);
v_idx_421_ = lean_ctor_get(v_snd_366_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_snd_366_);
if (v_isSharedCheck_435_ == 0)
{
v___x_423_ = v_snd_366_;
v_isShared_424_ = v_isSharedCheck_435_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_idx_421_);
lean_inc(v_array_420_);
lean_dec(v_snd_366_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_435_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_byte_array_size(v_array_420_);
lean_dec_ref(v_array_420_);
v___x_426_ = lean_nat_dec_le(v___x_425_, v_idx_421_);
lean_dec(v_idx_421_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9));
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 1);
lean_ctor_set(v___x_423_, 1, v___x_427_);
lean_ctor_set(v___x_423_, 0, v_a_360_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_360_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_box(0);
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 1);
lean_ctor_set(v___x_423_, 1, v___x_431_);
lean_ctor_set(v___x_423_, 0, v_a_360_);
v___x_433_ = v___x_423_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_360_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_431_);
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
v___jp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_string_utf8_byte_size(v___y_371_);
lean_inc_ref(v___y_371_);
v___x_373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_373_, 0, v___y_371_);
lean_ctor_set(v___x_373_, 1, v___x_363_);
lean_ctor_set(v___x_373_, 2, v___x_372_);
v___x_374_ = l_String_Slice_toNat_x3f(v___x_373_);
lean_dec_ref(v___x_373_);
if (lean_obj_tag(v___x_374_) == 1)
{
lean_object* v_val_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_395_; 
lean_dec_ref(v___y_371_);
v_val_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_395_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_395_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_val_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_395_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(65535u);
v___x_380_ = lean_nat_dec_lt(v___x_379_, v_val_375_);
if (v___x_380_ == 0)
{
uint16_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
lean_del_object(v___x_377_);
v___x_381_ = lean_uint16_of_nat(v_val_375_);
lean_dec(v_val_375_);
v___x_382_ = lean_box(v___x_381_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_382_);
lean_ctor_set(v___x_368_, 0, v_snd_366_);
v___x_384_ = v___x_368_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_snd_366_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_386_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__1));
v___x_387_ = l_Nat_reprFast(v_val_375_);
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
lean_dec_ref(v___x_387_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_388_);
v___x_390_ = v___x_377_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 1);
lean_ctor_set(v___x_368_, 1, v___x_390_);
lean_ctor_set(v___x_368_, 0, v_snd_366_);
v___x_392_ = v___x_368_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_snd_366_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
lean_dec(v___x_374_);
v___x_396_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber___closed__2));
v___x_397_ = lean_string_append(v___x_396_, v___y_371_);
lean_dec_ref(v___y_371_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 1);
lean_ctor_set(v___x_368_, 1, v___x_398_);
lean_ctor_set(v___x_368_, 0, v_snd_366_);
v___x_400_ = v___x_368_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_snd_366_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0(void){
_start:
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 58;
v___x_438_ = lean_uint32_to_uint8(v___x_437_);
return v___x_438_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1(void){
_start:
{
uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 37;
v___x_440_ = lean_uint32_to_uint8(v___x_439_);
return v___x_440_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2(void){
_start:
{
uint32_t v___x_441_; uint8_t v___x_442_; 
v___x_441_ = 38;
v___x_442_ = lean_uint32_to_uint8(v___x_441_);
return v___x_442_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3(void){
_start:
{
uint32_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 39;
v___x_444_ = lean_uint32_to_uint8(v___x_443_);
return v___x_444_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4(void){
_start:
{
uint32_t v___x_445_; uint8_t v___x_446_; 
v___x_445_ = 40;
v___x_446_ = lean_uint32_to_uint8(v___x_445_);
return v___x_446_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5(void){
_start:
{
uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_447_ = 41;
v___x_448_ = lean_uint32_to_uint8(v___x_447_);
return v___x_448_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6(void){
_start:
{
uint32_t v___x_449_; uint8_t v___x_450_; 
v___x_449_ = 42;
v___x_450_ = lean_uint32_to_uint8(v___x_449_);
return v___x_450_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7(void){
_start:
{
uint32_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 44;
v___x_452_ = lean_uint32_to_uint8(v___x_451_);
return v___x_452_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8(void){
_start:
{
uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 59;
v___x_454_ = lean_uint32_to_uint8(v___x_453_);
return v___x_454_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9(void){
_start:
{
uint32_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 61;
v___x_456_ = lean_uint32_to_uint8(v___x_455_);
return v___x_456_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10(void){
_start:
{
uint32_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = 33;
v___x_458_ = lean_uint32_to_uint8(v___x_457_);
return v___x_458_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11(void){
_start:
{
uint32_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 36;
v___x_460_ = lean_uint32_to_uint8(v___x_459_);
return v___x_460_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12(void){
_start:
{
uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 95;
v___x_462_ = lean_uint32_to_uint8(v___x_461_);
return v___x_462_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13(void){
_start:
{
uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 126;
v___x_464_ = lean_uint32_to_uint8(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(uint8_t v_x_465_){
_start:
{
uint8_t v___y_467_; uint8_t v___y_473_; uint8_t v___y_493_; uint8_t v___y_499_; uint8_t v___y_505_; uint8_t v___y_511_; uint8_t v___y_517_; uint8_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_523_ = lean_uint8_dec_eq(v_x_465_, v___x_522_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_525_ = lean_uint8_dec_le(v___x_524_, v_x_465_);
if (v___x_525_ == 0)
{
v___y_517_ = v___x_525_;
goto v___jp_516_;
}
else
{
uint8_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_527_ = lean_uint8_dec_le(v_x_465_, v___x_526_);
v___y_517_ = v___x_527_;
goto v___jp_516_;
}
}
else
{
uint8_t v___x_528_; 
v___x_528_ = 0;
return v___x_528_;
}
v___jp_466_:
{
if (v___y_467_ == 0)
{
uint8_t v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_469_ = lean_uint8_dec_eq(v_x_465_, v___x_468_);
if (v___x_469_ == 0)
{
uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_471_ = lean_uint8_dec_eq(v_x_465_, v___x_470_);
if (v___x_471_ == 0)
{
return v___x_469_;
}
else
{
return v___x_471_;
}
}
else
{
return v___x_469_;
}
}
else
{
return v___y_467_;
}
}
v___jp_472_:
{
if (v___y_473_ == 0)
{
uint8_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_475_ = lean_uint8_dec_eq(v_x_465_, v___x_474_);
if (v___x_475_ == 0)
{
uint8_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_477_ = lean_uint8_dec_eq(v_x_465_, v___x_476_);
if (v___x_477_ == 0)
{
uint8_t v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_479_ = lean_uint8_dec_eq(v_x_465_, v___x_478_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_481_ = lean_uint8_dec_eq(v_x_465_, v___x_480_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_483_ = lean_uint8_dec_eq(v_x_465_, v___x_482_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_485_ = lean_uint8_dec_eq(v_x_465_, v___x_484_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_487_ = lean_uint8_dec_eq(v_x_465_, v___x_486_);
if (v___x_487_ == 0)
{
uint8_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_489_ = lean_uint8_dec_eq(v_x_465_, v___x_488_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_491_ = lean_uint8_dec_eq(v_x_465_, v___x_490_);
v___y_467_ = v___x_491_;
goto v___jp_466_;
}
else
{
v___y_467_ = v___x_489_;
goto v___jp_466_;
}
}
else
{
v___y_467_ = v___x_487_;
goto v___jp_466_;
}
}
else
{
v___y_467_ = v___x_485_;
goto v___jp_466_;
}
}
else
{
v___y_467_ = v___x_483_;
goto v___jp_466_;
}
}
else
{
v___y_467_ = v___x_481_;
goto v___jp_466_;
}
}
else
{
v___y_467_ = v___x_479_;
goto v___jp_466_;
}
}
else
{
v___y_467_ = v___x_477_;
goto v___jp_466_;
}
}
else
{
v___y_467_ = v___x_475_;
goto v___jp_466_;
}
}
else
{
return v___y_473_;
}
}
v___jp_492_:
{
if (v___y_493_ == 0)
{
uint8_t v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_495_ = lean_uint8_dec_eq(v_x_465_, v___x_494_);
if (v___x_495_ == 0)
{
uint8_t v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_497_ = lean_uint8_dec_eq(v_x_465_, v___x_496_);
v___y_473_ = v___x_497_;
goto v___jp_472_;
}
else
{
v___y_473_ = v___x_495_;
goto v___jp_472_;
}
}
else
{
return v___y_493_;
}
}
v___jp_498_:
{
if (v___y_499_ == 0)
{
uint8_t v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_501_ = lean_uint8_dec_eq(v_x_465_, v___x_500_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_503_ = lean_uint8_dec_eq(v_x_465_, v___x_502_);
v___y_493_ = v___x_503_;
goto v___jp_492_;
}
else
{
v___y_493_ = v___x_501_;
goto v___jp_492_;
}
}
else
{
return v___y_499_;
}
}
v___jp_504_:
{
if (v___y_505_ == 0)
{
uint8_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_507_ = lean_uint8_dec_eq(v_x_465_, v___x_506_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_509_ = lean_uint8_dec_eq(v_x_465_, v___x_508_);
v___y_499_ = v___x_509_;
goto v___jp_498_;
}
else
{
v___y_499_ = v___x_507_;
goto v___jp_498_;
}
}
else
{
return v___y_505_;
}
}
v___jp_510_:
{
if (v___y_511_ == 0)
{
uint8_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_513_ = lean_uint8_dec_le(v___x_512_, v_x_465_);
if (v___x_513_ == 0)
{
v___y_505_ = v___x_513_;
goto v___jp_504_;
}
else
{
uint8_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_515_ = lean_uint8_dec_le(v_x_465_, v___x_514_);
v___y_505_ = v___x_515_;
goto v___jp_504_;
}
}
else
{
return v___y_511_;
}
}
v___jp_516_:
{
if (v___y_517_ == 0)
{
uint8_t v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_519_ = lean_uint8_dec_le(v___x_518_, v_x_465_);
if (v___x_519_ == 0)
{
v___y_511_ = v___x_519_;
goto v___jp_510_;
}
else
{
uint8_t v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_521_ = lean_uint8_dec_le(v_x_465_, v___x_520_);
v___y_511_ = v___x_521_;
goto v___jp_510_;
}
}
else
{
return v___y_517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___boxed(lean_object* v_x_529_){
_start:
{
uint8_t v_x_boxed_530_; uint8_t v_res_531_; lean_object* v_r_532_; 
v_x_boxed_530_ = lean_unbox(v_x_529_);
v_res_531_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0(v_x_boxed_530_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(uint8_t v___x_533_, uint8_t v___x_534_, uint8_t v_x_535_){
_start:
{
uint8_t v___y_537_; uint8_t v___y_542_; uint8_t v___y_562_; uint8_t v___y_568_; uint8_t v___y_574_; uint8_t v___y_580_; uint8_t v___y_586_; uint8_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_592_ = lean_uint8_dec_le(v___x_591_, v_x_535_);
if (v___x_592_ == 0)
{
v___y_586_ = v___x_592_;
goto v___jp_585_;
}
else
{
uint8_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_594_ = lean_uint8_dec_le(v_x_535_, v___x_593_);
v___y_586_ = v___x_594_;
goto v___jp_585_;
}
v___jp_536_:
{
if (v___y_537_ == 0)
{
uint8_t v___x_538_; 
v___x_538_ = lean_uint8_dec_eq(v_x_535_, v___x_533_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_540_ = lean_uint8_dec_eq(v_x_535_, v___x_539_);
if (v___x_540_ == 0)
{
return v___x_538_;
}
else
{
return v___x_534_;
}
}
else
{
return v___x_538_;
}
}
else
{
return v___y_537_;
}
}
v___jp_541_:
{
if (v___y_542_ == 0)
{
uint8_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_544_ = lean_uint8_dec_eq(v_x_535_, v___x_543_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_546_ = lean_uint8_dec_eq(v_x_535_, v___x_545_);
if (v___x_546_ == 0)
{
uint8_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_548_ = lean_uint8_dec_eq(v_x_535_, v___x_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_550_ = lean_uint8_dec_eq(v_x_535_, v___x_549_);
if (v___x_550_ == 0)
{
uint8_t v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_552_ = lean_uint8_dec_eq(v_x_535_, v___x_551_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_554_ = lean_uint8_dec_eq(v_x_535_, v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_556_ = lean_uint8_dec_eq(v_x_535_, v___x_555_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_558_ = lean_uint8_dec_eq(v_x_535_, v___x_557_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_560_ = lean_uint8_dec_eq(v_x_535_, v___x_559_);
v___y_537_ = v___x_560_;
goto v___jp_536_;
}
else
{
v___y_537_ = v___x_558_;
goto v___jp_536_;
}
}
else
{
v___y_537_ = v___x_556_;
goto v___jp_536_;
}
}
else
{
v___y_537_ = v___x_554_;
goto v___jp_536_;
}
}
else
{
v___y_537_ = v___x_552_;
goto v___jp_536_;
}
}
else
{
v___y_537_ = v___x_550_;
goto v___jp_536_;
}
}
else
{
v___y_537_ = v___x_548_;
goto v___jp_536_;
}
}
else
{
v___y_537_ = v___x_546_;
goto v___jp_536_;
}
}
else
{
v___y_537_ = v___x_544_;
goto v___jp_536_;
}
}
else
{
return v___y_542_;
}
}
v___jp_561_:
{
if (v___y_562_ == 0)
{
uint8_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_564_ = lean_uint8_dec_eq(v_x_535_, v___x_563_);
if (v___x_564_ == 0)
{
uint8_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_566_ = lean_uint8_dec_eq(v_x_535_, v___x_565_);
v___y_542_ = v___x_566_;
goto v___jp_541_;
}
else
{
v___y_542_ = v___x_564_;
goto v___jp_541_;
}
}
else
{
return v___y_562_;
}
}
v___jp_567_:
{
if (v___y_568_ == 0)
{
uint8_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_570_ = lean_uint8_dec_eq(v_x_535_, v___x_569_);
if (v___x_570_ == 0)
{
uint8_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_572_ = lean_uint8_dec_eq(v_x_535_, v___x_571_);
v___y_562_ = v___x_572_;
goto v___jp_561_;
}
else
{
v___y_562_ = v___x_570_;
goto v___jp_561_;
}
}
else
{
return v___y_568_;
}
}
v___jp_573_:
{
if (v___y_574_ == 0)
{
uint8_t v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_576_ = lean_uint8_dec_eq(v_x_535_, v___x_575_);
if (v___x_576_ == 0)
{
uint8_t v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_578_ = lean_uint8_dec_eq(v_x_535_, v___x_577_);
v___y_568_ = v___x_578_;
goto v___jp_567_;
}
else
{
v___y_568_ = v___x_576_;
goto v___jp_567_;
}
}
else
{
return v___y_574_;
}
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
uint8_t v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_582_ = lean_uint8_dec_le(v___x_581_, v_x_535_);
if (v___x_582_ == 0)
{
v___y_574_ = v___x_582_;
goto v___jp_573_;
}
else
{
uint8_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_584_ = lean_uint8_dec_le(v_x_535_, v___x_583_);
v___y_574_ = v___x_584_;
goto v___jp_573_;
}
}
else
{
return v___y_580_;
}
}
v___jp_585_:
{
if (v___y_586_ == 0)
{
uint8_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_588_ = lean_uint8_dec_le(v___x_587_, v_x_535_);
if (v___x_588_ == 0)
{
v___y_580_ = v___x_588_;
goto v___jp_579_;
}
else
{
uint8_t v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_590_ = lean_uint8_dec_le(v_x_535_, v___x_589_);
v___y_580_ = v___x_590_;
goto v___jp_579_;
}
}
else
{
return v___y_586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed(lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v_x_597_){
_start:
{
uint8_t v___x_4635__boxed_598_; uint8_t v___x_4636__boxed_599_; uint8_t v_x_boxed_600_; uint8_t v_res_601_; lean_object* v_r_602_; 
v___x_4635__boxed_598_ = lean_unbox(v___x_595_);
v___x_4636__boxed_599_ = lean_unbox(v___x_596_);
v_x_boxed_600_ = lean_unbox(v_x_597_);
v_res_601_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1(v___x_4635__boxed_598_, v___x_4636__boxed_599_, v_x_boxed_600_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(lean_object* v_config_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___y_610_; lean_object* v_userPassEncoded_611_; lean_object* v___y_612_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v_lower_619_; lean_object* v_upper_620_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_635_; lean_object* v_pos_636_; lean_object* v_maxUserInfoLength_638_; lean_object* v___f_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_fst_642_; lean_object* v_snd_643_; lean_object* v_array_644_; lean_object* v_idx_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_696_; 
v_maxUserInfoLength_638_ = lean_ctor_get(v_config_607_, 2);
v___f_639_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__2));
v___x_640_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_608_);
v___x_641_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_639_, v_maxUserInfoLength_638_, v___x_640_, v_a_608_);
v_fst_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_fst_642_);
v_snd_643_ = lean_ctor_get(v___x_641_, 1);
lean_inc(v_snd_643_);
lean_dec_ref(v___x_641_);
v_array_644_ = lean_ctor_get(v_a_608_, 0);
v_idx_645_ = lean_ctor_get(v_a_608_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_696_ == 0)
{
v___x_647_ = v_a_608_;
v_isShared_648_ = v_isSharedCheck_696_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_idx_645_);
lean_inc(v_array_644_);
lean_dec(v_a_608_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_696_;
goto v_resetjp_646_;
}
v___jp_609_:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___y_610_);
lean_ctor_set(v___x_613_, 1, v_userPassEncoded_611_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___y_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
return v___x_614_;
}
v___jp_615_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = l_ByteArray_toByteSlice(v___y_616_, v_lower_619_, v_upper_620_);
v___x_622_ = l_ByteSlice_toByteArray(v___x_621_);
v___x_623_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_622_);
if (lean_obj_tag(v___x_623_) == 1)
{
v___y_610_ = v___y_618_;
v_userPassEncoded_611_ = v___x_623_;
v___y_612_ = v___y_617_;
goto v___jp_609_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v___x_623_);
lean_dec_ref(v___y_618_);
v___x_624_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___y_617_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
}
v___jp_626_:
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_le(v___y_630_, v___y_628_);
if (v___x_633_ == 0)
{
lean_dec(v___y_630_);
v___y_616_ = v___y_627_;
v___y_617_ = v___y_629_;
v___y_618_ = v___y_631_;
v_lower_619_ = v___y_632_;
v_upper_620_ = v___y_628_;
goto v___jp_615_;
}
else
{
lean_dec(v___y_628_);
v___y_616_ = v___y_627_;
v___y_617_ = v___y_629_;
v___y_618_ = v___y_631_;
v_lower_619_ = v___y_632_;
v_upper_620_ = v___y_630_;
goto v___jp_615_;
}
}
v___jp_634_:
{
lean_object* v___x_637_; 
v___x_637_ = lean_box(0);
v___y_610_ = v___y_635_;
v_userPassEncoded_611_ = v___x_637_;
v___y_612_ = v_pos_636_;
goto v___jp_609_;
}
v_resetjp_646_:
{
lean_object* v_lower_650_; lean_object* v_upper_651_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___y_693_; uint8_t v___x_695_; 
v___x_690_ = lean_nat_add(v_idx_645_, v_fst_642_);
lean_dec(v_fst_642_);
v___x_691_ = lean_byte_array_size(v_array_644_);
v___x_695_ = lean_nat_dec_le(v_idx_645_, v___x_640_);
if (v___x_695_ == 0)
{
v___y_693_ = v_idx_645_;
goto v___jp_692_;
}
else
{
lean_dec(v_idx_645_);
v___y_693_ = v___x_640_;
goto v___jp_692_;
}
v___jp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = l_ByteArray_toByteSlice(v_array_644_, v_lower_650_, v_upper_651_);
v___x_653_ = l_ByteSlice_toByteArray(v___x_652_);
v___x_654_ = l_Std_Http_URI_EncodedUserInfo_ofByteArray_x3f(v___x_653_);
if (lean_obj_tag(v___x_654_) == 1)
{
lean_object* v_val_655_; lean_object* v_array_656_; lean_object* v_idx_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_val_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_val_655_);
lean_dec_ref(v___x_654_);
v_array_656_ = lean_ctor_get(v_snd_643_, 0);
v_idx_657_ = lean_ctor_get(v_snd_643_, 1);
v___x_658_ = lean_byte_array_size(v_array_656_);
v___x_659_ = lean_nat_dec_lt(v_idx_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_del_object(v___x_647_);
v___y_635_ = v_val_655_;
v_pos_636_ = v_snd_643_;
goto v___jp_634_;
}
else
{
uint8_t v___x_660_; uint8_t v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_byte_array_fget(v_array_656_, v_idx_657_);
v___x_661_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_662_ = lean_uint8_dec_eq(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_del_object(v___x_647_);
v___y_635_ = v_val_655_;
v_pos_636_ = v_snd_643_;
goto v___jp_634_;
}
else
{
if (v___x_662_ == 0)
{
lean_del_object(v___x_647_);
v___y_635_ = v_val_655_;
v_pos_636_ = v_snd_643_;
goto v___jp_634_;
}
else
{
if (v___x_659_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_665_; 
lean_dec(v_val_655_);
v___x_663_ = lean_box(0);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 1);
lean_ctor_set(v___x_647_, 1, v___x_663_);
lean_ctor_set(v___x_647_, 0, v_snd_643_);
v___x_665_ = v___x_647_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_snd_643_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_683_; 
lean_inc(v_idx_657_);
lean_inc_ref(v_array_656_);
lean_del_object(v___x_647_);
v_isSharedCheck_683_ = !lean_is_exclusive(v_snd_643_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_684_ = lean_ctor_get(v_snd_643_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_snd_643_, 0);
lean_dec(v_unused_685_);
v___x_668_ = v_snd_643_;
v_isShared_669_ = v_isSharedCheck_683_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_snd_643_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_683_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___f_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_670_ = lean_box(v___x_661_);
v___x_671_ = lean_box(v___x_659_);
v___f_672_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__1___boxed), 3, 2);
lean_closure_set(v___f_672_, 0, v___x_670_);
lean_closure_set(v___f_672_, 1, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_idx_657_, v___x_673_);
lean_dec(v_idx_657_);
lean_inc(v___x_674_);
lean_inc_ref(v_array_656_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_674_);
v___x_676_ = v___x_668_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_array_656_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_674_);
v___x_676_ = v_reuseFailAlloc_682_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v_fst_678_; lean_object* v_snd_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_677_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_672_, v_maxUserInfoLength_638_, v___x_640_, v___x_676_);
v_fst_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_fst_678_);
v_snd_679_ = lean_ctor_get(v___x_677_, 1);
lean_inc(v_snd_679_);
lean_dec_ref(v___x_677_);
v___x_680_ = lean_nat_add(v___x_674_, v_fst_678_);
lean_dec(v_fst_678_);
v___x_681_ = lean_nat_dec_le(v___x_674_, v___x_640_);
if (v___x_681_ == 0)
{
v___y_627_ = v_array_656_;
v___y_628_ = v___x_658_;
v___y_629_ = v_snd_679_;
v___y_630_ = v___x_680_;
v___y_631_ = v_val_655_;
v___y_632_ = v___x_674_;
goto v___jp_626_;
}
else
{
lean_dec(v___x_674_);
v___y_627_ = v_array_656_;
v___y_628_ = v___x_658_;
v___y_629_ = v_snd_679_;
v___y_630_ = v___x_680_;
v___y_631_ = v_val_655_;
v___y_632_ = v___x_640_;
goto v___jp_626_;
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
lean_object* v___x_686_; lean_object* v___x_688_; 
lean_dec(v___x_654_);
v___x_686_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___closed__1));
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 1);
lean_ctor_set(v___x_647_, 1, v___x_686_);
lean_ctor_set(v___x_647_, 0, v_snd_643_);
v___x_688_ = v___x_647_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_snd_643_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
v___jp_692_:
{
uint8_t v___x_694_; 
v___x_694_ = lean_nat_dec_le(v___x_690_, v___x_691_);
if (v___x_694_ == 0)
{
lean_dec(v___x_690_);
v_lower_650_ = v___y_693_;
v_upper_651_ = v___x_691_;
goto v___jp_649_;
}
else
{
v_lower_650_ = v___y_693_;
v_upper_651_ = v___x_690_;
goto v___jp_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___boxed(lean_object* v_config_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_697_, v_a_698_);
lean_dec_ref(v_config_697_);
return v_res_699_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0(void){
_start:
{
uint32_t v___x_700_; uint8_t v___x_701_; 
v___x_700_ = 70;
v___x_701_ = lean_uint32_to_uint8(v___x_700_);
return v___x_701_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1(void){
_start:
{
uint32_t v___x_702_; uint8_t v___x_703_; 
v___x_702_ = 102;
v___x_703_ = lean_uint32_to_uint8(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(uint8_t v___x_704_, uint8_t v_x_705_){
_start:
{
uint8_t v___y_707_; uint8_t v___y_713_; uint8_t v___x_718_; uint8_t v___x_719_; 
v___x_718_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_719_ = lean_uint8_dec_eq(v_x_705_, v___x_718_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_721_ = lean_uint8_dec_eq(v_x_705_, v___x_720_);
if (v___x_721_ == 0)
{
uint8_t v___x_722_; uint8_t v___x_723_; 
v___x_722_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_723_ = lean_uint8_dec_le(v___x_722_, v_x_705_);
if (v___x_723_ == 0)
{
v___y_713_ = v___x_723_;
goto v___jp_712_;
}
else
{
uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_725_ = lean_uint8_dec_le(v_x_705_, v___x_724_);
v___y_713_ = v___x_725_;
goto v___jp_712_;
}
}
else
{
return v___x_704_;
}
}
else
{
return v___x_704_;
}
v___jp_706_:
{
if (v___y_707_ == 0)
{
uint8_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_709_ = lean_uint8_dec_le(v___x_708_, v_x_705_);
if (v___x_709_ == 0)
{
if (v___x_709_ == 0)
{
return v___x_709_;
}
else
{
return v___x_704_;
}
}
else
{
uint8_t v___x_710_; uint8_t v___x_711_; 
v___x_710_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__0);
v___x_711_ = lean_uint8_dec_le(v_x_705_, v___x_710_);
if (v___x_711_ == 0)
{
return v___x_711_;
}
else
{
return v___x_704_;
}
}
}
else
{
return v___x_704_;
}
}
v___jp_712_:
{
if (v___y_713_ == 0)
{
uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_715_ = lean_uint8_dec_le(v___x_714_, v_x_705_);
if (v___x_715_ == 0)
{
v___y_707_ = v___x_715_;
goto v___jp_706_;
}
else
{
uint8_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___closed__1);
v___x_717_ = lean_uint8_dec_le(v_x_705_, v___x_716_);
v___y_707_ = v___x_717_;
goto v___jp_706_;
}
}
else
{
return v___x_704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed(lean_object* v___x_726_, lean_object* v_x_727_){
_start:
{
uint8_t v___x_1506__boxed_728_; uint8_t v_x_boxed_729_; uint8_t v_res_730_; lean_object* v_r_731_; 
v___x_1506__boxed_728_ = lean_unbox(v___x_726_);
v_x_boxed_729_ = lean_unbox(v_x_727_);
v_res_730_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0(v___x_1506__boxed_728_, v_x_boxed_729_);
v_r_731_ = lean_box(v_res_730_);
return v_r_731_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1(void){
_start:
{
uint32_t v___x_733_; uint8_t v___x_734_; 
v___x_733_ = 91;
v___x_734_ = lean_uint32_to_uint8(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3(void){
_start:
{
uint8_t v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_737_ = lean_uint8_to_nat(v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__3);
v___x_739_ = l_Nat_reprFast(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__4);
v___x_741_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_742_ = lean_string_append(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_745_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__5);
v___x_746_ = lean_string_append(v___x_745_, v___x_744_);
return v___x_746_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__7);
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9(void){
_start:
{
uint32_t v___x_749_; uint8_t v___x_750_; 
v___x_749_ = 93;
v___x_750_ = lean_uint32_to_uint8(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10(void){
_start:
{
uint8_t v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9);
v___x_752_ = lean_uint8_to_nat(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__10);
v___x_754_ = l_Nat_reprFast(v___x_753_);
return v___x_754_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_755_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__11);
v___x_756_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_757_ = lean_string_append(v___x_756_, v___x_755_);
return v___x_757_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_759_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__12);
v___x_760_ = lean_string_append(v___x_759_, v___x_758_);
return v___x_760_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__13);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(lean_object* v_a_763_){
_start:
{
lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v_array_774_; lean_object* v_idx_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_array_774_ = lean_ctor_get(v_a_763_, 0);
v_idx_775_ = lean_ctor_get(v_a_763_, 1);
v___x_776_ = lean_byte_array_size(v_array_774_);
v___x_777_ = lean_nat_dec_lt(v_idx_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_box(0);
v___x_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_779_, 0, v_a_763_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
return v___x_779_;
}
else
{
uint8_t v___x_780_; uint8_t v_c_781_; uint8_t v___x_782_; 
v___x_780_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v_c_781_ = lean_byte_array_fget(v_array_774_, v_idx_775_);
v___x_782_ = lean_uint8_dec_eq(v_c_781_, v___x_780_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__8);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_763_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
return v___x_784_;
}
else
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_855_; 
lean_inc(v_idx_775_);
lean_inc_ref(v_array_774_);
v_isSharedCheck_855_ = !lean_is_exclusive(v_a_763_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; 
v_unused_856_ = lean_ctor_get(v_a_763_, 1);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_a_763_, 0);
lean_dec(v_unused_857_);
v___x_786_ = v_a_763_;
v_isShared_787_ = v_isSharedCheck_855_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_a_763_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_855_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_it_x27_793_; 
v___x_788_ = lean_box(v___x_777_);
v___f_789_ = lean_alloc_closure((void*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___lam__0___boxed), 2, 1);
lean_closure_set(v___f_789_, 0, v___x_788_);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_add(v_idx_775_, v___x_790_);
lean_dec(v_idx_775_);
lean_inc(v___x_791_);
lean_inc_ref(v_array_774_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_791_);
v_it_x27_793_ = v___x_786_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_array_774_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_791_);
v_it_x27_793_ = v_reuseFailAlloc_854_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_fst_797_; lean_object* v_snd_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_853_; 
v___x_794_ = lean_unsigned_to_nat(256u);
v___x_795_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_it_x27_793_);
v___x_796_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_789_, v___x_794_, v___x_795_, v_it_x27_793_);
v_fst_797_ = lean_ctor_get(v___x_796_, 0);
v_snd_798_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_853_ == 0)
{
v___x_800_ = v___x_796_;
v_isShared_801_ = v_isSharedCheck_853_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_798_);
lean_inc(v_fst_797_);
lean_dec(v___x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_853_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___y_803_; uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_eq(v_fst_797_, v___x_795_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___y_840_; uint8_t v___x_844_; 
lean_dec_ref(v_it_x27_793_);
v___x_838_ = lean_nat_add(v___x_791_, v_fst_797_);
lean_dec(v_fst_797_);
v___x_844_ = lean_nat_dec_le(v___x_791_, v___x_795_);
if (v___x_844_ == 0)
{
v___y_840_ = v___x_791_;
goto v___jp_839_;
}
else
{
lean_dec(v___x_791_);
v___y_840_ = v___x_795_;
goto v___jp_839_;
}
v___jp_839_:
{
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_le(v___x_838_, v___x_776_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_dec(v___x_838_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v___y_840_);
lean_ctor_set(v___x_842_, 1, v___x_776_);
v___y_803_ = v___x_842_;
goto v___jp_802_;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v___y_840_);
lean_ctor_set(v___x_843_, 1, v___x_838_);
v___y_803_ = v___x_843_;
goto v___jp_802_;
}
}
}
else
{
lean_object* v_array_845_; lean_object* v_idx_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
lean_del_object(v___x_800_);
lean_dec(v_fst_797_);
lean_dec(v___x_791_);
lean_dec_ref(v_array_774_);
v_array_845_ = lean_ctor_get(v_snd_798_, 0);
lean_inc_ref(v_array_845_);
v_idx_846_ = lean_ctor_get(v_snd_798_, 1);
lean_inc(v_idx_846_);
lean_dec(v_snd_798_);
v___x_847_ = lean_byte_array_size(v_array_845_);
lean_dec_ref(v_array_845_);
v___x_848_ = lean_nat_dec_le(v___x_847_, v_idx_846_);
lean_dec(v_idx_846_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9));
v___x_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_850_, 0, v_it_x27_793_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_box(0);
v___x_852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_852_, 0, v_it_x27_793_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
return v___x_852_;
}
}
v___jp_802_:
{
lean_object* v_array_804_; lean_object* v_idx_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_array_804_ = lean_ctor_get(v_snd_798_, 0);
v_idx_805_ = lean_ctor_get(v_snd_798_, 1);
v___x_806_ = lean_byte_array_size(v_array_804_);
v___x_807_ = lean_nat_dec_lt(v_idx_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec_ref(v___y_803_);
lean_dec_ref(v_array_774_);
v___x_808_ = lean_box(0);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 1);
lean_ctor_set(v___x_800_, 1, v___x_808_);
lean_ctor_set(v___x_800_, 0, v_snd_798_);
v___x_810_ = v___x_800_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_snd_798_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
uint8_t v___x_812_; uint8_t v_c_813_; uint8_t v___x_814_; 
v___x_812_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__9);
v_c_813_ = lean_byte_array_fget(v_array_804_, v_idx_805_);
v___x_814_ = lean_uint8_dec_eq(v_c_813_, v___x_812_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref(v___y_803_);
lean_dec_ref(v_array_774_);
v___x_815_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__14);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 1);
lean_ctor_set(v___x_800_, 1, v___x_815_);
lean_ctor_set(v___x_800_, 0, v_snd_798_);
v___x_817_ = v___x_800_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_snd_798_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_834_; 
lean_inc(v_idx_805_);
lean_inc_ref(v_array_804_);
lean_del_object(v___x_800_);
v_isSharedCheck_834_ = !lean_is_exclusive(v_snd_798_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; lean_object* v_unused_836_; 
v_unused_835_ = lean_ctor_get(v_snd_798_, 1);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_snd_798_, 0);
lean_dec(v_unused_836_);
v___x_820_ = v_snd_798_;
v_isShared_821_ = v_isSharedCheck_834_;
goto v_resetjp_819_;
}
else
{
lean_dec(v_snd_798_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_834_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_lower_822_; lean_object* v_upper_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_it_x27_827_; 
v_lower_822_ = lean_ctor_get(v___y_803_, 0);
lean_inc(v_lower_822_);
v_upper_823_ = lean_ctor_get(v___y_803_, 1);
lean_inc(v_upper_823_);
lean_dec_ref(v___y_803_);
v___x_824_ = l_ByteArray_toByteSlice(v_array_774_, v_lower_822_, v_upper_823_);
v___x_825_ = lean_nat_add(v_idx_805_, v___x_790_);
lean_dec(v_idx_805_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_825_);
v_it_x27_827_ = v___x_820_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_array_804_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_825_);
v_it_x27_827_ = v_reuseFailAlloc_833_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = l_ByteSlice_toByteArray(v___x_824_);
v___x_829_ = lean_string_validate_utf8(v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v___x_828_);
v___x_830_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6);
v___x_831_ = l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_830_);
v___y_765_ = v_it_x27_827_;
v___y_766_ = v___x_831_;
goto v___jp_764_;
}
else
{
lean_object* v___x_832_; 
v___x_832_ = lean_string_from_utf8_unchecked(v___x_828_);
v___y_765_ = v_it_x27_827_;
v___y_766_ = v___x_832_;
goto v___jp_764_;
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
v___jp_764_:
{
lean_object* v___x_767_; 
v___x_767_ = lean_uv_pton_v6(v___y_766_);
if (lean_obj_tag(v___x_767_) == 1)
{
lean_object* v_val_768_; lean_object* v___x_769_; 
lean_dec_ref(v___y_766_);
v_val_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_val_768_);
lean_dec_ref(v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___y_765_);
lean_ctor_set(v___x_769_, 1, v_val_768_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v___x_767_);
v___x_770_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__0));
v___x_771_ = lean_string_append(v___x_770_, v___y_766_);
lean_dec_ref(v___y_766_);
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___y_765_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
return v___x_773_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(uint8_t v_x_858_){
_start:
{
uint8_t v___x_859_; uint8_t v___x_860_; 
v___x_859_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_860_ = lean_uint8_dec_eq(v_x_858_, v___x_859_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; uint8_t v___x_862_; 
v___x_861_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_862_ = lean_uint8_dec_le(v___x_861_, v_x_858_);
if (v___x_862_ == 0)
{
return v___x_862_;
}
else
{
uint8_t v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_864_ = lean_uint8_dec_le(v_x_858_, v___x_863_);
return v___x_864_;
}
}
else
{
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0___boxed(lean_object* v_x_865_){
_start:
{
uint8_t v_x_boxed_866_; uint8_t v_res_867_; lean_object* v_r_868_; 
v_x_boxed_866_ = lean_unbox(v_x_865_);
v_res_867_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___lam__0(v_x_boxed_866_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(lean_object* v_a_871_){
_start:
{
lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_fst_876_; lean_object* v_snd_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_928_; 
v___f_872_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__0));
v___x_873_ = lean_unsigned_to_nat(256u);
v___x_874_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_871_);
v___x_875_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_872_, v___x_873_, v___x_874_, v_a_871_);
v_fst_876_ = lean_ctor_get(v___x_875_, 0);
v_snd_877_ = lean_ctor_get(v___x_875_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_928_ == 0)
{
v___x_879_ = v___x_875_;
v_isShared_880_ = v_isSharedCheck_928_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_snd_877_);
lean_inc(v_fst_876_);
lean_dec(v___x_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_928_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___y_882_; uint8_t v___x_894_; 
v___x_894_ = lean_nat_dec_eq(v_fst_876_, v___x_874_);
if (v___x_894_ == 0)
{
lean_object* v_array_895_; lean_object* v_idx_896_; lean_object* v_lower_898_; lean_object* v_upper_899_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___y_909_; uint8_t v___x_911_; 
v_array_895_ = lean_ctor_get(v_a_871_, 0);
lean_inc_ref(v_array_895_);
v_idx_896_ = lean_ctor_get(v_a_871_, 1);
lean_inc(v_idx_896_);
lean_dec_ref(v_a_871_);
v___x_906_ = lean_nat_add(v_idx_896_, v_fst_876_);
lean_dec(v_fst_876_);
v___x_907_ = lean_byte_array_size(v_array_895_);
v___x_911_ = lean_nat_dec_le(v_idx_896_, v___x_874_);
if (v___x_911_ == 0)
{
v___y_909_ = v_idx_896_;
goto v___jp_908_;
}
else
{
lean_dec(v_idx_896_);
v___y_909_ = v___x_874_;
goto v___jp_908_;
}
v___jp_897_:
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = l_ByteArray_toByteSlice(v_array_895_, v_lower_898_, v_upper_899_);
v___x_901_ = l_ByteSlice_toByteArray(v___x_900_);
v___x_902_ = lean_string_validate_utf8(v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec_ref(v___x_901_);
v___x_903_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__6);
v___x_904_ = l_panic___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__2(v___x_903_);
v___y_882_ = v___x_904_;
goto v___jp_881_;
}
else
{
lean_object* v___x_905_; 
v___x_905_ = lean_string_from_utf8_unchecked(v___x_901_);
v___y_882_ = v___x_905_;
goto v___jp_881_;
}
}
v___jp_908_:
{
uint8_t v___x_910_; 
v___x_910_ = lean_nat_dec_le(v___x_906_, v___x_907_);
if (v___x_910_ == 0)
{
lean_dec(v___x_906_);
v_lower_898_ = v___y_909_;
v_upper_899_ = v___x_907_;
goto v___jp_897_;
}
else
{
v_lower_898_ = v___y_909_;
v_upper_899_ = v___x_906_;
goto v___jp_897_;
}
}
}
else
{
lean_object* v_array_912_; lean_object* v_idx_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_927_; 
lean_del_object(v___x_879_);
lean_dec(v_fst_876_);
v_array_912_ = lean_ctor_get(v_snd_877_, 0);
v_idx_913_ = lean_ctor_get(v_snd_877_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_snd_877_);
if (v_isSharedCheck_927_ == 0)
{
v___x_915_ = v_snd_877_;
v_isShared_916_ = v_isSharedCheck_927_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_idx_913_);
lean_inc(v_array_912_);
lean_dec(v_snd_877_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_927_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_917_ = lean_byte_array_size(v_array_912_);
lean_dec_ref(v_array_912_);
v___x_918_ = lean_nat_dec_le(v___x_917_, v_idx_913_);
lean_dec(v_idx_913_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9));
if (v_isShared_916_ == 0)
{
lean_ctor_set_tag(v___x_915_, 1);
lean_ctor_set(v___x_915_, 1, v___x_919_);
lean_ctor_set(v___x_915_, 0, v_a_871_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = lean_box(0);
if (v_isShared_916_ == 0)
{
lean_ctor_set_tag(v___x_915_, 1);
lean_ctor_set(v___x_915_, 1, v___x_923_);
lean_ctor_set(v___x_915_, 0, v_a_871_);
v___x_925_ = v___x_915_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
v___jp_881_:
{
lean_object* v___x_883_; 
v___x_883_ = lean_uv_pton_v4(v___y_882_);
if (lean_obj_tag(v___x_883_) == 1)
{
lean_object* v_val_884_; lean_object* v___x_886_; 
lean_dec_ref(v___y_882_);
v_val_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_val_884_);
lean_dec_ref(v___x_883_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v_val_884_);
lean_ctor_set(v___x_879_, 0, v_snd_877_);
v___x_886_ = v___x_879_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_snd_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_val_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
lean_dec(v___x_883_);
v___x_888_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4___closed__1));
v___x_889_ = lean_string_append(v___x_888_, v___y_882_);
lean_dec_ref(v___y_882_);
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
if (v_isShared_880_ == 0)
{
lean_ctor_set_tag(v___x_879_, 1);
lean_ctor_set(v___x_879_, 1, v___x_890_);
lean_ctor_set(v___x_879_, 0, v_snd_877_);
v___x_892_ = v___x_879_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_snd_877_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(lean_object* v_s_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___boxed(lean_object* v_s_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v_s_933_);
lean_dec_ref(v_s_933_);
return v_res_934_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(uint8_t v_x_935_){
_start:
{
uint8_t v___y_937_; uint8_t v___y_943_; uint8_t v___y_949_; uint8_t v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_955_ = lean_uint8_dec_le(v___x_954_, v_x_935_);
if (v___x_955_ == 0)
{
v___y_949_ = v___x_955_;
goto v___jp_948_;
}
else
{
uint8_t v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_957_ = lean_uint8_dec_le(v_x_935_, v___x_956_);
v___y_949_ = v___x_957_;
goto v___jp_948_;
}
v___jp_936_:
{
if (v___y_937_ == 0)
{
uint8_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_939_ = lean_uint8_dec_eq(v_x_935_, v___x_938_);
if (v___x_939_ == 0)
{
uint8_t v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_941_ = lean_uint8_dec_eq(v_x_935_, v___x_940_);
if (v___x_941_ == 0)
{
return v___y_937_;
}
else
{
return v___x_941_;
}
}
else
{
return v___x_939_;
}
}
else
{
return v___y_937_;
}
}
v___jp_942_:
{
if (v___y_943_ == 0)
{
uint8_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_945_ = lean_uint8_dec_le(v___x_944_, v_x_935_);
if (v___x_945_ == 0)
{
v___y_937_ = v___x_945_;
goto v___jp_936_;
}
else
{
uint8_t v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_947_ = lean_uint8_dec_le(v_x_935_, v___x_946_);
v___y_937_ = v___x_947_;
goto v___jp_936_;
}
}
else
{
return v___y_943_;
}
}
v___jp_948_:
{
if (v___y_949_ == 0)
{
uint8_t v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_951_ = lean_uint8_dec_le(v___x_950_, v_x_935_);
if (v___x_951_ == 0)
{
v___y_943_ = v___x_951_;
goto v___jp_942_;
}
else
{
uint8_t v___x_952_; uint8_t v___x_953_; 
v___x_952_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_953_ = lean_uint8_dec_le(v_x_935_, v___x_952_);
v___y_943_ = v___x_953_;
goto v___jp_942_;
}
}
else
{
return v___y_949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0___boxed(lean_object* v_x_958_){
_start:
{
uint8_t v_x_boxed_959_; uint8_t v_res_960_; lean_object* v_r_961_; 
v_x_boxed_959_ = lean_unbox(v_x_958_);
v_res_960_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___lam__0(v_x_boxed_959_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(lean_object* v___x_962_, lean_object* v___x_963_, lean_object* v___x_964_, lean_object* v_a_965_, uint8_t v_b_966_){
_start:
{
if (lean_obj_tag(v_a_965_) == 0)
{
lean_object* v_currPos_967_; lean_object* v_searcher_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1002_; 
v_currPos_967_ = lean_ctor_get(v_a_965_, 0);
v_searcher_968_ = lean_ctor_get(v_a_965_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_a_965_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_970_ = v_a_965_;
v_isShared_971_ = v_isSharedCheck_1002_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_searcher_968_);
lean_inc(v_currPos_967_);
lean_dec(v_a_965_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1002_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_startInclusive_972_; lean_object* v_endExclusive_973_; uint8_t v___x_974_; lean_object* v_it_976_; lean_object* v_startInclusive_977_; lean_object* v_endExclusive_978_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_startInclusive_972_ = lean_ctor_get(v___x_963_, 1);
v_endExclusive_973_ = lean_ctor_get(v___x_963_, 2);
v___x_974_ = 1;
v___x_982_ = lean_nat_sub(v_endExclusive_973_, v_startInclusive_972_);
v___x_983_ = lean_nat_dec_eq(v_searcher_968_, v___x_982_);
lean_dec(v___x_982_);
if (v___x_983_ == 0)
{
uint32_t v___x_984_; uint32_t v___x_985_; uint8_t v___x_986_; 
v___x_984_ = 46;
v___x_985_ = lean_string_utf8_get_fast(v___x_962_, v_searcher_968_);
v___x_986_ = lean_uint32_dec_eq(v___x_985_, v___x_984_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = lean_string_utf8_next_fast(v___x_962_, v_searcher_968_);
lean_dec(v_searcher_968_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_987_);
v___x_989_ = v___x_970_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_currPos_967_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_987_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
v_a_965_ = v___x_989_;
goto _start;
}
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_slice_995_; lean_object* v_nextIt_997_; 
v___x_992_ = lean_string_utf8_next_fast(v___x_962_, v_searcher_968_);
v___x_993_ = lean_nat_sub(v___x_992_, v_searcher_968_);
v___x_994_ = lean_nat_add(v_searcher_968_, v___x_993_);
lean_dec(v___x_993_);
v_slice_995_ = l_String_Slice_subslice_x21(v___x_963_, v_currPos_967_, v_searcher_968_);
lean_inc(v___x_994_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_994_);
lean_ctor_set(v___x_970_, 0, v___x_994_);
v_nextIt_997_ = v___x_970_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_994_);
v_nextIt_997_ = v_reuseFailAlloc_1000_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v_startInclusive_998_; lean_object* v_endExclusive_999_; 
v_startInclusive_998_ = lean_ctor_get(v_slice_995_, 0);
lean_inc(v_startInclusive_998_);
v_endExclusive_999_ = lean_ctor_get(v_slice_995_, 1);
lean_inc(v_endExclusive_999_);
lean_dec_ref(v_slice_995_);
v_it_976_ = v_nextIt_997_;
v_startInclusive_977_ = v_startInclusive_998_;
v_endExclusive_978_ = v_endExclusive_999_;
goto v___jp_975_;
}
}
}
else
{
lean_object* v___x_1001_; 
lean_del_object(v___x_970_);
lean_dec(v_searcher_968_);
v___x_1001_ = lean_box(1);
lean_inc(v___x_964_);
v_it_976_ = v___x_1001_;
v_startInclusive_977_ = v_currPos_967_;
v_endExclusive_978_ = v___x_964_;
goto v___jp_975_;
}
v___jp_975_:
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_string_utf8_extract(v___x_962_, v_startInclusive_977_, v_endExclusive_978_);
lean_dec(v_endExclusive_978_);
lean_dec(v_startInclusive_977_);
v___x_980_ = l_Std_Http_URI_isValidDomainLabel(v___x_979_);
if (v___x_980_ == 0)
{
lean_dec(v_it_976_);
lean_dec(v___x_964_);
return v___x_980_;
}
else
{
v_a_965_ = v_it_976_;
v_b_966_ = v___x_974_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_964_);
return v_b_966_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg___boxed(lean_object* v___x_1003_, lean_object* v___x_1004_, lean_object* v___x_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_){
_start:
{
uint8_t v_b_boxed_1008_; uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_b_boxed_1008_ = lean_unbox(v_b_1007_);
v_res_1009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1003_, v___x_1004_, v___x_1005_, v_a_1006_, v_b_boxed_1008_);
lean_dec_ref(v___x_1004_);
lean_dec_ref(v___x_1003_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v_a_1013_, uint8_t v_b_1014_){
_start:
{
if (lean_obj_tag(v_a_1013_) == 0)
{
lean_object* v_currPos_1015_; lean_object* v_searcher_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1033_; 
v_currPos_1015_ = lean_ctor_get(v_a_1013_, 0);
v_searcher_1016_ = lean_ctor_get(v_a_1013_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1018_ = v_a_1013_;
v_isShared_1019_ = v_isSharedCheck_1033_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_searcher_1016_);
lean_inc(v_currPos_1015_);
lean_dec(v_a_1013_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1033_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_startInclusive_1020_; lean_object* v_endExclusive_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_startInclusive_1020_ = lean_ctor_get(v___x_1012_, 1);
v_endExclusive_1021_ = lean_ctor_get(v___x_1012_, 2);
v___x_1022_ = 0;
v___x_1023_ = lean_nat_sub(v_endExclusive_1021_, v_startInclusive_1020_);
v___x_1024_ = lean_nat_dec_eq(v_searcher_1016_, v___x_1023_);
lean_dec(v___x_1023_);
if (v___x_1024_ == 0)
{
uint32_t v___x_1025_; uint32_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = 46;
v___x_1026_ = lean_string_utf8_get_fast(v___x_1011_, v_searcher_1016_);
v___x_1027_ = lean_uint32_dec_eq(v___x_1026_, v___x_1025_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_string_utf8_next_fast(v___x_1011_, v_searcher_1016_);
lean_dec(v_searcher_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1028_);
v___x_1030_ = v___x_1018_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_currPos_1015_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
v_a_1013_ = v___x_1030_;
goto _start;
}
}
else
{
lean_del_object(v___x_1018_);
lean_dec(v_searcher_1016_);
lean_dec(v_currPos_1015_);
return v___x_1022_;
}
}
else
{
lean_del_object(v___x_1018_);
lean_dec(v_searcher_1016_);
lean_dec(v_currPos_1015_);
return v___x_1022_;
}
}
}
else
{
return v_b_1014_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg___boxed(lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v_a_1036_, lean_object* v_b_1037_){
_start:
{
uint8_t v_b_boxed_1038_; uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_b_boxed_1038_ = lean_unbox(v_b_1037_);
v_res_1039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1034_, v___x_1035_, v_a_1036_, v_b_boxed_1038_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1034_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(lean_object* v_config_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; uint8_t v___y_1059_; lean_object* v___y_1063_; lean_object* v___y_1064_; uint8_t v___y_1065_; uint8_t v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v_lower_1083_; lean_object* v_upper_1084_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v_array_1105_; lean_object* v_idx_1106_; lean_object* v___f_1107_; lean_object* v___y_1109_; lean_object* v_pos_1138_; lean_object* v_pos_1162_; lean_object* v_res_1163_; lean_object* v___y_1165_; lean_object* v___y_1166_; uint8_t v___y_1167_; lean_object* v_pos_1169_; lean_object* v_res_1170_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_array_1105_ = lean_ctor_get(v_a_1047_, 0);
v_idx_1106_ = lean_ctor_get(v_a_1047_, 1);
v___f_1107_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__3));
v___x_1178_ = lean_byte_array_size(v_array_1105_);
v___x_1179_ = lean_nat_dec_lt(v_idx_1106_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_inc(v_idx_1106_);
lean_inc_ref(v_array_1105_);
v___x_1180_ = lean_box(0);
v_pos_1169_ = v_a_1047_;
v_res_1170_ = v___x_1180_;
goto v___jp_1168_;
}
else
{
uint8_t v___x_1181_; uint8_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = lean_byte_array_fget(v_array_1105_, v_idx_1106_);
v___x_1182_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__1);
v___x_1183_ = lean_uint8_dec_eq(v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
lean_inc(v_idx_1106_);
lean_inc_ref(v_array_1105_);
v___x_1184_ = lean_box(0);
v_pos_1169_ = v_a_1047_;
v_res_1170_ = v___x_1184_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6(v_a_1047_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_pos_1186_; lean_object* v_res_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1195_; 
v_pos_1186_ = lean_ctor_get(v___x_1185_, 0);
v_res_1187_ = lean_ctor_get(v___x_1185_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1189_ = v___x_1185_;
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_res_1187_);
lean_inc(v_pos_1186_);
lean_dec(v___x_1185_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_res_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_pos_1186_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
lean_object* v_pos_1196_; lean_object* v_err_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_pos_1196_ = lean_ctor_get(v___x_1185_, 0);
v_err_1197_ = lean_ctor_get(v___x_1185_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1185_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_err_1197_);
lean_inc(v_pos_1196_);
lean_dec(v___x_1185_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_pos_1196_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_err_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
v___jp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1051_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__0));
v___x_1052_ = lean_string_append(v___x_1051_, v___y_1050_);
lean_dec_ref(v___y_1050_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___y_1049_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
return v___x_1054_;
}
v___jp_1055_:
{
if (v___y_1059_ == 0)
{
lean_dec_ref(v___y_1056_);
v___y_1049_ = v___y_1057_;
v___y_1050_ = v___y_1058_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref(v___y_1058_);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___y_1056_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1057_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
return v___x_1061_;
}
}
v___jp_1062_:
{
if (v___y_1069_ == 0)
{
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
v___y_1049_ = v___y_1067_;
v___y_1050_ = v___y_1068_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1070_ = lean_string_utf8_byte_size(v___y_1063_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
v___x_1071_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1071_, 0, v___y_1063_);
lean_ctor_set(v___x_1071_, 1, v___y_1064_);
lean_ctor_set(v___x_1071_, 2, v___x_1070_);
v___x_1072_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_1071_);
v___x_1073_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___y_1063_, v___x_1071_, v___x_1070_, v___x_1072_, v___y_1069_);
lean_dec_ref(v___x_1071_);
if (v___x_1073_ == 0)
{
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
v___y_1049_ = v___y_1067_;
v___y_1050_ = v___y_1068_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_string_length(v___y_1063_);
v___x_1075_ = lean_unsigned_to_nat(255u);
v___x_1076_ = lean_nat_dec_le(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
v___y_1049_ = v___y_1067_;
v___y_1050_ = v___y_1068_;
goto v___jp_1048_;
}
else
{
uint8_t v___x_1077_; 
v___x_1077_ = lean_nat_dec_eq(v___x_1070_, v___y_1064_);
lean_dec(v___y_1064_);
if (v___x_1077_ == 0)
{
v___y_1056_ = v___y_1063_;
v___y_1057_ = v___y_1067_;
v___y_1058_ = v___y_1068_;
v___y_1059_ = v___y_1066_;
goto v___jp_1055_;
}
else
{
v___y_1056_ = v___y_1063_;
v___y_1057_ = v___y_1067_;
v___y_1058_ = v___y_1068_;
v___y_1059_ = v___y_1065_;
goto v___jp_1055_;
}
}
}
}
}
v___jp_1078_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = l_ByteArray_toByteSlice(v___y_1082_, v_lower_1083_, v_upper_1084_);
v___x_1086_ = l_ByteSlice_toByteArray(v___x_1085_);
v___x_1087_ = lean_string_validate_utf8(v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v___x_1086_);
lean_dec(v___y_1079_);
v___x_1088_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___closed__2));
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___y_1081_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
return v___x_1089_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1090_ = lean_string_from_utf8_unchecked(v___x_1086_);
lean_inc_n(v___y_1079_, 2);
lean_inc_ref(v___x_1090_);
v___x_1091_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme_spec__0(v___x_1090_, v___y_1079_);
v___x_1092_ = lean_string_utf8_byte_size(v___x_1091_);
lean_inc_ref(v___x_1091_);
v___x_1093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___y_1079_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
v___x_1094_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0(v___x_1093_);
v___x_1095_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1091_, v___x_1093_, v___x_1094_, v___x_1087_);
lean_dec_ref(v___x_1093_);
if (v___x_1095_ == 0)
{
v___y_1063_ = v___x_1091_;
v___y_1064_ = v___y_1079_;
v___y_1065_ = v___y_1080_;
v___y_1066_ = v___x_1087_;
v___y_1067_ = v___y_1081_;
v___y_1068_ = v___x_1090_;
v___y_1069_ = v___x_1087_;
goto v___jp_1062_;
}
else
{
v___y_1063_ = v___x_1091_;
v___y_1064_ = v___y_1079_;
v___y_1065_ = v___y_1080_;
v___y_1066_ = v___x_1087_;
v___y_1067_ = v___y_1081_;
v___y_1068_ = v___x_1090_;
v___y_1069_ = v___y_1080_;
goto v___jp_1062_;
}
}
}
v___jp_1096_:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_nat_dec_le(v___y_1101_, v___y_1097_);
if (v___x_1104_ == 0)
{
lean_dec(v___y_1101_);
v___y_1079_ = v___y_1098_;
v___y_1080_ = v___y_1099_;
v___y_1081_ = v___y_1100_;
v___y_1082_ = v___y_1102_;
v_lower_1083_ = v___y_1103_;
v_upper_1084_ = v___y_1097_;
goto v___jp_1078_;
}
else
{
lean_dec(v___y_1097_);
v___y_1079_ = v___y_1098_;
v___y_1080_ = v___y_1099_;
v___y_1081_ = v___y_1100_;
v___y_1082_ = v___y_1102_;
v_lower_1083_ = v___y_1103_;
v_upper_1084_ = v___y_1101_;
goto v___jp_1078_;
}
}
v___jp_1108_:
{
lean_object* v_maxHostLength_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_fst_1113_; lean_object* v_snd_1114_; uint8_t v___x_1115_; 
v_maxHostLength_1110_ = lean_ctor_get(v_config_1046_, 1);
v___x_1111_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_1109_);
v___x_1112_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo1_findEnd(v___f_1107_, v_maxHostLength_1110_, v___x_1111_, v___y_1109_);
v_fst_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_fst_1113_);
v_snd_1114_ = lean_ctor_get(v___x_1112_, 1);
lean_inc(v_snd_1114_);
lean_dec_ref(v___x_1112_);
v___x_1115_ = lean_nat_dec_eq(v_fst_1113_, v___x_1111_);
if (v___x_1115_ == 0)
{
lean_object* v_array_1116_; lean_object* v_idx_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_array_1116_ = lean_ctor_get(v___y_1109_, 0);
lean_inc_ref(v_array_1116_);
v_idx_1117_ = lean_ctor_get(v___y_1109_, 1);
lean_inc(v_idx_1117_);
lean_dec_ref(v___y_1109_);
v___x_1118_ = lean_nat_add(v_idx_1117_, v_fst_1113_);
lean_dec(v_fst_1113_);
v___x_1119_ = lean_byte_array_size(v_array_1116_);
v___x_1120_ = lean_nat_dec_le(v_idx_1117_, v___x_1111_);
if (v___x_1120_ == 0)
{
v___y_1097_ = v___x_1119_;
v___y_1098_ = v___x_1111_;
v___y_1099_ = v___x_1115_;
v___y_1100_ = v_snd_1114_;
v___y_1101_ = v___x_1118_;
v___y_1102_ = v_array_1116_;
v___y_1103_ = v_idx_1117_;
goto v___jp_1096_;
}
else
{
lean_dec(v_idx_1117_);
v___y_1097_ = v___x_1119_;
v___y_1098_ = v___x_1111_;
v___y_1099_ = v___x_1115_;
v___y_1100_ = v_snd_1114_;
v___y_1101_ = v___x_1118_;
v___y_1102_ = v_array_1116_;
v___y_1103_ = v___x_1111_;
goto v___jp_1096_;
}
}
else
{
lean_object* v_array_1121_; lean_object* v_idx_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_fst_1113_);
v_array_1121_ = lean_ctor_get(v_snd_1114_, 0);
v_idx_1122_ = lean_ctor_get(v_snd_1114_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_snd_1114_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1124_ = v_snd_1114_;
v_isShared_1125_ = v_isSharedCheck_1136_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_idx_1122_);
lean_inc(v_array_1121_);
lean_dec(v_snd_1114_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1136_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = lean_byte_array_size(v_array_1121_);
lean_dec_ref(v_array_1121_);
v___x_1127_ = lean_nat_dec_le(v___x_1126_, v_idx_1122_);
lean_dec(v_idx_1122_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___closed__9));
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 1);
lean_ctor_set(v___x_1124_, 1, v___x_1128_);
lean_ctor_set(v___x_1124_, 0, v___y_1109_);
v___x_1130_ = v___x_1124_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___y_1109_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_box(0);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 1);
lean_ctor_set(v___x_1124_, 1, v___x_1132_);
lean_ctor_set(v___x_1124_, 0, v___y_1109_);
v___x_1134_ = v___x_1124_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___y_1109_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
v___jp_1137_:
{
lean_object* v___x_1139_; 
lean_inc_ref(v_pos_1138_);
v___x_1139_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv4(v_pos_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_pos_1140_; lean_object* v_res_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_pos_1138_);
v_pos_1140_ = lean_ctor_get(v___x_1139_, 0);
v_res_1141_ = lean_ctor_get(v___x_1139_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v___x_1139_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_res_1141_);
lean_inc(v_pos_1140_);
lean_dec(v___x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_res_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1145_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_pos_1140_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
lean_object* v_err_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1159_; 
v_err_1150_ = lean_ctor_get(v___x_1139_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v___x_1139_, 0);
lean_dec(v_unused_1160_);
v___x_1152_ = v___x_1139_;
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_err_1150_);
lean_dec(v___x_1139_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1159_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_idx_1154_; uint8_t v___x_1155_; 
v_idx_1154_ = lean_ctor_get(v_pos_1138_, 1);
v___x_1155_ = lean_nat_dec_eq(v_idx_1154_, v_idx_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1157_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_pos_1138_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_pos_1138_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_err_1150_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
else
{
lean_del_object(v___x_1152_);
lean_dec(v_err_1150_);
v___y_1109_ = v_pos_1138_;
goto v___jp_1108_;
}
}
}
}
v___jp_1161_:
{
v___y_1109_ = v_pos_1162_;
goto v___jp_1108_;
}
v___jp_1164_:
{
if (v___y_1167_ == 0)
{
v_pos_1162_ = v___y_1166_;
v_res_1163_ = v___y_1165_;
goto v___jp_1161_;
}
else
{
v_pos_1138_ = v___y_1166_;
goto v___jp_1137_;
}
}
v___jp_1168_:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_byte_array_size(v_array_1105_);
v___x_1172_ = lean_nat_dec_lt(v_idx_1106_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_dec(v_idx_1106_);
lean_dec_ref(v_array_1105_);
v_pos_1162_ = v_pos_1169_;
v_res_1163_ = v_res_1170_;
goto v___jp_1161_;
}
else
{
uint8_t v___x_1173_; uint8_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1173_ = lean_byte_array_fget(v_array_1105_, v_idx_1106_);
lean_dec(v_idx_1106_);
lean_dec_ref(v_array_1105_);
v___x_1174_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_1175_ = lean_uint8_dec_le(v___x_1174_, v___x_1173_);
if (v___x_1175_ == 0)
{
v___y_1165_ = v_res_1170_;
v___y_1166_ = v_pos_1169_;
v___y_1167_ = v___x_1175_;
goto v___jp_1164_;
}
else
{
uint8_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_1177_ = lean_uint8_dec_le(v___x_1173_, v___x_1176_);
v___y_1165_ = v_res_1170_;
v___y_1166_ = v_pos_1169_;
v___y_1167_ = v___x_1177_;
goto v___jp_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost___boxed(lean_object* v_config_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1205_, v_a_1206_);
lean_dec_ref(v_config_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(lean_object* v___x_1208_, lean_object* v___x_1209_, lean_object* v___x_1210_, lean_object* v_inst_1211_, lean_object* v_R_1212_, lean_object* v_a_1213_, uint8_t v_b_1214_, lean_object* v_c_1215_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___redArg(v___x_1208_, v___x_1209_, v___x_1210_, v_a_1213_, v_b_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1___boxed(lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v_inst_1220_, lean_object* v_R_1221_, lean_object* v_a_1222_, lean_object* v_b_1223_, lean_object* v_c_1224_){
_start:
{
uint8_t v_b_boxed_1225_; uint8_t v_res_1226_; lean_object* v_r_1227_; 
v_b_boxed_1225_ = lean_unbox(v_b_1223_);
v_res_1226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__1(v___x_1217_, v___x_1218_, v___x_1219_, v_inst_1220_, v_R_1221_, v_a_1222_, v_b_boxed_1225_, v_c_1224_);
lean_dec_ref(v___x_1218_);
lean_dec_ref(v___x_1217_);
v_r_1227_ = lean_box(v_res_1226_);
return v_r_1227_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(lean_object* v___x_1228_, lean_object* v___x_1229_, lean_object* v___x_1230_, lean_object* v_inst_1231_, lean_object* v_R_1232_, lean_object* v_a_1233_, uint8_t v_b_1234_, lean_object* v_c_1235_){
_start:
{
uint8_t v___x_1236_; 
v___x_1236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___redArg(v___x_1228_, v___x_1229_, v_a_1233_, v_b_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2___boxed(lean_object* v___x_1237_, lean_object* v___x_1238_, lean_object* v___x_1239_, lean_object* v_inst_1240_, lean_object* v_R_1241_, lean_object* v_a_1242_, lean_object* v_b_1243_, lean_object* v_c_1244_){
_start:
{
uint8_t v_b_boxed_1245_; uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_b_boxed_1245_ = lean_unbox(v_b_1243_);
v_res_1246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__2(v___x_1237_, v___x_1238_, v___x_1239_, v_inst_1240_, v_R_1241_, v_a_1242_, v_b_boxed_1245_, v_c_1244_);
lean_dec(v___x_1239_);
lean_dec_ref(v___x_1238_);
lean_dec_ref(v___x_1237_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2(void){
_start:
{
uint32_t v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = 47;
v___x_1252_ = lean_uint32_to_uint8(v___x_1251_);
return v___x_1252_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3(void){
_start:
{
uint32_t v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = 63;
v___x_1254_ = lean_uint32_to_uint8(v___x_1253_);
return v___x_1254_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4(void){
_start:
{
uint32_t v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = 35;
v___x_1256_ = lean_uint32_to_uint8(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5(void){
_start:
{
uint8_t v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1258_ = lean_uint8_to_nat(v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__5);
v___x_1260_ = l_Nat_reprFast(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__6);
v___x_1262_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1263_ = lean_string_append(v___x_1262_, v___x_1261_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1265_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__7);
v___x_1266_ = lean_string_append(v___x_1265_, v___x_1264_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__8);
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
static uint8_t _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10(void){
_start:
{
uint32_t v___x_1269_; uint8_t v___x_1270_; 
v___x_1269_ = 64;
v___x_1270_ = lean_uint32_to_uint8(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11(void){
_start:
{
uint8_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1272_ = lean_uint8_to_nat(v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__11);
v___x_1274_ = l_Nat_reprFast(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__12);
v___x_1276_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_1277_ = lean_string_append(v___x_1276_, v___x_1275_);
return v___x_1277_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_1279_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__13);
v___x_1280_ = lean_string_append(v___x_1279_, v___x_1278_);
return v___x_1280_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__14);
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(lean_object* v_config_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v_port_1288_; lean_object* v___y_1289_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v_pos_1295_; lean_object* v___y_1298_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; uint8_t v___y_1310_; lean_object* v___y_1312_; uint8_t v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; uint8_t v___y_1316_; lean_object* v___y_1317_; uint8_t v___y_1318_; lean_object* v___y_1330_; lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; uint8_t v___y_1335_; lean_object* v___y_1345_; uint8_t v___y_1346_; uint8_t v___y_1347_; lean_object* v___y_1348_; lean_object* v_pos_1349_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; uint8_t v___y_1358_; lean_object* v_pos_1374_; lean_object* v_res_1375_; lean_object* v_pos_1427_; lean_object* v_res_1428_; lean_object* v_err_1431_; lean_object* v___x_1436_; 
lean_inc_ref(v_a_1284_);
v___x_1436_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo(v_config_1283_, v_a_1284_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_pos_1437_; lean_object* v_res_1438_; lean_object* v_array_1439_; lean_object* v_idx_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1456_; 
v_pos_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_pos_1437_);
v_res_1438_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_res_1438_);
lean_dec_ref(v___x_1436_);
v_array_1439_ = lean_ctor_get(v_pos_1437_, 0);
v_idx_1440_ = lean_ctor_get(v_pos_1437_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_pos_1437_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1442_ = v_pos_1437_;
v_isShared_1443_ = v_isSharedCheck_1456_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_idx_1440_);
lean_inc(v_array_1439_);
lean_dec(v_pos_1437_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1456_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_byte_array_size(v_array_1439_);
v___x_1445_ = lean_nat_dec_lt(v_idx_1440_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_del_object(v___x_1442_);
lean_dec(v_idx_1440_);
lean_dec_ref(v_array_1439_);
lean_dec(v_res_1438_);
v___x_1446_ = lean_box(0);
v_err_1431_ = v___x_1446_;
goto v___jp_1430_;
}
else
{
uint8_t v___x_1447_; uint8_t v_c_1448_; uint8_t v___x_1449_; 
v___x_1447_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v_c_1448_ = lean_byte_array_fget(v_array_1439_, v_idx_1440_);
v___x_1449_ = lean_uint8_dec_eq(v_c_1448_, v___x_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_del_object(v___x_1442_);
lean_dec(v_idx_1440_);
lean_dec_ref(v_array_1439_);
lean_dec(v_res_1438_);
v___x_1450_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__15);
v_err_1431_ = v___x_1450_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_it_x27_1454_; 
lean_dec_ref(v_a_1284_);
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_add(v_idx_1440_, v___x_1451_);
lean_dec(v_idx_1440_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1452_);
v_it_x27_1454_ = v___x_1442_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_array_1439_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1452_);
v_it_x27_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
v_pos_1427_ = v_it_x27_1454_;
v_res_1428_ = v_res_1438_;
goto v___jp_1426_;
}
}
}
}
}
else
{
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_pos_1457_; lean_object* v_res_1458_; 
lean_dec_ref(v_a_1284_);
v_pos_1457_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_pos_1457_);
v_res_1458_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_res_1458_);
lean_dec_ref(v___x_1436_);
v_pos_1427_ = v_pos_1457_;
v_res_1428_ = v_res_1458_;
goto v___jp_1426_;
}
else
{
lean_object* v_err_1459_; 
v_err_1459_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_err_1459_);
lean_dec_ref(v___x_1436_);
v_err_1431_ = v_err_1459_;
goto v___jp_1430_;
}
}
v___jp_1285_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1290_, 0, v___y_1287_);
lean_ctor_set(v___x_1290_, 1, v___y_1286_);
lean_ctor_set(v___x_1290_, 2, v_port_1288_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___y_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
return v___x_1291_;
}
v___jp_1292_:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_box(0);
v___y_1286_ = v___y_1293_;
v___y_1287_ = v___y_1294_;
v_port_1288_ = v___x_1296_;
v___y_1289_ = v_pos_1295_;
goto v___jp_1285_;
}
v___jp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__1));
v___x_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___y_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
return v___x_1300_;
}
v___jp_1301_:
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_box(1);
v___y_1286_ = v___y_1302_;
v___y_1287_ = v___y_1304_;
v_port_1288_ = v___x_1305_;
v___y_1289_ = v___y_1303_;
goto v___jp_1285_;
}
v___jp_1306_:
{
if (v___y_1310_ == 0)
{
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1307_);
v___y_1298_ = v___y_1308_;
goto v___jp_1297_;
}
else
{
v___y_1302_ = v___y_1307_;
v___y_1303_ = v___y_1308_;
v___y_1304_ = v___y_1309_;
goto v___jp_1301_;
}
}
v___jp_1311_:
{
if (v___y_1318_ == 0)
{
if (lean_obj_tag(v___y_1315_) == 0)
{
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1312_);
v___y_1298_ = v___y_1314_;
goto v___jp_1297_;
}
else
{
lean_object* v_val_1319_; uint8_t v___x_1320_; uint8_t v___x_1321_; uint8_t v___x_1322_; 
v_val_1319_ = lean_ctor_get(v___y_1315_, 0);
lean_inc(v_val_1319_);
lean_dec_ref(v___y_1315_);
v___x_1320_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1321_ = lean_unbox(v_val_1319_);
v___x_1322_ = lean_uint8_dec_eq(v___x_1321_, v___x_1320_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; uint8_t v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1324_ = lean_unbox(v_val_1319_);
v___x_1325_ = lean_uint8_dec_eq(v___x_1324_, v___x_1323_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; uint8_t v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1327_ = lean_unbox(v_val_1319_);
lean_dec(v_val_1319_);
v___x_1328_ = lean_uint8_dec_eq(v___x_1327_, v___x_1326_);
if (v___x_1328_ == 0)
{
v___y_1307_ = v___y_1312_;
v___y_1308_ = v___y_1314_;
v___y_1309_ = v___y_1317_;
v___y_1310_ = v___x_1328_;
goto v___jp_1306_;
}
else
{
v___y_1307_ = v___y_1312_;
v___y_1308_ = v___y_1314_;
v___y_1309_ = v___y_1317_;
v___y_1310_ = v___y_1313_;
goto v___jp_1306_;
}
}
else
{
lean_dec(v_val_1319_);
v___y_1307_ = v___y_1312_;
v___y_1308_ = v___y_1314_;
v___y_1309_ = v___y_1317_;
v___y_1310_ = v___y_1313_;
goto v___jp_1306_;
}
}
else
{
lean_dec(v_val_1319_);
v___y_1307_ = v___y_1312_;
v___y_1308_ = v___y_1314_;
v___y_1309_ = v___y_1317_;
v___y_1310_ = v___y_1316_;
goto v___jp_1306_;
}
}
}
else
{
lean_dec(v___y_1315_);
v___y_1302_ = v___y_1312_;
v___y_1303_ = v___y_1314_;
v___y_1304_ = v___y_1317_;
goto v___jp_1301_;
}
}
v___jp_1329_:
{
lean_object* v_array_1336_; lean_object* v_idx_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
v_array_1336_ = lean_ctor_get(v___y_1331_, 0);
v_idx_1337_ = lean_ctor_get(v___y_1331_, 1);
v___x_1338_ = lean_byte_array_size(v_array_1336_);
v___x_1339_ = lean_nat_dec_lt(v_idx_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_box(0);
v___y_1312_ = v___y_1330_;
v___y_1313_ = v___y_1332_;
v___y_1314_ = v___y_1331_;
v___y_1315_ = v___x_1340_;
v___y_1316_ = v___y_1334_;
v___y_1317_ = v___y_1333_;
v___y_1318_ = v___y_1334_;
goto v___jp_1311_;
}
else
{
uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_byte_array_fget(v_array_1336_, v_idx_1337_);
v___x_1342_ = lean_box(v___x_1341_);
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
v___y_1312_ = v___y_1330_;
v___y_1313_ = v___y_1332_;
v___y_1314_ = v___y_1331_;
v___y_1315_ = v___x_1343_;
v___y_1316_ = v___y_1334_;
v___y_1317_ = v___y_1333_;
v___y_1318_ = v___y_1335_;
goto v___jp_1311_;
}
}
v___jp_1344_:
{
uint8_t v___x_1350_; 
v___x_1350_ = 0;
v___y_1330_ = v___y_1345_;
v___y_1331_ = v_pos_1349_;
v___y_1332_ = v___y_1346_;
v___y_1333_ = v___y_1348_;
v___y_1334_ = v___y_1347_;
v___y_1335_ = v___x_1350_;
goto v___jp_1329_;
}
v___jp_1351_:
{
lean_dec(v___y_1357_);
if (v___y_1358_ == 0)
{
v___y_1345_ = v___y_1352_;
v___y_1346_ = v___y_1354_;
v___y_1347_ = v___y_1356_;
v___y_1348_ = v___y_1355_;
v_pos_1349_ = v___y_1353_;
goto v___jp_1344_;
}
else
{
if (v___y_1356_ == 0)
{
v___y_1330_ = v___y_1352_;
v___y_1331_ = v___y_1353_;
v___y_1332_ = v___y_1354_;
v___y_1333_ = v___y_1355_;
v___y_1334_ = v___y_1356_;
v___y_1335_ = v___y_1356_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1359_; 
v___x_1359_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v___y_1353_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_pos_1360_; lean_object* v_res_1361_; lean_object* v___x_1362_; uint16_t v___x_1363_; 
v_pos_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_pos_1360_);
v_res_1361_ = lean_ctor_get(v___x_1359_, 1);
lean_inc(v_res_1361_);
lean_dec_ref(v___x_1359_);
v___x_1362_ = lean_alloc_ctor(2, 0, 2);
v___x_1363_ = lean_unbox(v_res_1361_);
lean_dec(v_res_1361_);
lean_ctor_set_uint16(v___x_1362_, 0, v___x_1363_);
v___y_1286_ = v___y_1352_;
v___y_1287_ = v___y_1355_;
v_port_1288_ = v___x_1362_;
v___y_1289_ = v_pos_1360_;
goto v___jp_1285_;
}
else
{
lean_object* v_pos_1364_; lean_object* v_err_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1352_);
v_pos_1364_ = lean_ctor_get(v___x_1359_, 0);
v_err_1365_ = lean_ctor_get(v___x_1359_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1359_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_err_1365_);
lean_inc(v_pos_1364_);
lean_dec(v___x_1359_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_pos_1364_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_err_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
v___jp_1373_:
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_1283_, v_pos_1374_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_pos_1377_; lean_object* v_res_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1416_; 
v_pos_1377_ = lean_ctor_get(v___x_1376_, 0);
v_res_1378_ = lean_ctor_get(v___x_1376_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1380_ = v___x_1376_;
v_isShared_1381_ = v_isSharedCheck_1416_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_res_1378_);
lean_inc(v_pos_1377_);
lean_dec(v___x_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1416_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_array_1382_; lean_object* v_idx_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_array_1382_ = lean_ctor_get(v_pos_1377_, 0);
v_idx_1383_ = lean_ctor_get(v_pos_1377_, 1);
v___x_1384_ = lean_byte_array_size(v_array_1382_);
v___x_1385_ = lean_nat_dec_lt(v_idx_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_del_object(v___x_1380_);
v___y_1293_ = v_res_1378_;
v___y_1294_ = v_res_1375_;
v_pos_1295_ = v_pos_1377_;
goto v___jp_1292_;
}
else
{
uint8_t v___x_1386_; uint8_t v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = lean_byte_array_fget(v_array_1382_, v_idx_1383_);
v___x_1387_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1388_ = lean_uint8_dec_eq(v___x_1386_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_del_object(v___x_1380_);
v___y_1293_ = v_res_1378_;
v___y_1294_ = v_res_1375_;
v_pos_1295_ = v_pos_1377_;
goto v___jp_1292_;
}
else
{
if (v___x_1388_ == 0)
{
lean_del_object(v___x_1380_);
v___y_1293_ = v_res_1378_;
v___y_1294_ = v_res_1375_;
v_pos_1295_ = v_pos_1377_;
goto v___jp_1292_;
}
else
{
if (v___x_1385_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_dec(v_res_1378_);
lean_dec(v_res_1375_);
v___x_1389_ = lean_box(0);
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 1);
lean_ctor_set(v___x_1380_, 1, v___x_1389_);
v___x_1391_ = v___x_1380_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_pos_1377_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
if (v___x_1388_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_dec(v_res_1378_);
lean_dec(v_res_1375_);
v___x_1393_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 1);
lean_ctor_set(v___x_1380_, 1, v___x_1393_);
v___x_1395_ = v___x_1380_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_pos_1377_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1413_; 
lean_inc(v_idx_1383_);
lean_inc_ref(v_array_1382_);
lean_del_object(v___x_1380_);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_pos_1377_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; lean_object* v_unused_1415_; 
v_unused_1414_ = lean_ctor_get(v_pos_1377_, 1);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_pos_1377_, 0);
lean_dec(v_unused_1415_);
v___x_1398_ = v_pos_1377_;
v_isShared_1399_ = v_isSharedCheck_1413_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v_pos_1377_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1413_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v_it_x27_1403_; 
v___x_1400_ = lean_unsigned_to_nat(1u);
v___x_1401_ = lean_nat_add(v_idx_1383_, v___x_1400_);
lean_dec(v_idx_1383_);
lean_inc(v___x_1401_);
lean_inc_ref(v_array_1382_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1401_);
v_it_x27_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_array_1382_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1401_);
v_it_x27_1403_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_nat_dec_lt(v___x_1401_, v___x_1384_);
if (v___x_1404_ == 0)
{
lean_dec(v___x_1401_);
lean_dec_ref(v_array_1382_);
v___y_1345_ = v_res_1378_;
v___y_1346_ = v___x_1388_;
v___y_1347_ = v___x_1385_;
v___y_1348_ = v_res_1375_;
v_pos_1349_ = v_it_x27_1403_;
goto v___jp_1344_;
}
else
{
uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; uint8_t v___x_1409_; 
v___x_1405_ = lean_byte_array_fget(v_array_1382_, v___x_1401_);
lean_dec(v___x_1401_);
lean_dec_ref(v_array_1382_);
v___x_1406_ = lean_box(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
v___x_1408_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_1409_ = lean_uint8_dec_le(v___x_1408_, v___x_1405_);
if (v___x_1409_ == 0)
{
v___y_1352_ = v_res_1378_;
v___y_1353_ = v_it_x27_1403_;
v___y_1354_ = v___x_1388_;
v___y_1355_ = v_res_1375_;
v___y_1356_ = v___x_1385_;
v___y_1357_ = v___x_1407_;
v___y_1358_ = v___x_1409_;
goto v___jp_1351_;
}
else
{
uint8_t v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_1411_ = lean_uint8_dec_le(v___x_1405_, v___x_1410_);
v___y_1352_ = v_res_1378_;
v___y_1353_ = v_it_x27_1403_;
v___y_1354_ = v___x_1388_;
v___y_1355_ = v_res_1375_;
v___y_1356_ = v___x_1385_;
v___y_1357_ = v___x_1407_;
v___y_1358_ = v___x_1411_;
goto v___jp_1351_;
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
lean_object* v_pos_1417_; lean_object* v_err_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_res_1375_);
v_pos_1417_ = lean_ctor_get(v___x_1376_, 0);
v_err_1418_ = lean_ctor_get(v___x_1376_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1376_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_err_1418_);
lean_inc(v_pos_1417_);
lean_dec(v___x_1376_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_pos_1417_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_err_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v_res_1428_);
v_pos_1374_ = v_pos_1427_;
v_res_1375_ = v___x_1429_;
goto v___jp_1373_;
}
v___jp_1430_:
{
lean_object* v_idx_1432_; uint8_t v___x_1433_; 
v_idx_1432_ = lean_ctor_get(v_a_1284_, 1);
v___x_1433_ = lean_nat_dec_eq(v_idx_1432_, v_idx_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_a_1284_);
lean_ctor_set(v___x_1434_, 1, v_err_1431_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; 
lean_dec(v_err_1431_);
v___x_1435_ = lean_box(0);
v_pos_1374_ = v_a_1284_;
v_res_1375_ = v___x_1435_;
goto v___jp_1373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___boxed(lean_object* v_config_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_1460_, v_a_1461_);
lean_dec_ref(v_config_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(uint8_t v_c_1463_){
_start:
{
uint8_t v___y_1465_; uint8_t v___y_1469_; uint8_t v___y_1475_; uint8_t v___y_1495_; uint8_t v___y_1501_; uint8_t v___y_1507_; uint8_t v___y_1513_; uint8_t v___y_1519_; uint8_t v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_1525_ = lean_uint8_dec_le(v___x_1524_, v_c_1463_);
if (v___x_1525_ == 0)
{
v___y_1519_ = v___x_1525_;
goto v___jp_1518_;
}
else
{
uint8_t v___x_1526_; uint8_t v___x_1527_; 
v___x_1526_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_1527_ = lean_uint8_dec_le(v_c_1463_, v___x_1526_);
v___y_1519_ = v___x_1527_;
goto v___jp_1518_;
}
v___jp_1464_:
{
if (v___y_1465_ == 0)
{
uint8_t v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1467_ = lean_uint8_dec_eq(v_c_1463_, v___x_1466_);
if (v___x_1467_ == 0)
{
return v___y_1465_;
}
else
{
return v___x_1467_;
}
}
else
{
return v___y_1465_;
}
}
v___jp_1468_:
{
if (v___y_1469_ == 0)
{
uint8_t v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1471_ = lean_uint8_dec_eq(v_c_1463_, v___x_1470_);
if (v___x_1471_ == 0)
{
uint8_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1472_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1473_ = lean_uint8_dec_eq(v_c_1463_, v___x_1472_);
v___y_1465_ = v___x_1473_;
goto v___jp_1464_;
}
else
{
v___y_1465_ = v___x_1471_;
goto v___jp_1464_;
}
}
else
{
return v___y_1469_;
}
}
v___jp_1474_:
{
if (v___y_1475_ == 0)
{
uint8_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1477_ = lean_uint8_dec_eq(v_c_1463_, v___x_1476_);
if (v___x_1477_ == 0)
{
uint8_t v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1479_ = lean_uint8_dec_eq(v_c_1463_, v___x_1478_);
if (v___x_1479_ == 0)
{
uint8_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1481_ = lean_uint8_dec_eq(v_c_1463_, v___x_1480_);
if (v___x_1481_ == 0)
{
uint8_t v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1483_ = lean_uint8_dec_eq(v_c_1463_, v___x_1482_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1485_ = lean_uint8_dec_eq(v_c_1463_, v___x_1484_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_1487_ = lean_uint8_dec_eq(v_c_1463_, v___x_1486_);
if (v___x_1487_ == 0)
{
uint8_t v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1489_ = lean_uint8_dec_eq(v_c_1463_, v___x_1488_);
if (v___x_1489_ == 0)
{
uint8_t v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1491_ = lean_uint8_dec_eq(v_c_1463_, v___x_1490_);
if (v___x_1491_ == 0)
{
uint8_t v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1493_ = lean_uint8_dec_eq(v_c_1463_, v___x_1492_);
v___y_1469_ = v___x_1493_;
goto v___jp_1468_;
}
else
{
v___y_1469_ = v___x_1491_;
goto v___jp_1468_;
}
}
else
{
v___y_1469_ = v___x_1489_;
goto v___jp_1468_;
}
}
else
{
v___y_1469_ = v___x_1487_;
goto v___jp_1468_;
}
}
else
{
v___y_1469_ = v___x_1485_;
goto v___jp_1468_;
}
}
else
{
v___y_1469_ = v___x_1483_;
goto v___jp_1468_;
}
}
else
{
v___y_1469_ = v___x_1481_;
goto v___jp_1468_;
}
}
else
{
v___y_1469_ = v___x_1479_;
goto v___jp_1468_;
}
}
else
{
v___y_1469_ = v___x_1477_;
goto v___jp_1468_;
}
}
else
{
return v___y_1475_;
}
}
v___jp_1494_:
{
if (v___y_1495_ == 0)
{
uint8_t v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1497_ = lean_uint8_dec_eq(v_c_1463_, v___x_1496_);
if (v___x_1497_ == 0)
{
uint8_t v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1499_ = lean_uint8_dec_eq(v_c_1463_, v___x_1498_);
v___y_1475_ = v___x_1499_;
goto v___jp_1474_;
}
else
{
v___y_1475_ = v___x_1497_;
goto v___jp_1474_;
}
}
else
{
return v___y_1495_;
}
}
v___jp_1500_:
{
if (v___y_1501_ == 0)
{
uint8_t v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1503_ = lean_uint8_dec_eq(v_c_1463_, v___x_1502_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1505_ = lean_uint8_dec_eq(v_c_1463_, v___x_1504_);
v___y_1495_ = v___x_1505_;
goto v___jp_1494_;
}
else
{
v___y_1495_ = v___x_1503_;
goto v___jp_1494_;
}
}
else
{
return v___y_1501_;
}
}
v___jp_1506_:
{
if (v___y_1507_ == 0)
{
uint8_t v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_1509_ = lean_uint8_dec_eq(v_c_1463_, v___x_1508_);
if (v___x_1509_ == 0)
{
uint8_t v___x_1510_; uint8_t v___x_1511_; 
v___x_1510_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_1511_ = lean_uint8_dec_eq(v_c_1463_, v___x_1510_);
v___y_1501_ = v___x_1511_;
goto v___jp_1500_;
}
else
{
v___y_1501_ = v___x_1509_;
goto v___jp_1500_;
}
}
else
{
return v___y_1507_;
}
}
v___jp_1512_:
{
if (v___y_1513_ == 0)
{
uint8_t v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1515_ = lean_uint8_dec_le(v___x_1514_, v_c_1463_);
if (v___x_1515_ == 0)
{
v___y_1507_ = v___x_1515_;
goto v___jp_1506_;
}
else
{
uint8_t v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1517_ = lean_uint8_dec_le(v_c_1463_, v___x_1516_);
v___y_1507_ = v___x_1517_;
goto v___jp_1506_;
}
}
else
{
return v___y_1513_;
}
}
v___jp_1518_:
{
if (v___y_1519_ == 0)
{
uint8_t v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1521_ = lean_uint8_dec_le(v___x_1520_, v_c_1463_);
if (v___x_1521_ == 0)
{
v___y_1513_ = v___x_1521_;
goto v___jp_1512_;
}
else
{
uint8_t v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1523_ = lean_uint8_dec_le(v_c_1463_, v___x_1522_);
v___y_1513_ = v___x_1523_;
goto v___jp_1512_;
}
}
else
{
return v___y_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0___boxed(lean_object* v_c_1528_){
_start:
{
uint8_t v_c_boxed_1529_; uint8_t v_res_1530_; lean_object* v_r_1531_; 
v_c_boxed_1529_ = lean_unbox(v_c_1528_);
v_res_1530_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___lam__0(v_c_boxed_1529_);
v_r_1531_ = lean_box(v_res_1530_);
return v_r_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(lean_object* v_config_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_maxSegmentLength_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_fst_1539_; lean_object* v_snd_1540_; lean_object* v_array_1541_; lean_object* v_idx_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1559_; 
v_maxSegmentLength_1535_ = lean_ctor_get(v_config_1533_, 3);
v___f_1536_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___closed__0));
v___x_1537_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_1534_);
v___x_1538_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_1536_, v_maxSegmentLength_1535_, v___x_1537_, v_a_1534_);
v_fst_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_fst_1539_);
v_snd_1540_ = lean_ctor_get(v___x_1538_, 1);
lean_inc(v_snd_1540_);
lean_dec_ref(v___x_1538_);
v_array_1541_ = lean_ctor_get(v_a_1534_, 0);
v_idx_1542_ = lean_ctor_get(v_a_1534_, 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_a_1534_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1544_ = v_a_1534_;
v_isShared_1545_ = v_isSharedCheck_1559_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_idx_1542_);
lean_inc(v_array_1541_);
lean_dec(v_a_1534_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1559_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_lower_1547_; lean_object* v_upper_1548_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___y_1556_; uint8_t v___x_1558_; 
v___x_1553_ = lean_nat_add(v_idx_1542_, v_fst_1539_);
lean_dec(v_fst_1539_);
v___x_1554_ = lean_byte_array_size(v_array_1541_);
v___x_1558_ = lean_nat_dec_le(v_idx_1542_, v___x_1537_);
if (v___x_1558_ == 0)
{
v___y_1556_ = v_idx_1542_;
goto v___jp_1555_;
}
else
{
lean_dec(v_idx_1542_);
v___y_1556_ = v___x_1537_;
goto v___jp_1555_;
}
v___jp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1549_ = l_ByteArray_toByteSlice(v_array_1541_, v_lower_1547_, v_upper_1548_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 1, v___x_1549_);
lean_ctor_set(v___x_1544_, 0, v_snd_1540_);
v___x_1551_ = v___x_1544_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_snd_1540_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
v___jp_1555_:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_le(v___x_1553_, v___x_1554_);
if (v___x_1557_ == 0)
{
lean_dec(v___x_1553_);
v_lower_1547_ = v___y_1556_;
v_upper_1548_ = v___x_1554_;
goto v___jp_1546_;
}
else
{
v_lower_1547_ = v___y_1556_;
v_upper_1548_ = v___x_1553_;
goto v___jp_1546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment___boxed(lean_object* v_config_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1560_, v_a_1561_);
lean_dec_ref(v_config_1560_);
return v_res_1562_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(uint8_t v_c_1563_){
_start:
{
uint8_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_1565_ = lean_uint8_dec_eq(v_c_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
uint8_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_1567_ = lean_uint8_dec_eq(v_c_1563_, v___x_1566_);
return v___x_1567_;
}
else
{
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0___boxed(lean_object* v_c_1568_){
_start:
{
uint8_t v_c_boxed_1569_; uint8_t v_res_1570_; lean_object* v_r_1571_; 
v_c_boxed_1569_ = lean_unbox(v_c_1568_);
v_res_1570_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v_c_boxed_1569_);
v_r_1571_ = lean_box(v_res_1570_);
return v_r_1571_;
}
}
LEAN_EXPORT uint8_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1(uint8_t v___y_1572_){
_start:
{
uint8_t v___y_1574_; uint8_t v___y_1580_; uint8_t v___y_1600_; uint8_t v___y_1606_; uint8_t v___y_1612_; uint8_t v___y_1618_; uint8_t v___y_1624_; uint8_t v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_1630_ = lean_uint8_dec_le(v___x_1629_, v___y_1572_);
if (v___x_1630_ == 0)
{
v___y_1624_ = v___x_1630_;
goto v___jp_1623_;
}
else
{
uint8_t v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_1632_ = lean_uint8_dec_le(v___y_1572_, v___x_1631_);
v___y_1624_ = v___x_1632_;
goto v___jp_1623_;
}
v___jp_1573_:
{
if (v___y_1574_ == 0)
{
uint8_t v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1576_ = lean_uint8_dec_eq(v___y_1572_, v___x_1575_);
if (v___x_1576_ == 0)
{
uint8_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1578_ = lean_uint8_dec_eq(v___y_1572_, v___x_1577_);
return v___x_1578_;
}
else
{
return v___x_1576_;
}
}
else
{
return v___y_1574_;
}
}
v___jp_1579_:
{
if (v___y_1580_ == 0)
{
uint8_t v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1582_ = lean_uint8_dec_eq(v___y_1572_, v___x_1581_);
if (v___x_1582_ == 0)
{
uint8_t v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1584_ = lean_uint8_dec_eq(v___y_1572_, v___x_1583_);
if (v___x_1584_ == 0)
{
uint8_t v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1586_ = lean_uint8_dec_eq(v___y_1572_, v___x_1585_);
if (v___x_1586_ == 0)
{
uint8_t v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1588_ = lean_uint8_dec_eq(v___y_1572_, v___x_1587_);
if (v___x_1588_ == 0)
{
uint8_t v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1590_ = lean_uint8_dec_eq(v___y_1572_, v___x_1589_);
if (v___x_1590_ == 0)
{
uint8_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_1592_ = lean_uint8_dec_eq(v___y_1572_, v___x_1591_);
if (v___x_1592_ == 0)
{
uint8_t v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1594_ = lean_uint8_dec_eq(v___y_1572_, v___x_1593_);
if (v___x_1594_ == 0)
{
uint8_t v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1596_ = lean_uint8_dec_eq(v___y_1572_, v___x_1595_);
if (v___x_1596_ == 0)
{
uint8_t v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1598_ = lean_uint8_dec_eq(v___y_1572_, v___x_1597_);
v___y_1574_ = v___x_1598_;
goto v___jp_1573_;
}
else
{
v___y_1574_ = v___x_1596_;
goto v___jp_1573_;
}
}
else
{
v___y_1574_ = v___x_1594_;
goto v___jp_1573_;
}
}
else
{
v___y_1574_ = v___x_1592_;
goto v___jp_1573_;
}
}
else
{
v___y_1574_ = v___x_1590_;
goto v___jp_1573_;
}
}
else
{
v___y_1574_ = v___x_1588_;
goto v___jp_1573_;
}
}
else
{
v___y_1574_ = v___x_1586_;
goto v___jp_1573_;
}
}
else
{
v___y_1574_ = v___x_1584_;
goto v___jp_1573_;
}
}
else
{
v___y_1574_ = v___x_1582_;
goto v___jp_1573_;
}
}
else
{
return v___y_1580_;
}
}
v___jp_1599_:
{
if (v___y_1600_ == 0)
{
uint8_t v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1602_ = lean_uint8_dec_eq(v___y_1572_, v___x_1601_);
if (v___x_1602_ == 0)
{
uint8_t v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1604_ = lean_uint8_dec_eq(v___y_1572_, v___x_1603_);
v___y_1580_ = v___x_1604_;
goto v___jp_1579_;
}
else
{
v___y_1580_ = v___x_1602_;
goto v___jp_1579_;
}
}
else
{
return v___y_1600_;
}
}
v___jp_1605_:
{
if (v___y_1606_ == 0)
{
uint8_t v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1608_ = lean_uint8_dec_eq(v___y_1572_, v___x_1607_);
if (v___x_1608_ == 0)
{
uint8_t v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1610_ = lean_uint8_dec_eq(v___y_1572_, v___x_1609_);
v___y_1600_ = v___x_1610_;
goto v___jp_1599_;
}
else
{
v___y_1600_ = v___x_1608_;
goto v___jp_1599_;
}
}
else
{
return v___y_1606_;
}
}
v___jp_1611_:
{
if (v___y_1612_ == 0)
{
uint8_t v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_1614_ = lean_uint8_dec_eq(v___y_1572_, v___x_1613_);
if (v___x_1614_ == 0)
{
uint8_t v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_1616_ = lean_uint8_dec_eq(v___y_1572_, v___x_1615_);
v___y_1606_ = v___x_1616_;
goto v___jp_1605_;
}
else
{
v___y_1606_ = v___x_1614_;
goto v___jp_1605_;
}
}
else
{
return v___y_1612_;
}
}
v___jp_1617_:
{
if (v___y_1618_ == 0)
{
uint8_t v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1620_ = lean_uint8_dec_le(v___x_1619_, v___y_1572_);
if (v___x_1620_ == 0)
{
v___y_1612_ = v___x_1620_;
goto v___jp_1611_;
}
else
{
uint8_t v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1622_ = lean_uint8_dec_le(v___y_1572_, v___x_1621_);
v___y_1612_ = v___x_1622_;
goto v___jp_1611_;
}
}
else
{
return v___y_1618_;
}
}
v___jp_1623_:
{
if (v___y_1624_ == 0)
{
uint8_t v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1626_ = lean_uint8_dec_le(v___x_1625_, v___y_1572_);
if (v___x_1626_ == 0)
{
v___y_1618_ = v___x_1626_;
goto v___jp_1617_;
}
else
{
uint8_t v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1628_ = lean_uint8_dec_le(v___y_1572_, v___x_1627_);
v___y_1618_ = v___x_1628_;
goto v___jp_1617_;
}
}
else
{
return v___y_1624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1___boxed(lean_object* v___y_1633_){
_start:
{
uint8_t v___y_19202__boxed_1634_; uint8_t v_res_1635_; lean_object* v_r_1636_; 
v___y_19202__boxed_1634_ = lean_unbox(v___y_1633_);
v_res_1635_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__1(v___y_19202__boxed_1634_);
v_r_1636_ = lean_box(v_res_1635_);
return v_r_1636_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___f_1638_; lean_object* v___x_1639_; 
v___f_1638_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__0));
v___x_1639_ = l_Std_Http_URI_EncodedString_empty(v___f_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(lean_object* v_config_1647_, lean_object* v_b_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v_array_1662_; lean_object* v_idx_1663_; lean_object* v_fst_1664_; lean_object* v_snd_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1867_; 
v_array_1662_ = lean_ctor_get(v___y_1649_, 0);
v_idx_1663_ = lean_ctor_get(v___y_1649_, 1);
v_fst_1664_ = lean_ctor_get(v_b_1648_, 0);
v_snd_1665_ = lean_ctor_get(v_b_1648_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_b_1648_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1667_ = v_b_1648_;
v_isShared_1668_ = v_isSharedCheck_1867_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_snd_1665_);
lean_inc(v_fst_1664_);
lean_dec(v_b_1648_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1867_;
goto v_resetjp_1666_;
}
v___jp_1650_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___y_1652_);
lean_ctor_set(v___x_1654_, 1, v___y_1651_);
v_b_1648_ = v___x_1654_;
v___y_1649_ = v___y_1653_;
goto _start;
}
v___jp_1656_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___y_1659_);
lean_ctor_set(v___x_1660_, 1, v___y_1658_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___y_1657_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
return v___x_1661_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = lean_byte_array_size(v_array_1662_);
v___x_1670_ = lean_nat_dec_lt(v_idx_1663_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref(v_config_1647_);
if (v_isShared_1668_ == 0)
{
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_fst_1664_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_snd_1665_);
v___x_1672_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___y_1649_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
return v___x_1673_;
}
}
else
{
if (v___x_1670_ == 0)
{
lean_object* v___x_1676_; 
lean_dec_ref(v_config_1647_);
if (v_isShared_1668_ == 0)
{
v___x_1676_ = v___x_1667_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_fst_1664_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_snd_1665_);
v___x_1676_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1649_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
return v___x_1677_;
}
}
else
{
uint8_t v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = lean_byte_array_fget(v_array_1662_, v_idx_1663_);
v___x_1680_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; uint8_t v___y_1794_; uint8_t v___y_1798_; uint8_t v___y_1802_; uint8_t v___y_1808_; uint8_t v___y_1828_; uint8_t v___y_1834_; uint8_t v___y_1840_; uint8_t v___y_1846_; uint8_t v___y_1852_; uint8_t v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1858_ = lean_uint8_dec_eq(v___x_1679_, v___x_1857_);
if (v___x_1858_ == 0)
{
uint8_t v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_1860_ = lean_uint8_dec_le(v___x_1859_, v___x_1679_);
if (v___x_1860_ == 0)
{
v___y_1852_ = v___x_1860_;
goto v___jp_1851_;
}
else
{
uint8_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_1862_ = lean_uint8_dec_le(v___x_1679_, v___x_1861_);
v___y_1852_ = v___x_1862_;
goto v___jp_1851_;
}
}
else
{
v___y_1794_ = v___x_1858_;
goto v___jp_1793_;
}
v___jp_1681_:
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = lean_array_get_size(v___y_1683_);
v___x_1687_ = lean_nat_dec_le(v___y_1684_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
lean_dec(v___y_1684_);
v___x_1688_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1);
v___x_1689_ = lean_array_push(v___y_1683_, v___x_1688_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___y_1682_);
lean_ctor_set(v___x_1667_, 0, v___x_1689_);
v___x_1691_ = v___x_1667_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___y_1682_);
v___x_1691_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
v_b_1648_ = v___x_1691_;
v___y_1649_ = v___y_1685_;
goto _start;
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_del_object(v___x_1667_);
lean_dec_ref(v_config_1647_);
v___x_1694_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1695_ = l_Nat_reprFast(v___y_1684_);
v___x_1696_ = lean_string_append(v___x_1694_, v___x_1695_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1698_ = lean_string_append(v___x_1696_, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___y_1685_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
return v___x_1700_;
}
}
v___jp_1701_:
{
lean_object* v_maxPathSegments_1702_; lean_object* v_maxTotalPathLength_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_maxPathSegments_1702_ = lean_ctor_get(v_config_1647_, 6);
v_maxTotalPathLength_1703_ = lean_ctor_get(v_config_1647_, 7);
v___x_1704_ = lean_array_get_size(v_fst_1664_);
v___x_1705_ = lean_nat_dec_le(v_maxPathSegments_1702_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1647_, v___y_1649_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_pos_1707_; lean_object* v_res_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1776_; 
v_pos_1707_ = lean_ctor_get(v___x_1706_, 0);
v_res_1708_ = lean_ctor_get(v___x_1706_, 1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1710_ = v___x_1706_;
v_isShared_1711_ = v_isSharedCheck_1776_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_res_1708_);
lean_inc(v_pos_1707_);
lean_dec(v___x_1706_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1776_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_inc(v_res_1708_);
v___x_1712_ = l_ByteSlice_toByteArray(v_res_1708_);
v___x_1713_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1712_);
if (lean_obj_tag(v___x_1713_) == 1)
{
lean_object* v_val_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1771_; 
v_val_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1771_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_val_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1771_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1718_ = l_ByteSlice_size(v_res_1708_);
lean_dec(v_res_1708_);
v___x_1719_ = lean_nat_add(v_snd_1665_, v___x_1718_);
lean_dec(v___x_1718_);
lean_dec(v_snd_1665_);
v___x_1720_ = lean_nat_dec_lt(v_maxTotalPathLength_1703_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v_array_1721_; lean_object* v_idx_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_array_1721_ = lean_ctor_get(v_pos_1707_, 0);
v_idx_1722_ = lean_ctor_get(v_pos_1707_, 1);
v___x_1723_ = lean_array_push(v_fst_1664_, v_val_1714_);
v___x_1724_ = lean_byte_array_size(v_array_1721_);
v___x_1725_ = lean_nat_dec_lt(v_idx_1722_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_del_object(v___x_1716_);
lean_del_object(v___x_1710_);
lean_del_object(v___x_1667_);
lean_dec_ref(v_config_1647_);
v___y_1657_ = v_pos_1707_;
v___y_1658_ = v___x_1719_;
v___y_1659_ = v___x_1723_;
goto v___jp_1656_;
}
else
{
uint8_t v___x_1726_; uint8_t v___x_1727_; uint8_t v___x_1728_; 
v___x_1726_ = lean_byte_array_fget(v_array_1721_, v_idx_1722_);
v___x_1727_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1728_ = lean_uint8_dec_eq(v___x_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_del_object(v___x_1716_);
lean_del_object(v___x_1710_);
lean_del_object(v___x_1667_);
lean_dec_ref(v_config_1647_);
v___y_1657_ = v_pos_1707_;
v___y_1658_ = v___x_1719_;
v___y_1659_ = v___x_1723_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1729_ = lean_unsigned_to_nat(1u);
v___x_1730_ = lean_nat_add(v___x_1719_, v___x_1729_);
lean_dec(v___x_1719_);
v___x_1731_ = lean_nat_dec_lt(v_maxTotalPathLength_1703_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_del_object(v___x_1716_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_dec(v___x_1730_);
lean_dec_ref(v___x_1723_);
lean_del_object(v___x_1667_);
lean_dec_ref(v_config_1647_);
v___x_1732_ = lean_box(0);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 1, v___x_1732_);
v___x_1734_ = v___x_1710_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
else
{
lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1746_; 
lean_inc(v_idx_1722_);
lean_inc_ref(v_array_1721_);
lean_del_object(v___x_1710_);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_pos_1707_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; lean_object* v_unused_1748_; 
v_unused_1747_ = lean_ctor_get(v_pos_1707_, 1);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_pos_1707_, 0);
lean_dec(v_unused_1748_);
v___x_1737_ = v_pos_1707_;
v_isShared_1738_ = v_isSharedCheck_1746_;
goto v_resetjp_1736_;
}
else
{
lean_dec(v_pos_1707_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1746_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_nat_add(v_idx_1722_, v___x_1729_);
lean_dec(v_idx_1722_);
lean_inc(v___x_1739_);
lean_inc_ref(v_array_1721_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v___x_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_array_1721_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_nat_dec_lt(v___x_1739_, v___x_1724_);
if (v___x_1742_ == 0)
{
lean_dec(v___x_1739_);
lean_dec_ref(v_array_1721_);
if (v___x_1725_ == 0)
{
lean_del_object(v___x_1667_);
v___y_1651_ = v___x_1730_;
v___y_1652_ = v___x_1723_;
v___y_1653_ = v___x_1741_;
goto v___jp_1650_;
}
else
{
lean_inc(v_maxPathSegments_1702_);
v___y_1682_ = v___x_1730_;
v___y_1683_ = v___x_1723_;
v___y_1684_ = v_maxPathSegments_1702_;
v___y_1685_ = v___x_1741_;
goto v___jp_1681_;
}
}
else
{
uint8_t v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = lean_byte_array_fget(v_array_1721_, v___x_1739_);
lean_dec(v___x_1739_);
lean_dec_ref(v_array_1721_);
v___x_1744_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1743_);
if (v___x_1744_ == 0)
{
lean_del_object(v___x_1667_);
v___y_1651_ = v___x_1730_;
v___y_1652_ = v___x_1723_;
v___y_1653_ = v___x_1741_;
goto v___jp_1650_;
}
else
{
lean_inc(v_maxPathSegments_1702_);
v___y_1682_ = v___x_1730_;
v___y_1683_ = v___x_1723_;
v___y_1684_ = v_maxPathSegments_1702_;
v___y_1685_ = v___x_1741_;
goto v___jp_1681_;
}
}
}
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
lean_inc(v_maxTotalPathLength_1703_);
lean_dec(v___x_1730_);
lean_dec_ref(v___x_1723_);
lean_del_object(v___x_1667_);
lean_dec_ref(v_config_1647_);
v___x_1749_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1750_ = l_Nat_reprFast(v_maxTotalPathLength_1703_);
v___x_1751_ = lean_string_append(v___x_1749_, v___x_1750_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1753_ = lean_string_append(v___x_1751_, v___x_1752_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1753_);
v___x_1755_ = v___x_1716_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 1, v___x_1755_);
v___x_1757_ = v___x_1710_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1755_);
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
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_inc(v_maxTotalPathLength_1703_);
lean_dec(v___x_1719_);
lean_dec(v_val_1714_);
lean_del_object(v___x_1667_);
lean_dec(v_fst_1664_);
lean_dec_ref(v_config_1647_);
v___x_1760_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1761_ = l_Nat_reprFast(v_maxTotalPathLength_1703_);
v___x_1762_ = lean_string_append(v___x_1760_, v___x_1761_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1764_ = lean_string_append(v___x_1762_, v___x_1763_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1764_);
v___x_1766_ = v___x_1716_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 1, v___x_1766_);
v___x_1768_ = v___x_1710_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
lean_dec(v___x_1713_);
lean_dec(v_res_1708_);
lean_del_object(v___x_1667_);
lean_dec(v_snd_1665_);
lean_dec(v_fst_1664_);
lean_dec_ref(v_config_1647_);
v___x_1772_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7));
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 1);
lean_ctor_set(v___x_1710_, 1, v___x_1772_);
v___x_1774_ = v___x_1710_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_pos_1707_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_pos_1777_; lean_object* v_err_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_del_object(v___x_1667_);
lean_dec(v_snd_1665_);
lean_dec(v_fst_1664_);
lean_dec_ref(v_config_1647_);
v_pos_1777_ = lean_ctor_get(v___x_1706_, 0);
v_err_1778_ = lean_ctor_get(v___x_1706_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1706_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_err_1778_);
lean_inc(v_pos_1777_);
lean_dec(v___x_1706_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_pos_1777_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_err_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_inc(v_maxPathSegments_1702_);
lean_del_object(v___x_1667_);
lean_dec(v_snd_1665_);
lean_dec(v_fst_1664_);
lean_dec_ref(v_config_1647_);
v___x_1786_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1787_ = l_Nat_reprFast(v_maxPathSegments_1702_);
v___x_1788_ = lean_string_append(v___x_1786_, v___x_1787_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1790_ = lean_string_append(v___x_1788_, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___y_1649_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
return v___x_1792_;
}
}
v___jp_1793_:
{
if (v___y_1794_ == 0)
{
if (v___x_1670_ == 0)
{
goto v___jp_1701_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_del_object(v___x_1667_);
lean_dec_ref(v_config_1647_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_fst_1664_);
lean_ctor_set(v___x_1795_, 1, v_snd_1665_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___y_1649_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
return v___x_1796_;
}
}
else
{
goto v___jp_1701_;
}
}
v___jp_1797_:
{
if (v___y_1798_ == 0)
{
uint8_t v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_1800_ = lean_uint8_dec_eq(v___x_1679_, v___x_1799_);
if (v___x_1800_ == 0)
{
v___y_1794_ = v___x_1800_;
goto v___jp_1793_;
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
v___jp_1801_:
{
if (v___y_1802_ == 0)
{
uint8_t v___x_1803_; uint8_t v___x_1804_; 
v___x_1803_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_1804_ = lean_uint8_dec_eq(v___x_1679_, v___x_1803_);
if (v___x_1804_ == 0)
{
uint8_t v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_1806_ = lean_uint8_dec_eq(v___x_1679_, v___x_1805_);
v___y_1798_ = v___x_1806_;
goto v___jp_1797_;
}
else
{
v___y_1798_ = v___x_1804_;
goto v___jp_1797_;
}
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
v___jp_1807_:
{
if (v___y_1808_ == 0)
{
uint8_t v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_1810_ = lean_uint8_dec_eq(v___x_1679_, v___x_1809_);
if (v___x_1810_ == 0)
{
uint8_t v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_1812_ = lean_uint8_dec_eq(v___x_1679_, v___x_1811_);
if (v___x_1812_ == 0)
{
uint8_t v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_1814_ = lean_uint8_dec_eq(v___x_1679_, v___x_1813_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_1816_ = lean_uint8_dec_eq(v___x_1679_, v___x_1815_);
if (v___x_1816_ == 0)
{
uint8_t v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_1818_ = lean_uint8_dec_eq(v___x_1679_, v___x_1817_);
if (v___x_1818_ == 0)
{
uint8_t v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_1820_ = lean_uint8_dec_eq(v___x_1679_, v___x_1819_);
if (v___x_1820_ == 0)
{
uint8_t v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_1822_ = lean_uint8_dec_eq(v___x_1679_, v___x_1821_);
if (v___x_1822_ == 0)
{
uint8_t v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_1824_ = lean_uint8_dec_eq(v___x_1679_, v___x_1823_);
if (v___x_1824_ == 0)
{
uint8_t v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_1826_ = lean_uint8_dec_eq(v___x_1679_, v___x_1825_);
v___y_1802_ = v___x_1826_;
goto v___jp_1801_;
}
else
{
v___y_1802_ = v___x_1824_;
goto v___jp_1801_;
}
}
else
{
v___y_1802_ = v___x_1822_;
goto v___jp_1801_;
}
}
else
{
v___y_1802_ = v___x_1820_;
goto v___jp_1801_;
}
}
else
{
v___y_1802_ = v___x_1818_;
goto v___jp_1801_;
}
}
else
{
v___y_1802_ = v___x_1816_;
goto v___jp_1801_;
}
}
else
{
v___y_1802_ = v___x_1814_;
goto v___jp_1801_;
}
}
else
{
v___y_1802_ = v___x_1812_;
goto v___jp_1801_;
}
}
else
{
v___y_1802_ = v___x_1810_;
goto v___jp_1801_;
}
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
v___jp_1827_:
{
if (v___y_1828_ == 0)
{
uint8_t v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_1830_ = lean_uint8_dec_eq(v___x_1679_, v___x_1829_);
if (v___x_1830_ == 0)
{
uint8_t v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_1832_ = lean_uint8_dec_eq(v___x_1679_, v___x_1831_);
v___y_1808_ = v___x_1832_;
goto v___jp_1807_;
}
else
{
v___y_1808_ = v___x_1830_;
goto v___jp_1807_;
}
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
v___jp_1833_:
{
if (v___y_1834_ == 0)
{
uint8_t v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_1836_ = lean_uint8_dec_eq(v___x_1679_, v___x_1835_);
if (v___x_1836_ == 0)
{
uint8_t v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_1838_ = lean_uint8_dec_eq(v___x_1679_, v___x_1837_);
v___y_1828_ = v___x_1838_;
goto v___jp_1827_;
}
else
{
v___y_1828_ = v___x_1836_;
goto v___jp_1827_;
}
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
v___jp_1839_:
{
if (v___y_1840_ == 0)
{
uint8_t v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_1842_ = lean_uint8_dec_eq(v___x_1679_, v___x_1841_);
if (v___x_1842_ == 0)
{
uint8_t v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_1844_ = lean_uint8_dec_eq(v___x_1679_, v___x_1843_);
v___y_1834_ = v___x_1844_;
goto v___jp_1833_;
}
else
{
v___y_1834_ = v___x_1842_;
goto v___jp_1833_;
}
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
v___jp_1845_:
{
if (v___y_1846_ == 0)
{
uint8_t v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_1848_ = lean_uint8_dec_le(v___x_1847_, v___x_1679_);
if (v___x_1848_ == 0)
{
v___y_1840_ = v___x_1848_;
goto v___jp_1839_;
}
else
{
uint8_t v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_1850_ = lean_uint8_dec_le(v___x_1679_, v___x_1849_);
v___y_1840_ = v___x_1850_;
goto v___jp_1839_;
}
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
v___jp_1851_:
{
if (v___y_1852_ == 0)
{
uint8_t v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_1854_ = lean_uint8_dec_le(v___x_1853_, v___x_1679_);
if (v___x_1854_ == 0)
{
v___y_1846_ = v___x_1854_;
goto v___jp_1845_;
}
else
{
uint8_t v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_1856_ = lean_uint8_dec_le(v___x_1679_, v___x_1855_);
v___y_1846_ = v___x_1856_;
goto v___jp_1845_;
}
}
else
{
v___y_1794_ = v___x_1670_;
goto v___jp_1793_;
}
}
}
else
{
lean_object* v___x_1864_; 
lean_dec_ref(v_config_1647_);
if (v_isShared_1668_ == 0)
{
v___x_1864_ = v___x_1667_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_fst_1664_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_snd_1665_);
v___x_1864_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___y_1649_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
return v___x_1865_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0(lean_object* v_config_1868_, lean_object* v_b_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v_array_1883_; lean_object* v_idx_1884_; lean_object* v_fst_1885_; lean_object* v_snd_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_2088_; 
v_array_1883_ = lean_ctor_get(v___y_1870_, 0);
v_idx_1884_ = lean_ctor_get(v___y_1870_, 1);
v_fst_1885_ = lean_ctor_get(v_b_1869_, 0);
v_snd_1886_ = lean_ctor_get(v_b_1869_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_b_1869_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_1888_ = v_b_1869_;
v_isShared_1889_ = v_isSharedCheck_2088_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snd_1886_);
lean_inc(v_fst_1885_);
lean_dec(v_b_1869_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_2088_;
goto v_resetjp_1887_;
}
v___jp_1871_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___y_1872_);
lean_ctor_set(v___x_1875_, 1, v___y_1874_);
v___x_1876_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(v_config_1868_, v___x_1875_, v___y_1873_);
return v___x_1876_;
}
v___jp_1877_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___y_1878_);
lean_ctor_set(v___x_1881_, 1, v___y_1879_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___y_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
return v___x_1882_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_byte_array_size(v_array_1883_);
v___x_1891_ = lean_nat_dec_lt(v_idx_1884_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1893_; 
lean_dec_ref(v_config_1868_);
if (v_isShared_1889_ == 0)
{
v___x_1893_ = v___x_1888_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_fst_1885_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_snd_1886_);
v___x_1893_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___y_1870_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
return v___x_1894_;
}
}
else
{
if (v___x_1891_ == 0)
{
lean_object* v___x_1897_; 
lean_dec_ref(v_config_1868_);
if (v_isShared_1889_ == 0)
{
v___x_1897_ = v___x_1888_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_fst_1885_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_snd_1886_);
v___x_1897_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___y_1870_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
return v___x_1898_;
}
}
else
{
uint8_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_byte_array_fget(v_array_1883_, v_idx_1884_);
v___x_1901_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___y_2015_; uint8_t v___y_2019_; uint8_t v___y_2023_; uint8_t v___y_2029_; uint8_t v___y_2049_; uint8_t v___y_2055_; uint8_t v___y_2061_; uint8_t v___y_2067_; uint8_t v___y_2073_; uint8_t v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2079_ = lean_uint8_dec_eq(v___x_1900_, v___x_2078_);
if (v___x_2079_ == 0)
{
uint8_t v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_2081_ = lean_uint8_dec_le(v___x_2080_, v___x_1900_);
if (v___x_2081_ == 0)
{
v___y_2073_ = v___x_2081_;
goto v___jp_2072_;
}
else
{
uint8_t v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_2083_ = lean_uint8_dec_le(v___x_1900_, v___x_2082_);
v___y_2073_ = v___x_2083_;
goto v___jp_2072_;
}
}
else
{
v___y_2015_ = v___x_2079_;
goto v___jp_2014_;
}
v___jp_1902_:
{
lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = lean_array_get_size(v___y_1903_);
v___x_1908_ = lean_nat_dec_le(v___y_1904_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec(v___y_1904_);
v___x_1909_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__1);
v___x_1910_ = lean_array_push(v___y_1903_, v___x_1909_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v___y_1906_);
lean_ctor_set(v___x_1888_, 0, v___x_1910_);
v___x_1912_ = v___x_1888_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___y_1906_);
v___x_1912_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; 
v___x_1913_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0(v_config_1868_, v___x_1912_, v___y_1905_);
return v___x_1913_;
}
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1903_);
lean_del_object(v___x_1888_);
lean_dec_ref(v_config_1868_);
v___x_1915_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_1916_ = l_Nat_reprFast(v___y_1904_);
v___x_1917_ = lean_string_append(v___x_1915_, v___x_1916_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_1919_ = lean_string_append(v___x_1917_, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___y_1905_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
return v___x_1921_;
}
}
v___jp_1922_:
{
lean_object* v_maxPathSegments_1923_; lean_object* v_maxTotalPathLength_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v_maxPathSegments_1923_ = lean_ctor_get(v_config_1868_, 6);
v_maxTotalPathLength_1924_ = lean_ctor_get(v_config_1868_, 7);
v___x_1925_ = lean_array_get_size(v_fst_1885_);
v___x_1926_ = lean_nat_dec_le(v_maxPathSegments_1923_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseSegment(v_config_1868_, v___y_1870_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_pos_1928_; lean_object* v_res_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1997_; 
v_pos_1928_ = lean_ctor_get(v___x_1927_, 0);
v_res_1929_ = lean_ctor_get(v___x_1927_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1931_ = v___x_1927_;
v_isShared_1932_ = v_isSharedCheck_1997_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_res_1929_);
lean_inc(v_pos_1928_);
lean_dec(v___x_1927_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1997_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_inc(v_res_1929_);
v___x_1933_ = l_ByteSlice_toByteArray(v_res_1929_);
v___x_1934_ = l_Std_Http_URI_EncodedSegment_ofByteArray_x3f(v___x_1933_);
if (lean_obj_tag(v___x_1934_) == 1)
{
lean_object* v_val_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1992_; 
v_val_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1992_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_val_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1992_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1939_ = l_ByteSlice_size(v_res_1929_);
lean_dec(v_res_1929_);
v___x_1940_ = lean_nat_add(v_snd_1886_, v___x_1939_);
lean_dec(v___x_1939_);
lean_dec(v_snd_1886_);
v___x_1941_ = lean_nat_dec_lt(v_maxTotalPathLength_1924_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v_array_1942_; lean_object* v_idx_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v_array_1942_ = lean_ctor_get(v_pos_1928_, 0);
v_idx_1943_ = lean_ctor_get(v_pos_1928_, 1);
v___x_1944_ = lean_array_push(v_fst_1885_, v_val_1935_);
v___x_1945_ = lean_byte_array_size(v_array_1942_);
v___x_1946_ = lean_nat_dec_lt(v_idx_1943_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_del_object(v___x_1937_);
lean_del_object(v___x_1931_);
lean_del_object(v___x_1888_);
lean_dec_ref(v_config_1868_);
v___y_1878_ = v___x_1944_;
v___y_1879_ = v___x_1940_;
v___y_1880_ = v_pos_1928_;
goto v___jp_1877_;
}
else
{
uint8_t v___x_1947_; uint8_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = lean_byte_array_fget(v_array_1942_, v_idx_1943_);
v___x_1948_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_1949_ = lean_uint8_dec_eq(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_del_object(v___x_1937_);
lean_del_object(v___x_1931_);
lean_del_object(v___x_1888_);
lean_dec_ref(v_config_1868_);
v___y_1878_ = v___x_1944_;
v___y_1879_ = v___x_1940_;
v___y_1880_ = v_pos_1928_;
goto v___jp_1877_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = lean_nat_add(v___x_1940_, v___x_1950_);
lean_dec(v___x_1940_);
v___x_1952_ = lean_nat_dec_lt(v_maxTotalPathLength_1924_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_del_object(v___x_1937_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
lean_dec(v___x_1951_);
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1888_);
lean_dec_ref(v_config_1868_);
v___x_1953_ = lean_box(0);
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 1, v___x_1953_);
v___x_1955_ = v___x_1931_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_pos_1928_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
else
{
lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1967_; 
lean_inc(v_idx_1943_);
lean_inc_ref(v_array_1942_);
lean_del_object(v___x_1931_);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_pos_1928_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; lean_object* v_unused_1969_; 
v_unused_1968_ = lean_ctor_get(v_pos_1928_, 1);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_pos_1928_, 0);
lean_dec(v_unused_1969_);
v___x_1958_ = v_pos_1928_;
v_isShared_1959_ = v_isSharedCheck_1967_;
goto v_resetjp_1957_;
}
else
{
lean_dec(v_pos_1928_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1967_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1960_ = lean_nat_add(v_idx_1943_, v___x_1950_);
lean_dec(v_idx_1943_);
lean_inc(v___x_1960_);
lean_inc_ref(v_array_1942_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v___x_1960_);
v___x_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_array_1942_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_nat_dec_lt(v___x_1960_, v___x_1945_);
if (v___x_1963_ == 0)
{
lean_dec(v___x_1960_);
lean_dec_ref(v_array_1942_);
if (v___x_1946_ == 0)
{
lean_del_object(v___x_1888_);
v___y_1872_ = v___x_1944_;
v___y_1873_ = v___x_1962_;
v___y_1874_ = v___x_1951_;
goto v___jp_1871_;
}
else
{
lean_inc(v_maxPathSegments_1923_);
v___y_1903_ = v___x_1944_;
v___y_1904_ = v_maxPathSegments_1923_;
v___y_1905_ = v___x_1962_;
v___y_1906_ = v___x_1951_;
goto v___jp_1902_;
}
}
else
{
uint8_t v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = lean_byte_array_fget(v_array_1942_, v___x_1960_);
lean_dec(v___x_1960_);
lean_dec_ref(v_array_1942_);
v___x_1965_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0___lam__0(v___x_1964_);
if (v___x_1965_ == 0)
{
lean_del_object(v___x_1888_);
v___y_1872_ = v___x_1944_;
v___y_1873_ = v___x_1962_;
v___y_1874_ = v___x_1951_;
goto v___jp_1871_;
}
else
{
lean_inc(v_maxPathSegments_1923_);
v___y_1903_ = v___x_1944_;
v___y_1904_ = v_maxPathSegments_1923_;
v___y_1905_ = v___x_1962_;
v___y_1906_ = v___x_1951_;
goto v___jp_1902_;
}
}
}
}
}
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
lean_inc(v_maxTotalPathLength_1924_);
lean_dec(v___x_1951_);
lean_dec_ref(v___x_1944_);
lean_del_object(v___x_1888_);
lean_dec_ref(v_config_1868_);
v___x_1970_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1971_ = l_Nat_reprFast(v_maxTotalPathLength_1924_);
v___x_1972_ = lean_string_append(v___x_1970_, v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1974_ = lean_string_append(v___x_1972_, v___x_1973_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1974_);
v___x_1976_ = v___x_1937_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1978_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 1, v___x_1976_);
v___x_1978_ = v___x_1931_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_pos_1928_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
lean_inc(v_maxTotalPathLength_1924_);
lean_dec(v___x_1940_);
lean_dec(v_val_1935_);
lean_del_object(v___x_1888_);
lean_dec(v_fst_1885_);
lean_dec_ref(v_config_1868_);
v___x_1981_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__4));
v___x_1982_ = l_Nat_reprFast(v_maxTotalPathLength_1924_);
v___x_1983_ = lean_string_append(v___x_1981_, v___x_1982_);
lean_dec_ref(v___x_1982_);
v___x_1984_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__5));
v___x_1985_ = lean_string_append(v___x_1983_, v___x_1984_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1985_);
v___x_1987_ = v___x_1937_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 1, v___x_1987_);
v___x_1989_ = v___x_1931_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_pos_1928_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
lean_dec(v___x_1934_);
lean_dec(v_res_1929_);
lean_del_object(v___x_1888_);
lean_dec(v_snd_1886_);
lean_dec(v_fst_1885_);
lean_dec_ref(v_config_1868_);
v___x_1993_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__7));
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 1, v___x_1993_);
v___x_1995_ = v___x_1931_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_pos_1928_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v_pos_1998_; lean_object* v_err_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_del_object(v___x_1888_);
lean_dec(v_snd_1886_);
lean_dec(v_fst_1885_);
lean_dec_ref(v_config_1868_);
v_pos_1998_ = lean_ctor_get(v___x_1927_, 0);
v_err_1999_ = lean_ctor_get(v___x_1927_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1927_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_err_1999_);
lean_inc(v_pos_1998_);
lean_dec(v___x_1927_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_pos_1998_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_err_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_inc(v_maxPathSegments_1923_);
lean_del_object(v___x_1888_);
lean_dec(v_snd_1886_);
lean_dec(v_fst_1885_);
lean_dec_ref(v_config_1868_);
v___x_2007_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__2));
v___x_2008_ = l_Nat_reprFast(v_maxPathSegments_1923_);
v___x_2009_ = lean_string_append(v___x_2007_, v___x_2008_);
lean_dec_ref(v___x_2008_);
v___x_2010_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_2011_ = lean_string_append(v___x_2009_, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___y_1870_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
return v___x_2013_;
}
}
v___jp_2014_:
{
if (v___y_2015_ == 0)
{
if (v___x_1891_ == 0)
{
goto v___jp_1922_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_del_object(v___x_1888_);
lean_dec_ref(v_config_1868_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_fst_1885_);
lean_ctor_set(v___x_2016_, 1, v_snd_1886_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___y_1870_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
return v___x_2017_;
}
}
else
{
goto v___jp_1922_;
}
}
v___jp_2018_:
{
if (v___y_2019_ == 0)
{
uint8_t v___x_2020_; uint8_t v___x_2021_; 
v___x_2020_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2021_ = lean_uint8_dec_eq(v___x_1900_, v___x_2020_);
if (v___x_2021_ == 0)
{
v___y_2015_ = v___x_2021_;
goto v___jp_2014_;
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
v___jp_2022_:
{
if (v___y_2023_ == 0)
{
uint8_t v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2025_ = lean_uint8_dec_eq(v___x_1900_, v___x_2024_);
if (v___x_2025_ == 0)
{
uint8_t v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2027_ = lean_uint8_dec_eq(v___x_1900_, v___x_2026_);
v___y_2019_ = v___x_2027_;
goto v___jp_2018_;
}
else
{
v___y_2019_ = v___x_2025_;
goto v___jp_2018_;
}
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
v___jp_2028_:
{
if (v___y_2029_ == 0)
{
uint8_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2031_ = lean_uint8_dec_eq(v___x_1900_, v___x_2030_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; uint8_t v___x_2033_; 
v___x_2032_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2033_ = lean_uint8_dec_eq(v___x_1900_, v___x_2032_);
if (v___x_2033_ == 0)
{
uint8_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2035_ = lean_uint8_dec_eq(v___x_1900_, v___x_2034_);
if (v___x_2035_ == 0)
{
uint8_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2037_ = lean_uint8_dec_eq(v___x_1900_, v___x_2036_);
if (v___x_2037_ == 0)
{
uint8_t v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2039_ = lean_uint8_dec_eq(v___x_1900_, v___x_2038_);
if (v___x_2039_ == 0)
{
uint8_t v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_2041_ = lean_uint8_dec_eq(v___x_1900_, v___x_2040_);
if (v___x_2041_ == 0)
{
uint8_t v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2043_ = lean_uint8_dec_eq(v___x_1900_, v___x_2042_);
if (v___x_2043_ == 0)
{
uint8_t v___x_2044_; uint8_t v___x_2045_; 
v___x_2044_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2045_ = lean_uint8_dec_eq(v___x_1900_, v___x_2044_);
if (v___x_2045_ == 0)
{
uint8_t v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2047_ = lean_uint8_dec_eq(v___x_1900_, v___x_2046_);
v___y_2023_ = v___x_2047_;
goto v___jp_2022_;
}
else
{
v___y_2023_ = v___x_2045_;
goto v___jp_2022_;
}
}
else
{
v___y_2023_ = v___x_2043_;
goto v___jp_2022_;
}
}
else
{
v___y_2023_ = v___x_2041_;
goto v___jp_2022_;
}
}
else
{
v___y_2023_ = v___x_2039_;
goto v___jp_2022_;
}
}
else
{
v___y_2023_ = v___x_2037_;
goto v___jp_2022_;
}
}
else
{
v___y_2023_ = v___x_2035_;
goto v___jp_2022_;
}
}
else
{
v___y_2023_ = v___x_2033_;
goto v___jp_2022_;
}
}
else
{
v___y_2023_ = v___x_2031_;
goto v___jp_2022_;
}
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
v___jp_2048_:
{
if (v___y_2049_ == 0)
{
uint8_t v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2051_ = lean_uint8_dec_eq(v___x_1900_, v___x_2050_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2053_ = lean_uint8_dec_eq(v___x_1900_, v___x_2052_);
v___y_2029_ = v___x_2053_;
goto v___jp_2028_;
}
else
{
v___y_2029_ = v___x_2051_;
goto v___jp_2028_;
}
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
v___jp_2054_:
{
if (v___y_2055_ == 0)
{
uint8_t v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2057_ = lean_uint8_dec_eq(v___x_1900_, v___x_2056_);
if (v___x_2057_ == 0)
{
uint8_t v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2059_ = lean_uint8_dec_eq(v___x_1900_, v___x_2058_);
v___y_2049_ = v___x_2059_;
goto v___jp_2048_;
}
else
{
v___y_2049_ = v___x_2057_;
goto v___jp_2048_;
}
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
v___jp_2060_:
{
if (v___y_2061_ == 0)
{
uint8_t v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_2063_ = lean_uint8_dec_eq(v___x_1900_, v___x_2062_);
if (v___x_2063_ == 0)
{
uint8_t v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_2065_ = lean_uint8_dec_eq(v___x_1900_, v___x_2064_);
v___y_2055_ = v___x_2065_;
goto v___jp_2054_;
}
else
{
v___y_2055_ = v___x_2063_;
goto v___jp_2054_;
}
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
v___jp_2066_:
{
if (v___y_2067_ == 0)
{
uint8_t v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2069_ = lean_uint8_dec_le(v___x_2068_, v___x_1900_);
if (v___x_2069_ == 0)
{
v___y_2061_ = v___x_2069_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2071_ = lean_uint8_dec_le(v___x_1900_, v___x_2070_);
v___y_2061_ = v___x_2071_;
goto v___jp_2060_;
}
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
v___jp_2072_:
{
if (v___y_2073_ == 0)
{
uint8_t v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2075_ = lean_uint8_dec_le(v___x_2074_, v___x_1900_);
if (v___x_2075_ == 0)
{
v___y_2067_ = v___x_2075_;
goto v___jp_2066_;
}
else
{
uint8_t v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2077_ = lean_uint8_dec_le(v___x_1900_, v___x_2076_);
v___y_2067_ = v___x_2077_;
goto v___jp_2066_;
}
}
else
{
v___y_2015_ = v___x_1891_;
goto v___jp_2014_;
}
}
}
else
{
lean_object* v___x_2085_; 
lean_dec_ref(v_config_1868_);
if (v_isShared_1889_ == 0)
{
v___x_2085_ = v___x_1888_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_fst_1885_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_snd_1886_);
v___x_2085_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; 
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___y_1870_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
return v___x_2086_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath(lean_object* v_config_2100_, uint8_t v_forceAbsolute_2101_, uint8_t v_allowEmpty_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___y_2105_; lean_object* v___y_2109_; lean_object* v_array_2112_; lean_object* v_idx_2113_; uint8_t v_isAbsolute_2114_; lean_object* v___x_2115_; lean_object* v_segments_2116_; uint8_t v_isAbsolute_2118_; lean_object* v_totalLength_2119_; lean_object* v___y_2120_; lean_object* v___y_2144_; uint8_t v___y_2148_; lean_object* v_pos_2149_; uint8_t v_res_2150_; uint8_t v___y_2152_; lean_object* v_pos_2153_; uint8_t v___y_2159_; lean_object* v___y_2160_; uint8_t v___y_2182_; lean_object* v_pos_2183_; uint8_t v_res_2184_; lean_object* v_pos_2186_; lean_object* v_array_2187_; lean_object* v_idx_2188_; uint8_t v_res_2189_; uint8_t v___y_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_array_2112_ = lean_ctor_get(v_a_2103_, 0);
lean_inc_ref(v_array_2112_);
v_idx_2113_ = lean_ctor_get(v_a_2103_, 1);
lean_inc(v_idx_2113_);
v_isAbsolute_2114_ = 0;
v___x_2115_ = lean_unsigned_to_nat(0u);
v_segments_2116_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__4));
v___x_2195_ = lean_byte_array_size(v_array_2112_);
v___x_2196_ = lean_nat_dec_lt(v_idx_2113_, v___x_2195_);
if (v___x_2196_ == 0)
{
v_pos_2186_ = v_a_2103_;
v_array_2187_ = v_array_2112_;
v_idx_2188_ = v_idx_2113_;
v_res_2189_ = v_isAbsolute_2114_;
goto v___jp_2185_;
}
else
{
uint8_t v___x_2197_; uint8_t v___y_2199_; uint8_t v___y_2205_; uint8_t v___y_2211_; uint8_t v___y_2231_; uint8_t v___y_2237_; uint8_t v___y_2243_; uint8_t v___y_2249_; uint8_t v___y_2255_; uint8_t v___x_2260_; uint8_t v___x_2261_; 
v___x_2197_ = lean_byte_array_fget(v_array_2112_, v_idx_2113_);
v___x_2260_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_2261_ = lean_uint8_dec_le(v___x_2260_, v___x_2197_);
if (v___x_2261_ == 0)
{
v___y_2255_ = v___x_2261_;
goto v___jp_2254_;
}
else
{
uint8_t v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_2263_ = lean_uint8_dec_le(v___x_2197_, v___x_2262_);
v___y_2255_ = v___x_2263_;
goto v___jp_2254_;
}
v___jp_2198_:
{
if (v___y_2199_ == 0)
{
uint8_t v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2201_ = lean_uint8_dec_eq(v___x_2197_, v___x_2200_);
if (v___x_2201_ == 0)
{
uint8_t v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2203_ = lean_uint8_dec_eq(v___x_2197_, v___x_2202_);
v___y_2194_ = v___x_2203_;
goto v___jp_2193_;
}
else
{
v___y_2194_ = v___x_2201_;
goto v___jp_2193_;
}
}
else
{
v___y_2194_ = v___x_2196_;
goto v___jp_2193_;
}
}
v___jp_2204_:
{
if (v___y_2205_ == 0)
{
uint8_t v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2207_ = lean_uint8_dec_eq(v___x_2197_, v___x_2206_);
if (v___x_2207_ == 0)
{
uint8_t v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2209_ = lean_uint8_dec_eq(v___x_2197_, v___x_2208_);
v___y_2199_ = v___x_2209_;
goto v___jp_2198_;
}
else
{
v___y_2199_ = v___x_2207_;
goto v___jp_2198_;
}
}
else
{
v___y_2194_ = v___x_2196_;
goto v___jp_2193_;
}
}
v___jp_2210_:
{
if (v___y_2211_ == 0)
{
uint8_t v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2213_ = lean_uint8_dec_eq(v___x_2197_, v___x_2212_);
if (v___x_2213_ == 0)
{
uint8_t v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2215_ = lean_uint8_dec_eq(v___x_2197_, v___x_2214_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2217_ = lean_uint8_dec_eq(v___x_2197_, v___x_2216_);
if (v___x_2217_ == 0)
{
uint8_t v___x_2218_; uint8_t v___x_2219_; 
v___x_2218_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2219_ = lean_uint8_dec_eq(v___x_2197_, v___x_2218_);
if (v___x_2219_ == 0)
{
uint8_t v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2221_ = lean_uint8_dec_eq(v___x_2197_, v___x_2220_);
if (v___x_2221_ == 0)
{
uint8_t v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_2223_ = lean_uint8_dec_eq(v___x_2197_, v___x_2222_);
if (v___x_2223_ == 0)
{
uint8_t v___x_2224_; uint8_t v___x_2225_; 
v___x_2224_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2225_ = lean_uint8_dec_eq(v___x_2197_, v___x_2224_);
if (v___x_2225_ == 0)
{
uint8_t v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2227_ = lean_uint8_dec_eq(v___x_2197_, v___x_2226_);
if (v___x_2227_ == 0)
{
uint8_t v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2229_ = lean_uint8_dec_eq(v___x_2197_, v___x_2228_);
v___y_2205_ = v___x_2229_;
goto v___jp_2204_;
}
else
{
v___y_2205_ = v___x_2227_;
goto v___jp_2204_;
}
}
else
{
v___y_2205_ = v___x_2225_;
goto v___jp_2204_;
}
}
else
{
v___y_2205_ = v___x_2223_;
goto v___jp_2204_;
}
}
else
{
v___y_2205_ = v___x_2221_;
goto v___jp_2204_;
}
}
else
{
v___y_2205_ = v___x_2219_;
goto v___jp_2204_;
}
}
else
{
v___y_2205_ = v___x_2217_;
goto v___jp_2204_;
}
}
else
{
v___y_2205_ = v___x_2215_;
goto v___jp_2204_;
}
}
else
{
v___y_2205_ = v___x_2213_;
goto v___jp_2204_;
}
}
else
{
v___y_2194_ = v___x_2196_;
goto v___jp_2193_;
}
}
v___jp_2230_:
{
if (v___y_2231_ == 0)
{
uint8_t v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2233_ = lean_uint8_dec_eq(v___x_2197_, v___x_2232_);
if (v___x_2233_ == 0)
{
uint8_t v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2235_ = lean_uint8_dec_eq(v___x_2197_, v___x_2234_);
v___y_2211_ = v___x_2235_;
goto v___jp_2210_;
}
else
{
v___y_2211_ = v___x_2233_;
goto v___jp_2210_;
}
}
else
{
v___y_2194_ = v___x_2196_;
goto v___jp_2193_;
}
}
v___jp_2236_:
{
if (v___y_2237_ == 0)
{
uint8_t v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2239_ = lean_uint8_dec_eq(v___x_2197_, v___x_2238_);
if (v___x_2239_ == 0)
{
uint8_t v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2241_ = lean_uint8_dec_eq(v___x_2197_, v___x_2240_);
v___y_2231_ = v___x_2241_;
goto v___jp_2230_;
}
else
{
v___y_2231_ = v___x_2239_;
goto v___jp_2230_;
}
}
else
{
v___y_2194_ = v___x_2196_;
goto v___jp_2193_;
}
}
v___jp_2242_:
{
if (v___y_2243_ == 0)
{
uint8_t v___x_2244_; uint8_t v___x_2245_; 
v___x_2244_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_2245_ = lean_uint8_dec_eq(v___x_2197_, v___x_2244_);
if (v___x_2245_ == 0)
{
uint8_t v___x_2246_; uint8_t v___x_2247_; 
v___x_2246_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_2247_ = lean_uint8_dec_eq(v___x_2197_, v___x_2246_);
v___y_2237_ = v___x_2247_;
goto v___jp_2236_;
}
else
{
v___y_2237_ = v___x_2245_;
goto v___jp_2236_;
}
}
else
{
v___y_2194_ = v___x_2196_;
goto v___jp_2193_;
}
}
v___jp_2248_:
{
if (v___y_2249_ == 0)
{
uint8_t v___x_2250_; uint8_t v___x_2251_; 
v___x_2250_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2251_ = lean_uint8_dec_le(v___x_2250_, v___x_2197_);
if (v___x_2251_ == 0)
{
v___y_2243_ = v___x_2251_;
goto v___jp_2242_;
}
else
{
uint8_t v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2253_ = lean_uint8_dec_le(v___x_2197_, v___x_2252_);
v___y_2243_ = v___x_2253_;
goto v___jp_2242_;
}
}
else
{
v___y_2194_ = v___x_2196_;
goto v___jp_2193_;
}
}
v___jp_2254_:
{
if (v___y_2255_ == 0)
{
uint8_t v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2257_ = lean_uint8_dec_le(v___x_2256_, v___x_2197_);
if (v___x_2257_ == 0)
{
v___y_2249_ = v___x_2257_;
goto v___jp_2248_;
}
else
{
uint8_t v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2259_ = lean_uint8_dec_le(v___x_2197_, v___x_2258_);
v___y_2249_ = v___x_2259_;
goto v___jp_2248_;
}
}
else
{
v___y_2194_ = v___x_2196_;
goto v___jp_2193_;
}
}
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__1));
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___y_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
return v___x_2107_;
}
v___jp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__3));
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___y_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
return v___x_2111_;
}
v___jp_2117_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_segments_2116_);
lean_ctor_set(v___x_2121_, 1, v_totalLength_2119_);
v___x_2122_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0(v_config_2100_, v___x_2121_, v___y_2120_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_res_2123_; lean_object* v_pos_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2133_; 
v_res_2123_ = lean_ctor_get(v___x_2122_, 1);
v_pos_2124_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2133_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_res_2123_);
lean_inc(v_pos_2124_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2133_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_fst_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
v_fst_2128_ = lean_ctor_get(v_res_2123_, 0);
lean_inc(v_fst_2128_);
lean_dec(v_res_2123_);
v___x_2129_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2129_, 0, v_fst_2128_);
lean_ctor_set_uint8(v___x_2129_, sizeof(void*)*1, v_isAbsolute_2118_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 1, v___x_2129_);
v___x_2131_ = v___x_2126_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_pos_2124_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
else
{
lean_object* v_pos_2134_; lean_object* v_err_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_pos_2134_ = lean_ctor_get(v___x_2122_, 0);
v_err_2135_ = lean_ctor_get(v___x_2122_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2122_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_err_2135_);
lean_inc(v_pos_2134_);
lean_dec(v___x_2122_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_pos_2134_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_err_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
v___jp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Std_Http_URI_Parser_parsePath___closed__5));
v___x_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___y_2144_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
return v___x_2146_;
}
v___jp_2147_:
{
if (v_allowEmpty_2102_ == 0)
{
v___y_2105_ = v_pos_2149_;
goto v___jp_2104_;
}
else
{
if (v_res_2150_ == 0)
{
if (v___y_2148_ == 0)
{
v___y_2144_ = v_pos_2149_;
goto v___jp_2143_;
}
else
{
v___y_2105_ = v_pos_2149_;
goto v___jp_2104_;
}
}
else
{
v___y_2144_ = v_pos_2149_;
goto v___jp_2143_;
}
}
}
v___jp_2151_:
{
if (v_forceAbsolute_2101_ == 0)
{
v_isAbsolute_2118_ = v_isAbsolute_2114_;
v_totalLength_2119_ = v___x_2115_;
v___y_2120_ = v_pos_2153_;
goto v___jp_2117_;
}
else
{
lean_object* v_array_2154_; lean_object* v_idx_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
lean_dec_ref(v_config_2100_);
v_array_2154_ = lean_ctor_get(v_pos_2153_, 0);
v_idx_2155_ = lean_ctor_get(v_pos_2153_, 1);
v___x_2156_ = lean_byte_array_size(v_array_2154_);
v___x_2157_ = lean_nat_dec_lt(v_idx_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
v___y_2148_ = v___y_2152_;
v_pos_2149_ = v_pos_2153_;
v_res_2150_ = v_forceAbsolute_2101_;
goto v___jp_2147_;
}
else
{
v___y_2148_ = v___y_2152_;
v_pos_2149_ = v_pos_2153_;
v_res_2150_ = v_isAbsolute_2114_;
goto v___jp_2147_;
}
}
}
v___jp_2158_:
{
lean_object* v_array_2161_; lean_object* v_idx_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v_array_2161_ = lean_ctor_get(v___y_2160_, 0);
v_idx_2162_ = lean_ctor_get(v___y_2160_, 1);
v___x_2163_ = lean_byte_array_size(v_array_2161_);
v___x_2164_ = lean_nat_dec_lt(v_idx_2162_, v___x_2163_);
if (v___x_2164_ == 0)
{
v___y_2152_ = v___y_2159_;
v_pos_2153_ = v___y_2160_;
goto v___jp_2151_;
}
else
{
uint8_t v___x_2165_; uint8_t v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = lean_byte_array_fget(v_array_2161_, v_idx_2162_);
v___x_2166_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2167_ = lean_uint8_dec_eq(v___x_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
v___y_2152_ = v___y_2159_;
v_pos_2153_ = v___y_2160_;
goto v___jp_2151_;
}
else
{
if (v___x_2164_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec_ref(v_config_2100_);
v___x_2168_ = lean_box(0);
v___x_2169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___y_2160_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
return v___x_2169_;
}
else
{
lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2178_; 
lean_inc(v_idx_2162_);
lean_inc_ref(v_array_2161_);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___y_2160_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; lean_object* v_unused_2180_; 
v_unused_2179_ = lean_ctor_get(v___y_2160_, 1);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v___y_2160_, 0);
lean_dec(v_unused_2180_);
v___x_2171_ = v___y_2160_;
v_isShared_2172_ = v_isSharedCheck_2178_;
goto v_resetjp_2170_;
}
else
{
lean_dec(v___y_2160_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2178_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_nat_add(v_idx_2162_, v___x_2173_);
lean_dec(v_idx_2162_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 1, v___x_2174_);
v___x_2176_ = v___x_2171_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_array_2161_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
v_isAbsolute_2118_ = v___x_2164_;
v_totalLength_2119_ = v___x_2173_;
v___y_2120_ = v___x_2176_;
goto v___jp_2117_;
}
}
}
}
}
}
v___jp_2181_:
{
if (v_allowEmpty_2102_ == 0)
{
if (v_res_2184_ == 0)
{
if (v___y_2182_ == 0)
{
lean_dec_ref(v_config_2100_);
v___y_2109_ = v_pos_2183_;
goto v___jp_2108_;
}
else
{
v___y_2159_ = v___y_2182_;
v___y_2160_ = v_pos_2183_;
goto v___jp_2158_;
}
}
else
{
lean_dec_ref(v_config_2100_);
v___y_2109_ = v_pos_2183_;
goto v___jp_2108_;
}
}
else
{
v___y_2159_ = v___y_2182_;
v___y_2160_ = v_pos_2183_;
goto v___jp_2158_;
}
}
v___jp_2185_:
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = lean_byte_array_size(v_array_2187_);
lean_dec_ref(v_array_2187_);
v___x_2191_ = lean_nat_dec_lt(v_idx_2188_, v___x_2190_);
lean_dec(v_idx_2188_);
if (v___x_2191_ == 0)
{
uint8_t v___x_2192_; 
v___x_2192_ = 1;
v___y_2182_ = v_res_2189_;
v_pos_2183_ = v_pos_2186_;
v_res_2184_ = v___x_2192_;
goto v___jp_2181_;
}
else
{
v___y_2182_ = v_res_2189_;
v_pos_2183_ = v_pos_2186_;
v_res_2184_ = v_isAbsolute_2114_;
goto v___jp_2181_;
}
}
v___jp_2193_:
{
if (v___y_2194_ == 0)
{
v_pos_2186_ = v_a_2103_;
v_array_2187_ = v_array_2112_;
v_idx_2188_ = v_idx_2113_;
v_res_2189_ = v_isAbsolute_2114_;
goto v___jp_2185_;
}
else
{
v_pos_2186_ = v_a_2103_;
v_array_2187_ = v_array_2112_;
v_idx_2188_ = v_idx_2113_;
v_res_2189_ = v___y_2194_;
goto v___jp_2185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parsePath___boxed(lean_object* v_config_2264_, lean_object* v_forceAbsolute_2265_, lean_object* v_allowEmpty_2266_, lean_object* v_a_2267_){
_start:
{
uint8_t v_forceAbsolute_boxed_2268_; uint8_t v_allowEmpty_boxed_2269_; lean_object* v_res_2270_; 
v_forceAbsolute_boxed_2268_ = lean_unbox(v_forceAbsolute_2265_);
v_allowEmpty_boxed_2269_ = lean_unbox(v_allowEmpty_2266_);
v_res_2270_ = l_Std_Http_URI_Parser_parsePath(v_config_2264_, v_forceAbsolute_boxed_2268_, v_allowEmpty_boxed_2269_, v_a_2267_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(lean_object* v_s_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0___boxed(lean_object* v_s_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v_s_2273_);
lean_dec_ref(v_s_2273_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(lean_object* v_s_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost_spec__0___closed__0));
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2___boxed(lean_object* v_s_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v_s_2277_);
lean_dec_ref(v_s_2277_);
return v_res_2278_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(uint8_t v_c_2279_){
_start:
{
uint8_t v___y_2281_; uint8_t v___y_2285_; uint8_t v___y_2291_; uint8_t v___y_2297_; uint8_t v___y_2317_; uint8_t v___y_2323_; uint8_t v___y_2329_; uint8_t v___y_2335_; uint8_t v___y_2341_; uint8_t v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_2347_ = lean_uint8_dec_le(v___x_2346_, v_c_2279_);
if (v___x_2347_ == 0)
{
v___y_2341_ = v___x_2347_;
goto v___jp_2340_;
}
else
{
uint8_t v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_2349_ = lean_uint8_dec_le(v_c_2279_, v___x_2348_);
v___y_2341_ = v___x_2349_;
goto v___jp_2340_;
}
v___jp_2280_:
{
if (v___y_2281_ == 0)
{
uint8_t v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__1);
v___x_2283_ = lean_uint8_dec_eq(v_c_2279_, v___x_2282_);
if (v___x_2283_ == 0)
{
return v___y_2281_;
}
else
{
return v___x_2283_;
}
}
else
{
return v___y_2281_;
}
}
v___jp_2284_:
{
if (v___y_2285_ == 0)
{
uint8_t v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_2287_ = lean_uint8_dec_eq(v_c_2279_, v___x_2286_);
if (v___x_2287_ == 0)
{
uint8_t v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2289_ = lean_uint8_dec_eq(v_c_2279_, v___x_2288_);
v___y_2281_ = v___x_2289_;
goto v___jp_2280_;
}
else
{
v___y_2281_ = v___x_2287_;
goto v___jp_2280_;
}
}
else
{
return v___y_2285_;
}
}
v___jp_2290_:
{
if (v___y_2291_ == 0)
{
uint8_t v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_2293_ = lean_uint8_dec_eq(v_c_2279_, v___x_2292_);
if (v___x_2293_ == 0)
{
uint8_t v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__10);
v___x_2295_ = lean_uint8_dec_eq(v_c_2279_, v___x_2294_);
v___y_2285_ = v___x_2295_;
goto v___jp_2284_;
}
else
{
v___y_2285_ = v___x_2293_;
goto v___jp_2284_;
}
}
else
{
return v___y_2291_;
}
}
v___jp_2296_:
{
if (v___y_2297_ == 0)
{
uint8_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__2);
v___x_2299_ = lean_uint8_dec_eq(v_c_2279_, v___x_2298_);
if (v___x_2299_ == 0)
{
uint8_t v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__3);
v___x_2301_ = lean_uint8_dec_eq(v_c_2279_, v___x_2300_);
if (v___x_2301_ == 0)
{
uint8_t v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__4);
v___x_2303_ = lean_uint8_dec_eq(v_c_2279_, v___x_2302_);
if (v___x_2303_ == 0)
{
uint8_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__5);
v___x_2305_ = lean_uint8_dec_eq(v_c_2279_, v___x_2304_);
if (v___x_2305_ == 0)
{
uint8_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2306_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_2307_ = lean_uint8_dec_eq(v_c_2279_, v___x_2306_);
if (v___x_2307_ == 0)
{
uint8_t v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__0);
v___x_2309_ = lean_uint8_dec_eq(v_c_2279_, v___x_2308_);
if (v___x_2309_ == 0)
{
uint8_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__7);
v___x_2311_ = lean_uint8_dec_eq(v_c_2279_, v___x_2310_);
if (v___x_2311_ == 0)
{
uint8_t v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__8);
v___x_2313_ = lean_uint8_dec_eq(v_c_2279_, v___x_2312_);
if (v___x_2313_ == 0)
{
uint8_t v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__9);
v___x_2315_ = lean_uint8_dec_eq(v_c_2279_, v___x_2314_);
v___y_2291_ = v___x_2315_;
goto v___jp_2290_;
}
else
{
v___y_2291_ = v___x_2313_;
goto v___jp_2290_;
}
}
else
{
v___y_2291_ = v___x_2311_;
goto v___jp_2290_;
}
}
else
{
v___y_2291_ = v___x_2309_;
goto v___jp_2290_;
}
}
else
{
v___y_2291_ = v___x_2307_;
goto v___jp_2290_;
}
}
else
{
v___y_2291_ = v___x_2305_;
goto v___jp_2290_;
}
}
else
{
v___y_2291_ = v___x_2303_;
goto v___jp_2290_;
}
}
else
{
v___y_2291_ = v___x_2301_;
goto v___jp_2290_;
}
}
else
{
v___y_2291_ = v___x_2299_;
goto v___jp_2290_;
}
}
else
{
return v___y_2297_;
}
}
v___jp_2316_:
{
if (v___y_2317_ == 0)
{
uint8_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__10);
v___x_2319_ = lean_uint8_dec_eq(v_c_2279_, v___x_2318_);
if (v___x_2319_ == 0)
{
uint8_t v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__11);
v___x_2321_ = lean_uint8_dec_eq(v_c_2279_, v___x_2320_);
v___y_2297_ = v___x_2321_;
goto v___jp_2296_;
}
else
{
v___y_2297_ = v___x_2319_;
goto v___jp_2296_;
}
}
else
{
return v___y_2317_;
}
}
v___jp_2322_:
{
if (v___y_2323_ == 0)
{
uint8_t v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__12);
v___x_2325_ = lean_uint8_dec_eq(v_c_2279_, v___x_2324_);
if (v___x_2325_ == 0)
{
uint8_t v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__13);
v___x_2327_ = lean_uint8_dec_eq(v_c_2279_, v___x_2326_);
v___y_2317_ = v___x_2327_;
goto v___jp_2316_;
}
else
{
v___y_2317_ = v___x_2325_;
goto v___jp_2316_;
}
}
else
{
return v___y_2323_;
}
}
v___jp_2328_:
{
if (v___y_2329_ == 0)
{
uint8_t v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__1);
v___x_2331_ = lean_uint8_dec_eq(v_c_2279_, v___x_2330_);
if (v___x_2331_ == 0)
{
uint8_t v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__2);
v___x_2333_ = lean_uint8_dec_eq(v_c_2279_, v___x_2332_);
v___y_2323_ = v___x_2333_;
goto v___jp_2322_;
}
else
{
v___y_2323_ = v___x_2331_;
goto v___jp_2322_;
}
}
else
{
return v___y_2329_;
}
}
v___jp_2334_:
{
if (v___y_2335_ == 0)
{
uint8_t v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__2);
v___x_2337_ = lean_uint8_dec_le(v___x_2336_, v_c_2279_);
if (v___x_2337_ == 0)
{
v___y_2329_ = v___x_2337_;
goto v___jp_2328_;
}
else
{
uint8_t v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__3);
v___x_2339_ = lean_uint8_dec_le(v_c_2279_, v___x_2338_);
v___y_2329_ = v___x_2339_;
goto v___jp_2328_;
}
}
else
{
return v___y_2335_;
}
}
v___jp_2340_:
{
if (v___y_2341_ == 0)
{
uint8_t v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__0);
v___x_2343_ = lean_uint8_dec_le(v___x_2342_, v_c_2279_);
if (v___x_2343_ == 0)
{
v___y_2335_ = v___x_2343_;
goto v___jp_2334_;
}
else
{
uint8_t v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__0___closed__1);
v___x_2345_ = lean_uint8_dec_le(v_c_2279_, v___x_2344_);
v___y_2335_ = v___x_2345_;
goto v___jp_2334_;
}
}
else
{
return v___y_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0___boxed(lean_object* v_c_2350_){
_start:
{
uint8_t v_c_boxed_2351_; uint8_t v_res_2352_; lean_object* v_r_2353_; 
v_c_boxed_2351_ = lean_unbox(v_c_2350_);
v_res_2352_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___lam__0(v_c_boxed_2351_);
v_r_2353_ = lean_box(v_res_2352_);
return v_r_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(lean_object* v_out_2354_, lean_object* v_a_2355_, lean_object* v_b_2356_){
_start:
{
if (lean_obj_tag(v_a_2355_) == 0)
{
lean_object* v_currPos_2357_; lean_object* v_searcher_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2397_; 
v_currPos_2357_ = lean_ctor_get(v_a_2355_, 0);
v_searcher_2358_ = lean_ctor_get(v_a_2355_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_a_2355_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2360_ = v_a_2355_;
v_isShared_2361_ = v_isSharedCheck_2397_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_searcher_2358_);
lean_inc(v_currPos_2357_);
lean_dec(v_a_2355_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2397_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_str_2362_; lean_object* v_startInclusive_2363_; lean_object* v_endExclusive_2364_; lean_object* v_it_2366_; lean_object* v_startInclusive_2367_; lean_object* v_endExclusive_2368_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v_str_2362_ = lean_ctor_get(v_out_2354_, 0);
v_startInclusive_2363_ = lean_ctor_get(v_out_2354_, 1);
v_endExclusive_2364_ = lean_ctor_get(v_out_2354_, 2);
v___x_2375_ = lean_nat_sub(v_endExclusive_2364_, v_startInclusive_2363_);
v___x_2376_ = lean_nat_dec_eq(v_searcher_2358_, v___x_2375_);
if (v___x_2376_ == 0)
{
uint32_t v___x_2377_; lean_object* v___x_2378_; uint32_t v___x_2379_; uint8_t v___x_2380_; 
lean_dec(v___x_2375_);
v___x_2377_ = 61;
v___x_2378_ = lean_nat_add(v_startInclusive_2363_, v_searcher_2358_);
v___x_2379_ = lean_string_utf8_get_fast(v_str_2362_, v___x_2378_);
v___x_2380_ = lean_uint32_dec_eq(v___x_2379_, v___x_2377_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_dec(v_searcher_2358_);
v___x_2381_ = lean_string_utf8_next_fast(v_str_2362_, v___x_2378_);
lean_dec(v___x_2378_);
v___x_2382_ = lean_nat_sub(v___x_2381_, v_startInclusive_2363_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v___x_2382_);
v___x_2384_ = v___x_2360_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_currPos_2357_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v_a_2355_ = v___x_2384_;
goto _start;
}
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_slice_2390_; lean_object* v_nextIt_2392_; 
v___x_2387_ = lean_string_utf8_next_fast(v_str_2362_, v___x_2378_);
v___x_2388_ = lean_nat_sub(v___x_2387_, v___x_2378_);
lean_dec(v___x_2378_);
v___x_2389_ = lean_nat_add(v_searcher_2358_, v___x_2388_);
lean_dec(v___x_2388_);
v_slice_2390_ = l_String_Slice_subslice_x21(v_out_2354_, v_currPos_2357_, v_searcher_2358_);
lean_inc(v___x_2389_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v___x_2389_);
lean_ctor_set(v___x_2360_, 0, v___x_2389_);
v_nextIt_2392_ = v___x_2360_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2389_);
v_nextIt_2392_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v_startInclusive_2393_; lean_object* v_endExclusive_2394_; 
v_startInclusive_2393_ = lean_ctor_get(v_slice_2390_, 0);
lean_inc(v_startInclusive_2393_);
v_endExclusive_2394_ = lean_ctor_get(v_slice_2390_, 1);
lean_inc(v_endExclusive_2394_);
lean_dec_ref(v_slice_2390_);
v_it_2366_ = v_nextIt_2392_;
v_startInclusive_2367_ = v_startInclusive_2393_;
v_endExclusive_2368_ = v_endExclusive_2394_;
goto v___jp_2365_;
}
}
}
else
{
lean_object* v___x_2396_; 
lean_del_object(v___x_2360_);
lean_dec(v_searcher_2358_);
v___x_2396_ = lean_box(1);
v_it_2366_ = v___x_2396_;
v_startInclusive_2367_ = v_currPos_2357_;
v_endExclusive_2368_ = v___x_2375_;
goto v___jp_2365_;
}
v___jp_2365_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2369_ = lean_nat_add(v_startInclusive_2363_, v_startInclusive_2367_);
lean_dec(v_startInclusive_2367_);
v___x_2370_ = lean_nat_add(v_startInclusive_2363_, v_endExclusive_2368_);
lean_dec(v_endExclusive_2368_);
lean_inc_ref(v_str_2362_);
v___x_2371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2371_, 0, v_str_2362_);
lean_ctor_set(v___x_2371_, 1, v___x_2369_);
lean_ctor_set(v___x_2371_, 2, v___x_2370_);
v___x_2372_ = l_String_Slice_toString(v___x_2371_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = lean_array_push(v_b_2356_, v___x_2372_);
v_a_2355_ = v_it_2366_;
v_b_2356_ = v___x_2373_;
goto _start;
}
}
}
else
{
return v_b_2356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg___boxed(lean_object* v_out_2398_, lean_object* v_a_2399_, lean_object* v_b_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2398_, v_a_2399_, v_b_2400_);
lean_dec_ref(v_out_2398_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(lean_object* v___x_2405_, lean_object* v___x_2406_, lean_object* v___x_2407_, lean_object* v_a_2408_, lean_object* v_b_2409_){
_start:
{
lean_object* v_it_2411_; lean_object* v_startInclusive_2412_; lean_object* v_endExclusive_2413_; 
if (lean_obj_tag(v_a_2408_) == 0)
{
lean_object* v_currPos_2438_; lean_object* v_searcher_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2468_; 
v_currPos_2438_ = lean_ctor_get(v_a_2408_, 0);
v_searcher_2439_ = lean_ctor_get(v_a_2408_, 1);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_a_2408_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2441_ = v_a_2408_;
v_isShared_2442_ = v_isSharedCheck_2468_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_searcher_2439_);
lean_inc(v_currPos_2438_);
lean_dec(v_a_2408_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2468_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v_str_2443_; lean_object* v_startInclusive_2444_; lean_object* v_endExclusive_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v_str_2443_ = lean_ctor_get(v___x_2406_, 0);
v_startInclusive_2444_ = lean_ctor_get(v___x_2406_, 1);
v_endExclusive_2445_ = lean_ctor_get(v___x_2406_, 2);
v___x_2446_ = lean_nat_sub(v_endExclusive_2445_, v_startInclusive_2444_);
v___x_2447_ = lean_nat_dec_eq(v_searcher_2439_, v___x_2446_);
lean_dec(v___x_2446_);
if (v___x_2447_ == 0)
{
uint32_t v___x_2448_; lean_object* v___x_2449_; uint32_t v___x_2450_; uint8_t v___x_2451_; 
v___x_2448_ = 38;
v___x_2449_ = lean_nat_add(v_startInclusive_2444_, v_searcher_2439_);
v___x_2450_ = lean_string_utf8_get_fast(v_str_2443_, v___x_2449_);
v___x_2451_ = lean_uint32_dec_eq(v___x_2450_, v___x_2448_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_dec(v_searcher_2439_);
v___x_2452_ = lean_string_utf8_next_fast(v_str_2443_, v___x_2449_);
lean_dec(v___x_2449_);
v___x_2453_ = lean_nat_sub(v___x_2452_, v_startInclusive_2444_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v___x_2453_);
v___x_2455_ = v___x_2441_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_currPos_2438_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
v_a_2408_ = v___x_2455_;
goto _start;
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v_slice_2461_; lean_object* v_nextIt_2463_; 
v___x_2458_ = lean_string_utf8_next_fast(v_str_2443_, v___x_2449_);
v___x_2459_ = lean_nat_sub(v___x_2458_, v___x_2449_);
lean_dec(v___x_2449_);
v___x_2460_ = lean_nat_add(v_searcher_2439_, v___x_2459_);
lean_dec(v___x_2459_);
v_slice_2461_ = l_String_Slice_subslice_x21(v___x_2406_, v_currPos_2438_, v_searcher_2439_);
lean_inc(v___x_2460_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v___x_2460_);
lean_ctor_set(v___x_2441_, 0, v___x_2460_);
v_nextIt_2463_ = v___x_2441_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v___x_2460_);
v_nextIt_2463_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v_startInclusive_2464_; lean_object* v_endExclusive_2465_; 
v_startInclusive_2464_ = lean_ctor_get(v_slice_2461_, 0);
lean_inc(v_startInclusive_2464_);
v_endExclusive_2465_ = lean_ctor_get(v_slice_2461_, 1);
lean_inc(v_endExclusive_2465_);
lean_dec_ref(v_slice_2461_);
v_it_2411_ = v_nextIt_2463_;
v_startInclusive_2412_ = v_startInclusive_2464_;
v_endExclusive_2413_ = v_endExclusive_2465_;
goto v___jp_2410_;
}
}
}
else
{
lean_object* v___x_2467_; 
lean_del_object(v___x_2441_);
lean_dec(v_searcher_2439_);
v___x_2467_ = lean_box(1);
lean_inc(v___x_2407_);
v_it_2411_ = v___x_2467_;
v_startInclusive_2412_ = v_currPos_2438_;
v_endExclusive_2413_ = v___x_2407_;
goto v___jp_2410_;
}
}
}
else
{
lean_object* v___x_2469_; 
lean_dec(v___x_2407_);
lean_dec_ref(v___x_2405_);
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_b_2409_);
return v___x_2469_;
}
v___jp_2410_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_inc_ref(v___x_2405_);
v___x_2414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2405_);
lean_ctor_set(v___x_2414_, 1, v_startInclusive_2412_);
lean_ctor_set(v___x_2414_, 2, v_endExclusive_2413_);
v___x_2415_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_2414_);
v___x_2416_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2417_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2414_, v___x_2415_, v___x_2416_);
lean_dec_ref(v___x_2414_);
v___x_2418_ = lean_array_to_list(v___x_2417_);
if (lean_obj_tag(v___x_2418_) == 0)
{
v_a_2408_ = v_it_2411_;
goto _start;
}
else
{
lean_object* v_tail_2420_; 
v_tail_2420_ = lean_ctor_get(v___x_2418_, 1);
lean_inc(v_tail_2420_);
if (lean_obj_tag(v_tail_2420_) == 0)
{
lean_object* v_head_2421_; lean_object* v___x_2422_; 
v_head_2421_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_head_2421_);
lean_dec_ref(v___x_2418_);
v___x_2422_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2421_);
lean_dec(v_head_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2423_; 
lean_dec(v_it_2411_);
lean_dec_ref(v_b_2409_);
lean_dec(v___x_2407_);
lean_dec_ref(v___x_2405_);
v___x_2423_ = lean_box(0);
return v___x_2423_;
}
else
{
lean_object* v_val_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_val_2424_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_val_2424_);
lean_dec_ref(v___x_2422_);
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Std_Http_URI_Query_insertEncoded(v_b_2409_, v_val_2424_, v___x_2425_);
v_a_2408_ = v_it_2411_;
v_b_2409_ = v___x_2426_;
goto _start;
}
}
else
{
lean_object* v_head_2428_; lean_object* v___x_2429_; 
v_head_2428_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_head_2428_);
lean_dec_ref(v___x_2418_);
v___x_2429_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2428_);
lean_dec(v_head_2428_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v___x_2430_; 
lean_dec(v_tail_2420_);
lean_dec(v_it_2411_);
lean_dec_ref(v_b_2409_);
lean_dec(v___x_2407_);
lean_dec_ref(v___x_2405_);
v___x_2430_ = lean_box(0);
return v___x_2430_;
}
else
{
lean_object* v_val_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v_val_2431_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_val_2431_);
lean_dec_ref(v___x_2429_);
v___x_2432_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2433_ = l_String_intercalate(v___x_2432_, v_tail_2420_);
v___x_2434_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2433_);
lean_dec_ref(v___x_2433_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v___x_2435_; 
lean_dec(v_val_2431_);
lean_dec(v_it_2411_);
lean_dec_ref(v_b_2409_);
lean_dec(v___x_2407_);
lean_dec_ref(v___x_2405_);
v___x_2435_ = lean_box(0);
return v___x_2435_;
}
else
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Std_Http_URI_Query_insertEncoded(v_b_2409_, v_val_2431_, v___x_2434_);
v_a_2408_ = v_it_2411_;
v_b_2409_ = v___x_2436_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___boxed(lean_object* v___x_2470_, lean_object* v___x_2471_, lean_object* v___x_2472_, lean_object* v_a_2473_, lean_object* v_b_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2470_, v___x_2471_, v___x_2472_, v_a_2473_, v_b_2474_);
lean_dec_ref(v___x_2471_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(lean_object* v___x_2476_, lean_object* v___x_2477_, lean_object* v___x_2478_, lean_object* v_a_2479_, lean_object* v_b_2480_){
_start:
{
lean_object* v_it_2482_; lean_object* v_startInclusive_2483_; lean_object* v_endExclusive_2484_; 
if (lean_obj_tag(v_a_2479_) == 0)
{
lean_object* v_currPos_2509_; lean_object* v_searcher_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2539_; 
v_currPos_2509_ = lean_ctor_get(v_a_2479_, 0);
v_searcher_2510_ = lean_ctor_get(v_a_2479_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_a_2479_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2512_ = v_a_2479_;
v_isShared_2513_ = v_isSharedCheck_2539_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_searcher_2510_);
lean_inc(v_currPos_2509_);
lean_dec(v_a_2479_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2539_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v_str_2514_; lean_object* v_startInclusive_2515_; lean_object* v_endExclusive_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v_str_2514_ = lean_ctor_get(v___x_2477_, 0);
v_startInclusive_2515_ = lean_ctor_get(v___x_2477_, 1);
v_endExclusive_2516_ = lean_ctor_get(v___x_2477_, 2);
v___x_2517_ = lean_nat_sub(v_endExclusive_2516_, v_startInclusive_2515_);
v___x_2518_ = lean_nat_dec_eq(v_searcher_2510_, v___x_2517_);
lean_dec(v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; uint32_t v___x_2520_; uint32_t v___x_2521_; uint8_t v___x_2522_; 
v___x_2519_ = lean_nat_add(v_startInclusive_2515_, v_searcher_2510_);
v___x_2520_ = lean_string_utf8_get_fast(v_str_2514_, v___x_2519_);
v___x_2521_ = 38;
v___x_2522_ = lean_uint32_dec_eq(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; 
lean_dec(v_searcher_2510_);
v___x_2523_ = lean_string_utf8_next_fast(v_str_2514_, v___x_2519_);
lean_dec(v___x_2519_);
v___x_2524_ = lean_nat_sub(v___x_2523_, v_startInclusive_2515_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v___x_2524_);
v___x_2526_ = v___x_2512_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_currPos_2509_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2476_, v___x_2477_, v___x_2478_, v___x_2526_, v_b_2480_);
return v___x_2527_;
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_slice_2532_; lean_object* v_nextIt_2534_; 
v___x_2529_ = lean_string_utf8_next_fast(v_str_2514_, v___x_2519_);
v___x_2530_ = lean_nat_sub(v___x_2529_, v___x_2519_);
lean_dec(v___x_2519_);
v___x_2531_ = lean_nat_add(v_searcher_2510_, v___x_2530_);
lean_dec(v___x_2530_);
v_slice_2532_ = l_String_Slice_subslice_x21(v___x_2477_, v_currPos_2509_, v_searcher_2510_);
lean_inc(v___x_2531_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v___x_2531_);
lean_ctor_set(v___x_2512_, 0, v___x_2531_);
v_nextIt_2534_ = v___x_2512_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___x_2531_);
v_nextIt_2534_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v_startInclusive_2535_; lean_object* v_endExclusive_2536_; 
v_startInclusive_2535_ = lean_ctor_get(v_slice_2532_, 0);
lean_inc(v_startInclusive_2535_);
v_endExclusive_2536_ = lean_ctor_get(v_slice_2532_, 1);
lean_inc(v_endExclusive_2536_);
lean_dec_ref(v_slice_2532_);
v_it_2482_ = v_nextIt_2534_;
v_startInclusive_2483_ = v_startInclusive_2535_;
v_endExclusive_2484_ = v_endExclusive_2536_;
goto v___jp_2481_;
}
}
}
else
{
lean_object* v___x_2538_; 
lean_del_object(v___x_2512_);
lean_dec(v_searcher_2510_);
v___x_2538_ = lean_box(1);
lean_inc(v___x_2478_);
v_it_2482_ = v___x_2538_;
v_startInclusive_2483_ = v_currPos_2509_;
v_endExclusive_2484_ = v___x_2478_;
goto v___jp_2481_;
}
}
}
else
{
lean_object* v___x_2540_; 
lean_dec(v___x_2478_);
lean_dec_ref(v___x_2476_);
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_b_2480_);
return v___x_2540_;
}
v___jp_2481_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
lean_inc_ref(v___x_2476_);
v___x_2485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2476_);
lean_ctor_set(v___x_2485_, 1, v_startInclusive_2483_);
lean_ctor_set(v___x_2485_, 2, v_endExclusive_2484_);
v___x_2486_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__2(v___x_2485_);
v___x_2487_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__0));
v___x_2488_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v___x_2485_, v___x_2486_, v___x_2487_);
lean_dec_ref(v___x_2485_);
v___x_2489_ = lean_array_to_list(v___x_2488_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2490_; 
v___x_2490_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2476_, v___x_2477_, v___x_2478_, v_it_2482_, v_b_2480_);
return v___x_2490_;
}
else
{
lean_object* v_tail_2491_; 
v_tail_2491_ = lean_ctor_get(v___x_2489_, 1);
lean_inc(v_tail_2491_);
if (lean_obj_tag(v_tail_2491_) == 0)
{
lean_object* v_head_2492_; lean_object* v___x_2493_; 
v_head_2492_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_head_2492_);
lean_dec_ref(v___x_2489_);
v___x_2493_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2492_);
lean_dec(v_head_2492_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v___x_2494_; 
lean_dec(v_it_2482_);
lean_dec_ref(v_b_2480_);
lean_dec(v___x_2478_);
lean_dec_ref(v___x_2476_);
v___x_2494_ = lean_box(0);
return v___x_2494_;
}
else
{
lean_object* v_val_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v_val_2495_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_val_2495_);
lean_dec_ref(v___x_2493_);
v___x_2496_ = lean_box(0);
v___x_2497_ = l_Std_Http_URI_Query_insertEncoded(v_b_2480_, v_val_2495_, v___x_2496_);
v___x_2498_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2476_, v___x_2477_, v___x_2478_, v_it_2482_, v___x_2497_);
return v___x_2498_;
}
}
else
{
lean_object* v_head_2499_; lean_object* v___x_2500_; 
v_head_2499_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_head_2499_);
lean_dec_ref(v___x_2489_);
v___x_2500_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v_head_2499_);
lean_dec(v_head_2499_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v___x_2501_; 
lean_dec(v_tail_2491_);
lean_dec(v_it_2482_);
lean_dec_ref(v_b_2480_);
lean_dec(v___x_2478_);
lean_dec_ref(v___x_2476_);
v___x_2501_ = lean_box(0);
return v___x_2501_;
}
else
{
lean_object* v_val_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_val_2502_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_val_2502_);
lean_dec_ref(v___x_2500_);
v___x_2503_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg___closed__1));
v___x_2504_ = l_String_intercalate(v___x_2503_, v_tail_2491_);
v___x_2505_ = l_Std_Http_URI_EncodedQueryParam_fromString_x3f(v___x_2504_);
lean_dec_ref(v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2506_; 
lean_dec(v_val_2502_);
lean_dec(v_it_2482_);
lean_dec_ref(v_b_2480_);
lean_dec(v___x_2478_);
lean_dec_ref(v___x_2476_);
v___x_2506_ = lean_box(0);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = l_Std_Http_URI_Query_insertEncoded(v_b_2480_, v_val_2502_, v___x_2505_);
v___x_2508_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2476_, v___x_2477_, v___x_2478_, v_it_2482_, v___x_2507_);
return v___x_2508_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg___boxed(lean_object* v___x_2541_, lean_object* v___x_2542_, lean_object* v___x_2543_, lean_object* v_a_2544_, lean_object* v_b_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2541_, v___x_2542_, v___x_2543_, v_a_2544_, v_b_2545_);
lean_dec_ref(v___x_2542_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(lean_object* v___x_2547_, lean_object* v___x_2548_, lean_object* v_a_2549_, lean_object* v_b_2550_){
_start:
{
lean_object* v_it_2552_; 
if (lean_obj_tag(v_a_2549_) == 0)
{
lean_object* v_currPos_2556_; lean_object* v_searcher_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2583_; 
v_currPos_2556_ = lean_ctor_get(v_a_2549_, 0);
v_searcher_2557_ = lean_ctor_get(v_a_2549_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_a_2549_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2559_ = v_a_2549_;
v_isShared_2560_ = v_isSharedCheck_2583_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_searcher_2557_);
lean_inc(v_currPos_2556_);
lean_dec(v_a_2549_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2583_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_str_2561_; lean_object* v_startInclusive_2562_; lean_object* v_endExclusive_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_str_2561_ = lean_ctor_get(v___x_2547_, 0);
v_startInclusive_2562_ = lean_ctor_get(v___x_2547_, 1);
v_endExclusive_2563_ = lean_ctor_get(v___x_2547_, 2);
v___x_2564_ = lean_nat_sub(v_endExclusive_2563_, v_startInclusive_2562_);
v___x_2565_ = lean_nat_dec_eq(v_searcher_2557_, v___x_2564_);
lean_dec(v___x_2564_);
if (v___x_2565_ == 0)
{
uint32_t v___x_2566_; lean_object* v___x_2567_; uint32_t v___x_2568_; uint8_t v___x_2569_; 
v___x_2566_ = 38;
v___x_2567_ = lean_nat_add(v_startInclusive_2562_, v_searcher_2557_);
v___x_2568_ = lean_string_utf8_get_fast(v_str_2561_, v___x_2567_);
v___x_2569_ = lean_uint32_dec_eq(v___x_2568_, v___x_2566_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
lean_dec(v_searcher_2557_);
v___x_2570_ = lean_string_utf8_next_fast(v_str_2561_, v___x_2567_);
lean_dec(v___x_2567_);
v___x_2571_ = lean_nat_sub(v___x_2570_, v_startInclusive_2562_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v___x_2571_);
v___x_2573_ = v___x_2559_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_currPos_2556_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
v_a_2549_ = v___x_2573_;
goto _start;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_nextIt_2580_; 
lean_dec(v_currPos_2556_);
v___x_2576_ = lean_string_utf8_next_fast(v_str_2561_, v___x_2567_);
v___x_2577_ = lean_nat_sub(v___x_2576_, v___x_2567_);
lean_dec(v___x_2567_);
v___x_2578_ = lean_nat_add(v_searcher_2557_, v___x_2577_);
lean_dec(v___x_2577_);
lean_dec(v_searcher_2557_);
lean_inc(v___x_2578_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v___x_2578_);
lean_ctor_set(v___x_2559_, 0, v___x_2578_);
v_nextIt_2580_ = v___x_2559_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___x_2578_);
v_nextIt_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
v_it_2552_ = v_nextIt_2580_;
goto v___jp_2551_;
}
}
}
else
{
lean_object* v___x_2582_; 
lean_del_object(v___x_2559_);
lean_dec(v_searcher_2557_);
lean_dec(v_currPos_2556_);
v___x_2582_ = lean_box(1);
v_it_2552_ = v___x_2582_;
goto v___jp_2551_;
}
}
}
else
{
return v_b_2550_;
}
v___jp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_unsigned_to_nat(1u);
v___x_2554_ = lean_nat_add(v_b_2550_, v___x_2553_);
lean_dec(v_b_2550_);
v_a_2549_ = v_it_2552_;
v_b_2550_ = v___x_2554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg___boxed(lean_object* v___x_2584_, lean_object* v___x_2585_, lean_object* v_a_2586_, lean_object* v_b_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2584_, v___x_2585_, v_a_2586_, v_b_2587_);
lean_dec(v___x_2585_);
lean_dec_ref(v___x_2584_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(lean_object* v___x_2589_, lean_object* v___x_2590_, lean_object* v___x_2591_, lean_object* v_a_2592_, lean_object* v_b_2593_){
_start:
{
lean_object* v_it_2595_; 
if (lean_obj_tag(v_a_2592_) == 0)
{
lean_object* v_currPos_2599_; lean_object* v_searcher_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2626_; 
v_currPos_2599_ = lean_ctor_get(v_a_2592_, 0);
v_searcher_2600_ = lean_ctor_get(v_a_2592_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_a_2592_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2602_ = v_a_2592_;
v_isShared_2603_ = v_isSharedCheck_2626_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_searcher_2600_);
lean_inc(v_currPos_2599_);
lean_dec(v_a_2592_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2626_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_str_2604_; lean_object* v_startInclusive_2605_; lean_object* v_endExclusive_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_str_2604_ = lean_ctor_get(v___x_2590_, 0);
v_startInclusive_2605_ = lean_ctor_get(v___x_2590_, 1);
v_endExclusive_2606_ = lean_ctor_get(v___x_2590_, 2);
v___x_2607_ = lean_nat_sub(v_endExclusive_2606_, v_startInclusive_2605_);
v___x_2608_ = lean_nat_dec_eq(v_searcher_2600_, v___x_2607_);
lean_dec(v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; uint32_t v___x_2610_; uint32_t v___x_2611_; uint8_t v___x_2612_; 
v___x_2609_ = lean_nat_add(v_startInclusive_2605_, v_searcher_2600_);
v___x_2610_ = lean_string_utf8_get_fast(v_str_2604_, v___x_2609_);
v___x_2611_ = 38;
v___x_2612_ = lean_uint32_dec_eq(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_searcher_2600_);
v___x_2613_ = lean_string_utf8_next_fast(v_str_2604_, v___x_2609_);
lean_dec(v___x_2609_);
v___x_2614_ = lean_nat_sub(v___x_2613_, v_startInclusive_2605_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v___x_2614_);
v___x_2616_ = v___x_2602_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_currPos_2599_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2590_, v___x_2591_, v___x_2616_, v_b_2593_);
return v___x_2617_;
}
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v_nextIt_2623_; 
lean_dec(v_currPos_2599_);
v___x_2619_ = lean_string_utf8_next_fast(v_str_2604_, v___x_2609_);
v___x_2620_ = lean_nat_sub(v___x_2619_, v___x_2609_);
lean_dec(v___x_2609_);
v___x_2621_ = lean_nat_add(v_searcher_2600_, v___x_2620_);
lean_dec(v___x_2620_);
lean_dec(v_searcher_2600_);
lean_inc(v___x_2621_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v___x_2621_);
lean_ctor_set(v___x_2602_, 0, v___x_2621_);
v_nextIt_2623_ = v___x_2602_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2621_);
v_nextIt_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
v_it_2595_ = v_nextIt_2623_;
goto v___jp_2594_;
}
}
}
else
{
lean_object* v___x_2625_; 
lean_del_object(v___x_2602_);
lean_dec(v_searcher_2600_);
lean_dec(v_currPos_2599_);
v___x_2625_ = lean_box(1);
v_it_2595_ = v___x_2625_;
goto v___jp_2594_;
}
}
}
else
{
return v_b_2593_;
}
v___jp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_unsigned_to_nat(1u);
v___x_2597_ = lean_nat_add(v_b_2593_, v___x_2596_);
lean_dec(v_b_2593_);
v___x_2598_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2590_, v___x_2591_, v_it_2595_, v___x_2597_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg___boxed(lean_object* v___x_2627_, lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v_a_2630_, lean_object* v_b_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2627_, v___x_2628_, v___x_2629_, v_a_2630_, v_b_2631_);
lean_dec(v___x_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___x_2627_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(lean_object* v_config_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_maxQueryLength_2640_; lean_object* v_maxQueryParams_2641_; lean_object* v___f_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v_fst_2645_; lean_object* v_snd_2646_; lean_object* v_array_2647_; lean_object* v_idx_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2698_; 
v_maxQueryLength_2640_ = lean_ctor_get(v_config_2638_, 4);
lean_inc(v_maxQueryLength_2640_);
v_maxQueryParams_2641_ = lean_ctor_get(v_config_2638_, 8);
lean_inc(v_maxQueryParams_2641_);
lean_dec_ref(v_config_2638_);
v___f_2642_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2643_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2639_);
v___x_2644_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_2642_, v_maxQueryLength_2640_, v___x_2643_, v_a_2639_);
lean_dec(v_maxQueryLength_2640_);
v_fst_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_fst_2645_);
v_snd_2646_ = lean_ctor_get(v___x_2644_, 1);
lean_inc(v_snd_2646_);
lean_dec_ref(v___x_2644_);
v_array_2647_ = lean_ctor_get(v_a_2639_, 0);
v_idx_2648_ = lean_ctor_get(v_a_2639_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_a_2639_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2650_ = v_a_2639_;
v_isShared_2651_ = v_isSharedCheck_2698_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_idx_2648_);
lean_inc(v_array_2647_);
lean_dec(v_a_2639_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2698_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v_lower_2653_; lean_object* v_upper_2654_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___y_2695_; uint8_t v___x_2697_; 
v___x_2692_ = lean_nat_add(v_idx_2648_, v_fst_2645_);
lean_dec(v_fst_2645_);
v___x_2693_ = lean_byte_array_size(v_array_2647_);
v___x_2697_ = lean_nat_dec_le(v_idx_2648_, v___x_2643_);
if (v___x_2697_ == 0)
{
v___y_2695_ = v_idx_2648_;
goto v___jp_2694_;
}
else
{
lean_dec(v_idx_2648_);
v___y_2695_ = v___x_2643_;
goto v___jp_2694_;
}
v___jp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2655_ = l_ByteArray_toByteSlice(v_array_2647_, v_lower_2653_, v_upper_2654_);
v___x_2656_ = l_ByteSlice_toByteArray(v___x_2655_);
v___x_2657_ = lean_string_validate_utf8(v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
lean_dec_ref(v___x_2656_);
lean_dec(v_maxQueryParams_2641_);
v___x_2658_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 1);
lean_ctor_set(v___x_2650_, 1, v___x_2658_);
lean_ctor_set(v___x_2650_, 0, v_snd_2646_);
v___x_2660_ = v___x_2650_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_snd_2646_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2662_ = lean_string_from_utf8_unchecked(v___x_2656_);
v___x_2663_ = lean_string_utf8_byte_size(v___x_2662_);
v___x_2664_ = lean_nat_dec_eq(v___x_2663_, v___x_2643_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
lean_inc_ref(v___x_2662_);
v___x_2665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2662_);
lean_ctor_set(v___x_2665_, 1, v___x_2643_);
lean_ctor_set(v___x_2665_, 2, v___x_2663_);
v___x_2666_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__0(v___x_2665_);
lean_inc(v___x_2666_);
v___x_2667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2662_, v___x_2665_, v___x_2663_, v___x_2666_, v___x_2643_);
v___x_2668_ = lean_nat_dec_lt(v_maxQueryParams_2641_, v___x_2667_);
lean_dec(v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec(v_maxQueryParams_2641_);
v___x_2669_ = l_Std_Http_URI_Query_empty;
v___x_2670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2662_, v___x_2665_, v___x_2663_, v___x_2666_, v___x_2669_);
lean_dec_ref(v___x_2665_);
if (lean_obj_tag(v___x_2670_) == 1)
{
lean_object* v_val_2671_; lean_object* v___x_2673_; 
v_val_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_val_2671_);
lean_dec_ref(v___x_2670_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v_val_2671_);
lean_ctor_set(v___x_2650_, 0, v_snd_2646_);
v___x_2673_ = v___x_2650_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_snd_2646_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_val_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
else
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
lean_dec(v___x_2670_);
v___x_2675_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__2));
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 1);
lean_ctor_set(v___x_2650_, 1, v___x_2675_);
lean_ctor_set(v___x_2650_, 0, v_snd_2646_);
v___x_2677_ = v___x_2650_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_snd_2646_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec(v___x_2666_);
lean_dec_ref(v___x_2665_);
lean_dec_ref(v___x_2662_);
v___x_2679_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__3));
v___x_2680_ = l_Nat_reprFast(v_maxQueryParams_2641_);
v___x_2681_ = lean_string_append(v___x_2679_, v___x_2680_);
lean_dec_ref(v___x_2680_);
v___x_2682_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Http_URI_Parser_parsePath_spec__0_spec__0___closed__3));
v___x_2683_ = lean_string_append(v___x_2681_, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 1);
lean_ctor_set(v___x_2650_, 1, v___x_2684_);
lean_ctor_set(v___x_2650_, 0, v_snd_2646_);
v___x_2686_ = v___x_2650_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_snd_2646_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_dec_ref(v___x_2662_);
lean_dec(v_maxQueryParams_2641_);
v___x_2688_ = l_Std_Http_URI_Query_empty;
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v___x_2688_);
lean_ctor_set(v___x_2650_, 0, v_snd_2646_);
v___x_2690_ = v___x_2650_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_snd_2646_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
v___jp_2694_:
{
uint8_t v___x_2696_; 
v___x_2696_ = lean_nat_dec_le(v___x_2692_, v___x_2693_);
if (v___x_2696_ == 0)
{
lean_dec(v___x_2692_);
v_lower_2653_ = v___y_2695_;
v_upper_2654_ = v___x_2693_;
goto v___jp_2652_;
}
else
{
v_lower_2653_ = v___y_2695_;
v_upper_2654_ = v___x_2692_;
goto v___jp_2652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(lean_object* v___x_2699_, lean_object* v___x_2700_, lean_object* v___x_2701_, lean_object* v_inst_2702_, lean_object* v_R_2703_, lean_object* v_a_2704_, lean_object* v_b_2705_, lean_object* v_c_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___redArg(v___x_2699_, v___x_2700_, v___x_2701_, v_a_2704_, v_b_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1___boxed(lean_object* v___x_2708_, lean_object* v___x_2709_, lean_object* v___x_2710_, lean_object* v_inst_2711_, lean_object* v_R_2712_, lean_object* v_a_2713_, lean_object* v_b_2714_, lean_object* v_c_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1(v___x_2708_, v___x_2709_, v___x_2710_, v_inst_2711_, v_R_2712_, v_a_2713_, v_b_2714_, v_c_2715_);
lean_dec(v___x_2710_);
lean_dec_ref(v___x_2709_);
lean_dec_ref(v___x_2708_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(lean_object* v_out_2717_, lean_object* v_inst_2718_, lean_object* v_R_2719_, lean_object* v_a_2720_, lean_object* v_b_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___redArg(v_out_2717_, v_a_2720_, v_b_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3___boxed(lean_object* v_out_2723_, lean_object* v_inst_2724_, lean_object* v_R_2725_, lean_object* v_a_2726_, lean_object* v_b_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__3(v_out_2723_, v_inst_2724_, v_R_2725_, v_a_2726_, v_b_2727_);
lean_dec_ref(v_out_2723_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(lean_object* v___x_2729_, lean_object* v___x_2730_, lean_object* v___x_2731_, lean_object* v_inst_2732_, lean_object* v_R_2733_, lean_object* v_a_2734_, lean_object* v_b_2735_, lean_object* v_c_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___redArg(v___x_2729_, v___x_2730_, v___x_2731_, v_a_2734_, v_b_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4___boxed(lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v___x_2740_, lean_object* v_inst_2741_, lean_object* v_R_2742_, lean_object* v_a_2743_, lean_object* v_b_2744_, lean_object* v_c_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4(v___x_2738_, v___x_2739_, v___x_2740_, v_inst_2741_, v_R_2742_, v_a_2743_, v_b_2744_, v_c_2745_);
lean_dec_ref(v___x_2739_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(lean_object* v___x_2747_, lean_object* v___x_2748_, lean_object* v___x_2749_, lean_object* v_inst_2750_, lean_object* v_R_2751_, lean_object* v_a_2752_, lean_object* v_b_2753_, lean_object* v_c_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___redArg(v___x_2748_, v___x_2749_, v_a_2752_, v_b_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1___boxed(lean_object* v___x_2756_, lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v_inst_2759_, lean_object* v_R_2760_, lean_object* v_a_2761_, lean_object* v_b_2762_, lean_object* v_c_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__1_spec__1(v___x_2756_, v___x_2757_, v___x_2758_, v_inst_2759_, v_R_2760_, v_a_2761_, v_b_2762_, v_c_2763_);
lean_dec(v___x_2758_);
lean_dec_ref(v___x_2757_);
lean_dec_ref(v___x_2756_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(lean_object* v___x_2765_, lean_object* v___x_2766_, lean_object* v___x_2767_, lean_object* v_inst_2768_, lean_object* v_R_2769_, lean_object* v_a_2770_, lean_object* v_b_2771_, lean_object* v_c_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___redArg(v___x_2765_, v___x_2766_, v___x_2767_, v_a_2770_, v_b_2771_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5___boxed(lean_object* v___x_2774_, lean_object* v___x_2775_, lean_object* v___x_2776_, lean_object* v_inst_2777_, lean_object* v_R_2778_, lean_object* v_a_2779_, lean_object* v_b_2780_, lean_object* v_c_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery_spec__4_spec__5(v___x_2774_, v___x_2775_, v___x_2776_, v_inst_2777_, v_R_2778_, v_a_2779_, v_b_2780_, v_c_2781_);
lean_dec_ref(v___x_2775_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(lean_object* v_config_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_maxFragmentLength_2788_; lean_object* v___f_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v_fst_2792_; lean_object* v_snd_2793_; lean_object* v_array_2794_; lean_object* v_idx_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2819_; 
v_maxFragmentLength_2788_ = lean_ctor_get(v_config_2786_, 5);
v___f_2789_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery___closed__0));
v___x_2790_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_a_2787_);
v___x_2791_ = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_takeWhileUpTo_findEnd(v___f_2789_, v_maxFragmentLength_2788_, v___x_2790_, v_a_2787_);
v_fst_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_fst_2792_);
v_snd_2793_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_snd_2793_);
lean_dec_ref(v___x_2791_);
v_array_2794_ = lean_ctor_get(v_a_2787_, 0);
v_idx_2795_ = lean_ctor_get(v_a_2787_, 1);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_a_2787_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2797_ = v_a_2787_;
v_isShared_2798_ = v_isSharedCheck_2819_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_idx_2795_);
lean_inc(v_array_2794_);
lean_dec(v_a_2787_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2819_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v_lower_2800_; lean_object* v_upper_2801_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___y_2816_; uint8_t v___x_2818_; 
v___x_2813_ = lean_nat_add(v_idx_2795_, v_fst_2792_);
lean_dec(v_fst_2792_);
v___x_2814_ = lean_byte_array_size(v_array_2794_);
v___x_2818_ = lean_nat_dec_le(v_idx_2795_, v___x_2790_);
if (v___x_2818_ == 0)
{
v___y_2816_ = v_idx_2795_;
goto v___jp_2815_;
}
else
{
lean_dec(v_idx_2795_);
v___y_2816_ = v___x_2790_;
goto v___jp_2815_;
}
v___jp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = l_ByteArray_toByteSlice(v_array_2794_, v_lower_2800_, v_upper_2801_);
v___x_2803_ = l_ByteSlice_toByteArray(v___x_2802_);
v___x_2804_ = l_Std_Http_URI_EncodedFragment_ofByteArray_x3f(v___x_2803_);
if (lean_obj_tag(v___x_2804_) == 1)
{
lean_object* v_val_2805_; lean_object* v___x_2807_; 
v_val_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_val_2805_);
lean_dec_ref(v___x_2804_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v_val_2805_);
lean_ctor_set(v___x_2797_, 0, v_snd_2793_);
v___x_2807_ = v___x_2797_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_snd_2793_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_val_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
else
{
lean_object* v___x_2809_; lean_object* v___x_2811_; 
lean_dec(v___x_2804_);
v___x_2809_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___closed__1));
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 1);
lean_ctor_set(v___x_2797_, 1, v___x_2809_);
lean_ctor_set(v___x_2797_, 0, v_snd_2793_);
v___x_2811_ = v___x_2797_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_snd_2793_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
v___jp_2815_:
{
uint8_t v___x_2817_; 
v___x_2817_ = lean_nat_dec_le(v___x_2813_, v___x_2814_);
if (v___x_2817_ == 0)
{
lean_dec(v___x_2813_);
v_lower_2800_ = v___y_2816_;
v_upper_2801_ = v___x_2814_;
goto v___jp_2799_;
}
else
{
v_lower_2800_ = v___y_2816_;
v_upper_2801_ = v___x_2813_;
goto v___jp_2799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment___boxed(lean_object* v_config_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2820_, v_a_2821_);
lean_dec_ref(v_config_2820_);
return v_res_2822_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__0));
v___x_2825_ = lean_string_to_utf8(v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(lean_object* v_config_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_pos_2829_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart___closed__1);
lean_inc_ref(v_a_2827_);
v___x_2865_ = l_Std_Internal_Parsec_ByteArray_skipBytes(v___x_2864_, v_a_2827_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_pos_2866_; 
lean_dec_ref(v_a_2827_);
v_pos_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_pos_2866_);
lean_dec_ref(v___x_2865_);
v_pos_2829_ = v_pos_2866_;
goto v___jp_2828_;
}
else
{
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_pos_2867_; 
lean_dec_ref(v_a_2827_);
v_pos_2867_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_pos_2867_);
lean_dec_ref(v___x_2865_);
v_pos_2829_ = v_pos_2867_;
goto v___jp_2828_;
}
else
{
lean_object* v_err_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2899_; 
v_err_2868_ = lean_ctor_get(v___x_2865_, 1);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v___x_2865_, 0);
lean_dec(v_unused_2900_);
v___x_2870_ = v___x_2865_;
v_isShared_2871_ = v_isSharedCheck_2899_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_err_2868_);
lean_dec(v___x_2865_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2899_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_idx_2872_; uint8_t v___x_2873_; 
v_idx_2872_ = lean_ctor_get(v_a_2827_, 1);
v___x_2873_ = lean_nat_dec_eq(v_idx_2872_, v_idx_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2875_; 
lean_dec_ref(v_config_2826_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v_a_2827_);
v___x_2875_ = v___x_2870_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2827_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_err_2868_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
else
{
uint8_t v___x_2877_; lean_object* v___x_2878_; 
lean_del_object(v___x_2870_);
lean_dec(v_err_2868_);
v___x_2877_ = 0;
v___x_2878_ = l_Std_Http_URI_Parser_parsePath(v_config_2826_, v___x_2877_, v___x_2873_, v_a_2827_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_pos_2879_; lean_object* v_res_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2889_; 
v_pos_2879_ = lean_ctor_get(v___x_2878_, 0);
v_res_2880_ = lean_ctor_get(v___x_2878_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2882_ = v___x_2878_;
v_isShared_2883_ = v_isSharedCheck_2889_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_res_2880_);
lean_inc(v_pos_2879_);
lean_dec(v___x_2878_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2889_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2884_ = lean_box(0);
v___x_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v_res_2880_);
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 1, v___x_2885_);
v___x_2887_ = v___x_2882_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_pos_2879_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
else
{
lean_object* v_pos_2890_; lean_object* v_err_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_pos_2890_ = lean_ctor_get(v___x_2878_, 0);
v_err_2891_ = lean_ctor_get(v___x_2878_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2878_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_err_2891_);
lean_inc(v_pos_2890_);
lean_dec(v___x_2878_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_pos_2890_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_err_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
}
v___jp_2828_:
{
lean_object* v___x_2830_; 
v___x_2830_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority(v_config_2826_, v_pos_2829_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_pos_2831_; lean_object* v_res_2832_; uint8_t v___x_2833_; lean_object* v___x_2834_; 
v_pos_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_pos_2831_);
v_res_2832_ = lean_ctor_get(v___x_2830_, 1);
lean_inc(v_res_2832_);
lean_dec_ref(v___x_2830_);
v___x_2833_ = 1;
v___x_2834_ = l_Std_Http_URI_Parser_parsePath(v_config_2826_, v___x_2833_, v___x_2833_, v_pos_2831_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_pos_2835_; lean_object* v_res_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2845_; 
v_pos_2835_ = lean_ctor_get(v___x_2834_, 0);
v_res_2836_ = lean_ctor_get(v___x_2834_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2838_ = v___x_2834_;
v_isShared_2839_ = v_isSharedCheck_2845_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_res_2836_);
lean_inc(v_pos_2835_);
lean_dec(v___x_2834_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2845_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2840_, 0, v_res_2832_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v_res_2836_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v___x_2841_);
v___x_2843_ = v___x_2838_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_pos_2835_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_pos_2846_; lean_object* v_err_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_res_2832_);
v_pos_2846_ = lean_ctor_get(v___x_2834_, 0);
v_err_2847_ = lean_ctor_get(v___x_2834_, 1);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2834_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_err_2847_);
lean_inc(v_pos_2846_);
lean_dec(v___x_2834_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_pos_2846_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_err_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_pos_2855_; lean_object* v_err_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec_ref(v_config_2826_);
v_pos_2855_ = lean_ctor_get(v___x_2830_, 0);
v_err_2856_ = lean_ctor_get(v___x_2830_, 1);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2830_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_err_2856_);
lean_inc(v_pos_2855_);
lean_dec(v___x_2830_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_pos_2855_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_err_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__0(void){
_start:
{
uint8_t v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v___x_2902_ = lean_uint8_to_nat(v___x_2901_);
return v___x_2902_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__1(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__0, &l_Std_Http_URI_Parser_parseURI___closed__0_once, _init_l_Std_Http_URI_Parser_parseURI___closed__0);
v___x_2904_ = l_Nat_reprFast(v___x_2903_);
return v___x_2904_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__2(void){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2905_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__1, &l_Std_Http_URI_Parser_parseURI___closed__1_once, _init_l_Std_Http_URI_Parser_parseURI___closed__1);
v___x_2906_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2907_ = lean_string_append(v___x_2906_, v___x_2905_);
return v___x_2907_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__3(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2909_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__2, &l_Std_Http_URI_Parser_parseURI___closed__2_once, _init_l_Std_Http_URI_Parser_parseURI___closed__2);
v___x_2910_ = lean_string_append(v___x_2909_, v___x_2908_);
return v___x_2910_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__4(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__3, &l_Std_Http_URI_Parser_parseURI___closed__3_once, _init_l_Std_Http_URI_Parser_parseURI___closed__3);
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__7(void){
_start:
{
uint8_t v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v___x_2917_ = lean_uint8_to_nat(v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__8(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__7, &l_Std_Http_URI_Parser_parseURI___closed__7_once, _init_l_Std_Http_URI_Parser_parseURI___closed__7);
v___x_2919_ = l_Nat_reprFast(v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__9(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__8, &l_Std_Http_URI_Parser_parseURI___closed__8_once, _init_l_Std_Http_URI_Parser_parseURI___closed__8);
v___x_2921_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_2922_ = lean_string_append(v___x_2921_, v___x_2920_);
return v___x_2922_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__10(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_2924_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__9, &l_Std_Http_URI_Parser_parseURI___closed__9_once, _init_l_Std_Http_URI_Parser_parseURI___closed__9);
v___x_2925_ = lean_string_append(v___x_2924_, v___x_2923_);
return v___x_2925_;
}
}
static lean_object* _init_l_Std_Http_URI_Parser_parseURI___closed__11(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__10, &l_Std_Http_URI_Parser_parseURI___closed__10_once, _init_l_Std_Http_URI_Parser_parseURI___closed__10);
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseURI(lean_object* v_config_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_2928_, v_a_2929_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_pos_2931_; lean_object* v_res_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_3072_; 
v_pos_2931_ = lean_ctor_get(v___x_2930_, 0);
v_res_2932_ = lean_ctor_get(v___x_2930_, 1);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_2934_ = v___x_2930_;
v_isShared_2935_ = v_isSharedCheck_3072_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_res_2932_);
lean_inc(v_pos_2931_);
lean_dec(v___x_2930_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_3072_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v_array_2936_; lean_object* v_idx_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v_array_2936_ = lean_ctor_get(v_pos_2931_, 0);
v_idx_2937_ = lean_ctor_get(v_pos_2931_, 1);
v___x_2938_ = lean_byte_array_size(v_array_2936_);
v___x_2939_ = lean_nat_dec_lt(v_idx_2937_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec(v_res_2932_);
lean_dec_ref(v_config_2928_);
v___x_2940_ = lean_box(0);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 1);
lean_ctor_set(v___x_2934_, 1, v___x_2940_);
v___x_2942_ = v___x_2934_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_pos_2931_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
else
{
uint8_t v___x_2944_; uint8_t v_c_2945_; uint8_t v___x_2946_; 
v___x_2944_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_2945_ = lean_byte_array_fget(v_array_2936_, v_idx_2937_);
v___x_2946_ = lean_uint8_dec_eq(v_c_2945_, v___x_2944_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_dec(v_res_2932_);
lean_dec_ref(v_config_2928_);
v___x_2947_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 1);
lean_ctor_set(v___x_2934_, 1, v___x_2947_);
v___x_2949_ = v___x_2934_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_pos_2931_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
else
{
lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3069_; 
lean_inc(v_idx_2937_);
lean_inc_ref(v_array_2936_);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_pos_2931_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; lean_object* v_unused_3071_; 
v_unused_3070_ = lean_ctor_get(v_pos_2931_, 1);
lean_dec(v_unused_3070_);
v_unused_3071_ = lean_ctor_get(v_pos_2931_, 0);
lean_dec(v_unused_3071_);
v___x_2952_ = v_pos_2931_;
v_isShared_2953_ = v_isSharedCheck_3069_;
goto v_resetjp_2951_;
}
else
{
lean_dec(v_pos_2931_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3069_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v_it_x27_2957_; 
v___x_2954_ = lean_unsigned_to_nat(1u);
v___x_2955_ = lean_nat_add(v_idx_2937_, v___x_2954_);
lean_dec(v_idx_2937_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_2955_);
v_it_x27_2957_ = v___x_2952_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_array_2936_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_2955_);
v_it_x27_2957_ = v_reuseFailAlloc_3068_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; 
lean_inc_ref(v_config_2928_);
v___x_2958_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_2928_, v_it_x27_2957_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_res_2959_; lean_object* v_pos_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3058_; 
v_res_2959_ = lean_ctor_get(v___x_2958_, 1);
v_pos_2960_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_2962_ = v___x_2958_;
v_isShared_2963_ = v_isSharedCheck_3058_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_res_2959_);
lean_inc(v_pos_2960_);
lean_dec(v___x_2958_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3058_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v_fst_2964_; lean_object* v_snd_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3057_; 
v_fst_2964_ = lean_ctor_get(v_res_2959_, 0);
v_snd_2965_ = lean_ctor_get(v_res_2959_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_res_2959_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_2967_ = v_res_2959_;
v_isShared_2968_ = v_isSharedCheck_3057_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_snd_2965_);
lean_inc(v_fst_2964_);
lean_dec(v_res_2959_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3057_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___y_2970_; lean_object* v_pos_2971_; lean_object* v_res_2972_; lean_object* v___y_2978_; lean_object* v_idx_2979_; lean_object* v_pos_2980_; lean_object* v_idx_2981_; lean_object* v_err_2982_; lean_object* v___y_2989_; lean_object* v_idx_2990_; lean_object* v_pos_2991_; lean_object* v_err_2992_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v_array_3023_; lean_object* v_idx_3024_; lean_object* v_pos_3026_; lean_object* v_idx_3027_; lean_object* v_err_3028_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v_array_3023_ = lean_ctor_get(v_pos_2960_, 0);
v_idx_3024_ = lean_ctor_get(v_pos_2960_, 1);
lean_inc(v_idx_3024_);
v___x_3034_ = lean_byte_array_size(v_array_3023_);
v___x_3035_ = lean_nat_dec_lt(v_idx_3024_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_box(0);
lean_inc(v_idx_3024_);
v_pos_3026_ = v_pos_2960_;
v_idx_3027_ = v_idx_3024_;
v_err_3028_ = v___x_3036_;
goto v___jp_3025_;
}
else
{
uint8_t v___x_3037_; uint8_t v_c_3038_; uint8_t v___x_3039_; 
v___x_3037_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_3038_ = lean_byte_array_fget(v_array_3023_, v_idx_3024_);
v___x_3039_ = lean_uint8_dec_eq(v_c_3038_, v___x_3037_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3024_);
v_pos_3026_ = v_pos_2960_;
v_idx_3027_ = v_idx_3024_;
v_err_3028_ = v___x_3040_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3054_; 
lean_inc_ref(v_array_3023_);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_pos_2960_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; lean_object* v_unused_3056_; 
v_unused_3055_ = lean_ctor_get(v_pos_2960_, 1);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v_pos_2960_, 0);
lean_dec(v_unused_3056_);
v___x_3042_ = v_pos_2960_;
v_isShared_3043_ = v_isSharedCheck_3054_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v_pos_2960_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3054_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; lean_object* v_it_x27_3046_; 
v___x_3044_ = lean_nat_add(v_idx_3024_, v___x_2954_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 1, v___x_3044_);
v_it_x27_3046_ = v___x_3042_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_array_3023_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3044_);
v_it_x27_3046_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; 
lean_inc_ref(v_config_2928_);
v___x_3047_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_2928_, v_it_x27_3046_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_pos_3048_; lean_object* v_res_3049_; 
lean_dec(v_idx_3024_);
lean_del_object(v___x_2967_);
v_pos_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_pos_3048_);
v_res_3049_ = lean_ctor_get(v___x_3047_, 1);
lean_inc(v_res_3049_);
lean_dec_ref(v___x_3047_);
v___y_2995_ = v_pos_3048_;
v___y_2996_ = v_res_3049_;
goto v___jp_2994_;
}
else
{
lean_object* v_pos_3050_; lean_object* v_err_3051_; lean_object* v_idx_3052_; 
v_pos_3050_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_pos_3050_);
v_err_3051_ = lean_ctor_get(v___x_3047_, 1);
lean_inc(v_err_3051_);
lean_dec_ref(v___x_3047_);
v_idx_3052_ = lean_ctor_get(v_pos_3050_, 1);
lean_inc(v_idx_3052_);
v_pos_3026_ = v_pos_3050_;
v_idx_3027_ = v_idx_3052_;
v_err_3028_ = v_err_3051_;
goto v___jp_3025_;
}
}
}
}
}
v___jp_2969_:
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2973_, 0, v_res_2932_);
lean_ctor_set(v___x_2973_, 1, v_fst_2964_);
lean_ctor_set(v___x_2973_, 2, v_snd_2965_);
lean_ctor_set(v___x_2973_, 3, v___y_2970_);
lean_ctor_set(v___x_2973_, 4, v_res_2972_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 1, v___x_2973_);
lean_ctor_set(v___x_2962_, 0, v_pos_2971_);
v___x_2975_ = v___x_2962_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_pos_2971_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
v___jp_2977_:
{
uint8_t v___x_2983_; 
v___x_2983_ = lean_nat_dec_eq(v_idx_2979_, v_idx_2981_);
lean_dec(v_idx_2981_);
lean_dec(v_idx_2979_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2985_; 
lean_dec_ref(v___y_2978_);
lean_dec(v_snd_2965_);
lean_dec(v_fst_2964_);
lean_del_object(v___x_2962_);
lean_dec(v_res_2932_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 1);
lean_ctor_set(v___x_2934_, 1, v_err_2982_);
lean_ctor_set(v___x_2934_, 0, v_pos_2980_);
v___x_2985_ = v___x_2934_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_pos_2980_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_err_2982_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
else
{
lean_object* v___x_2987_; 
lean_dec(v_err_2982_);
lean_del_object(v___x_2934_);
v___x_2987_ = lean_box(0);
v___y_2970_ = v___y_2978_;
v_pos_2971_ = v_pos_2980_;
v_res_2972_ = v___x_2987_;
goto v___jp_2969_;
}
}
v___jp_2988_:
{
lean_object* v_idx_2993_; 
v_idx_2993_ = lean_ctor_get(v_pos_2991_, 1);
lean_inc(v_idx_2993_);
v___y_2978_ = v___y_2989_;
v_idx_2979_ = v_idx_2990_;
v_pos_2980_ = v_pos_2991_;
v_idx_2981_ = v_idx_2993_;
v_err_2982_ = v_err_2992_;
goto v___jp_2977_;
}
v___jp_2994_:
{
lean_object* v_array_2997_; lean_object* v_idx_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v_array_2997_ = lean_ctor_get(v___y_2995_, 0);
v_idx_2998_ = lean_ctor_get(v___y_2995_, 1);
lean_inc(v_idx_2998_);
v___x_2999_ = lean_byte_array_size(v_array_2997_);
v___x_3000_ = lean_nat_dec_lt(v_idx_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec_ref(v_config_2928_);
v___x_3001_ = lean_box(0);
lean_inc(v_idx_2998_);
v___y_2978_ = v___y_2996_;
v_idx_2979_ = v_idx_2998_;
v_pos_2980_ = v___y_2995_;
v_idx_2981_ = v_idx_2998_;
v_err_2982_ = v___x_3001_;
goto v___jp_2977_;
}
else
{
uint8_t v___x_3002_; uint8_t v_c_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__4);
v_c_3003_ = lean_byte_array_fget(v_array_2997_, v_idx_2998_);
v___x_3004_ = lean_uint8_dec_eq(v_c_3003_, v___x_3002_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
lean_dec_ref(v_config_2928_);
v___x_3005_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__4, &l_Std_Http_URI_Parser_parseURI___closed__4_once, _init_l_Std_Http_URI_Parser_parseURI___closed__4);
lean_inc(v_idx_2998_);
v___y_2978_ = v___y_2996_;
v_idx_2979_ = v_idx_2998_;
v_pos_2980_ = v___y_2995_;
v_idx_2981_ = v_idx_2998_;
v_err_2982_ = v___x_3005_;
goto v___jp_2977_;
}
else
{
lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3020_; 
lean_inc_ref(v_array_2997_);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___y_2995_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; lean_object* v_unused_3022_; 
v_unused_3021_ = lean_ctor_get(v___y_2995_, 1);
lean_dec(v_unused_3021_);
v_unused_3022_ = lean_ctor_get(v___y_2995_, 0);
lean_dec(v_unused_3022_);
v___x_3007_ = v___y_2995_;
v_isShared_3008_ = v_isSharedCheck_3020_;
goto v_resetjp_3006_;
}
else
{
lean_dec(v___y_2995_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3020_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v_it_x27_3011_; 
v___x_3009_ = lean_nat_add(v_idx_2998_, v___x_2954_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v___x_3009_);
v_it_x27_3011_ = v___x_3007_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_array_2997_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___x_3009_);
v_it_x27_3011_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; 
v___x_3012_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseFragment(v_config_2928_, v_it_x27_3011_);
lean_dec_ref(v_config_2928_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_pos_3013_; lean_object* v_res_3014_; lean_object* v___x_3015_; 
v_pos_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_pos_3013_);
v_res_3014_ = lean_ctor_get(v___x_3012_, 1);
lean_inc(v_res_3014_);
lean_dec_ref(v___x_3012_);
v___x_3015_ = l_Std_Http_URI_EncodedFragment_decode(v_res_3014_);
lean_dec(v_res_3014_);
if (lean_obj_tag(v___x_3015_) == 1)
{
lean_dec(v_idx_2998_);
lean_del_object(v___x_2934_);
v___y_2970_ = v___y_2996_;
v_pos_2971_ = v_pos_3013_;
v_res_2972_ = v___x_3015_;
goto v___jp_2969_;
}
else
{
lean_object* v___x_3016_; 
lean_dec(v___x_3015_);
v___x_3016_ = ((lean_object*)(l_Std_Http_URI_Parser_parseURI___closed__6));
v___y_2989_ = v___y_2996_;
v_idx_2990_ = v_idx_2998_;
v_pos_2991_ = v_pos_3013_;
v_err_2992_ = v___x_3016_;
goto v___jp_2988_;
}
}
else
{
lean_object* v_pos_3017_; lean_object* v_err_3018_; 
v_pos_3017_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_pos_3017_);
v_err_3018_ = lean_ctor_get(v___x_3012_, 1);
lean_inc(v_err_3018_);
lean_dec_ref(v___x_3012_);
v___y_2989_ = v___y_2996_;
v_idx_2990_ = v_idx_2998_;
v_pos_2991_ = v_pos_3017_;
v_err_2992_ = v_err_3018_;
goto v___jp_2988_;
}
}
}
}
}
}
v___jp_3025_:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_nat_dec_eq(v_idx_3024_, v_idx_3027_);
lean_dec(v_idx_3027_);
lean_dec(v_idx_3024_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3031_; 
lean_dec(v_snd_2965_);
lean_dec(v_fst_2964_);
lean_del_object(v___x_2962_);
lean_del_object(v___x_2934_);
lean_dec(v_res_2932_);
lean_dec_ref(v_config_2928_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 1);
lean_ctor_set(v___x_2967_, 1, v_err_3028_);
lean_ctor_set(v___x_2967_, 0, v_pos_3026_);
v___x_3031_ = v___x_2967_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_pos_3026_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_err_3028_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
else
{
lean_object* v___x_3033_; 
lean_dec(v_err_3028_);
lean_del_object(v___x_2967_);
v___x_3033_ = l_Std_Http_URI_Query_empty;
v___y_2995_ = v_pos_3026_;
v___y_2996_ = v___x_3033_;
goto v___jp_2994_;
}
}
}
}
}
else
{
lean_object* v_pos_3059_; lean_object* v_err_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_del_object(v___x_2934_);
lean_dec(v_res_2932_);
lean_dec_ref(v_config_2928_);
v_pos_3059_ = lean_ctor_get(v___x_2958_, 0);
v_err_3060_ = lean_ctor_get(v___x_2958_, 1);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_2958_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_err_3060_);
lean_inc(v_pos_3059_);
lean_dec(v___x_2958_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_pos_3059_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_err_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
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
lean_object* v_pos_3073_; lean_object* v_err_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec_ref(v_config_2928_);
v_pos_3073_ = lean_ctor_get(v___x_2930_, 0);
v_err_3074_ = lean_ctor_get(v___x_2930_, 1);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_2930_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_err_3074_);
lean_inc(v_pos_3073_);
lean_dec(v___x_2930_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_pos_3073_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_err_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0(void){
_start:
{
uint8_t v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v___x_3083_ = lean_uint8_to_nat(v___x_3082_);
return v___x_3083_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__0);
v___x_3085_ = l_Nat_reprFast(v___x_3084_);
return v___x_3085_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__1);
v___x_3087_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__2));
v___x_3088_ = lean_string_append(v___x_3087_, v___x_3086_);
return v___x_3088_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseIPv6___closed__6));
v___x_3090_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__2);
v___x_3091_ = lean_string_append(v___x_3090_, v___x_3089_);
return v___x_3091_;
}
}
static lean_object* _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__3);
v___x_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(lean_object* v_a_3094_){
_start:
{
lean_object* v_array_3095_; lean_object* v_idx_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_array_3095_ = lean_ctor_get(v_a_3094_, 0);
v_idx_3096_ = lean_ctor_get(v_a_3094_, 1);
v___x_3097_ = lean_byte_array_size(v_array_3095_);
v___x_3098_ = lean_nat_dec_lt(v_idx_3096_, v___x_3097_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_box(0);
v___x_3100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3100_, 0, v_a_3094_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
return v___x_3100_;
}
else
{
uint8_t v___x_3101_; uint8_t v_c_3102_; uint8_t v___x_3103_; 
v___x_3101_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__6);
v_c_3102_ = lean_byte_array_fget(v_array_3095_, v_idx_3096_);
v___x_3103_ = lean_uint8_dec_eq(v_c_3102_, v___x_3101_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk___closed__4);
v___x_3105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3105_, 0, v_a_3094_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
return v___x_3105_;
}
else
{
lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3116_; 
lean_inc(v_idx_3096_);
lean_inc_ref(v_array_3095_);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_a_3094_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; lean_object* v_unused_3118_; 
v_unused_3117_ = lean_ctor_get(v_a_3094_, 1);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_a_3094_, 0);
lean_dec(v_unused_3118_);
v___x_3107_ = v_a_3094_;
v_isShared_3108_ = v_isSharedCheck_3116_;
goto v_resetjp_3106_;
}
else
{
lean_dec(v_a_3094_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3116_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v_it_x27_3112_; 
v___x_3109_ = lean_unsigned_to_nat(1u);
v___x_3110_ = lean_nat_add(v_idx_3096_, v___x_3109_);
lean_dec(v_idx_3096_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v___x_3110_);
v_it_x27_3112_ = v___x_3107_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_array_3095_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3110_);
v_it_x27_3112_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_box(3);
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_it_x27_3112_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
return v___x_3114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(lean_object* v_config_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_array_3127_; lean_object* v_idx_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v_array_3127_ = lean_ctor_get(v_a_3123_, 0);
v_idx_3128_ = lean_ctor_get(v_a_3123_, 1);
v___x_3129_ = lean_byte_array_size(v_array_3127_);
v___x_3130_ = lean_nat_dec_lt(v_idx_3128_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_dec_ref(v_config_3122_);
goto v___jp_3124_;
}
else
{
uint8_t v___x_3131_; uint8_t v___x_3132_; uint8_t v___x_3133_; 
v___x_3131_ = lean_byte_array_fget(v_array_3127_, v_idx_3128_);
v___x_3132_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3133_ = lean_uint8_dec_eq(v___x_3131_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_dec_ref(v_config_3122_);
goto v___jp_3124_;
}
else
{
if (v___x_3133_ == 0)
{
lean_dec_ref(v_config_3122_);
goto v___jp_3124_;
}
else
{
lean_object* v___x_3134_; 
lean_inc_ref(v_a_3123_);
lean_inc_ref(v_config_3122_);
v___x_3134_ = l_Std_Http_URI_Parser_parsePath(v_config_3122_, v___x_3133_, v___x_3133_, v_a_3123_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_pos_3135_; lean_object* v_res_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3181_; 
v_pos_3135_ = lean_ctor_get(v___x_3134_, 0);
v_res_3136_ = lean_ctor_get(v___x_3134_, 1);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3138_ = v___x_3134_;
v_isShared_3139_ = v_isSharedCheck_3181_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_res_3136_);
lean_inc(v_pos_3135_);
lean_dec(v___x_3134_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3181_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v_pos_3141_; lean_object* v_res_3142_; lean_object* v_array_3147_; lean_object* v_idx_3148_; lean_object* v_pos_3150_; lean_object* v_idx_3151_; lean_object* v_err_3152_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v_array_3147_ = lean_ctor_get(v_pos_3135_, 0);
v_idx_3148_ = lean_ctor_get(v_pos_3135_, 1);
lean_inc(v_idx_3148_);
v___x_3156_ = lean_byte_array_size(v_array_3147_);
v___x_3157_ = lean_nat_dec_lt(v_idx_3148_, v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; 
lean_dec_ref(v_config_3122_);
v___x_3158_ = lean_box(0);
lean_inc(v_idx_3148_);
v_pos_3150_ = v_pos_3135_;
v_idx_3151_ = v_idx_3148_;
v_err_3152_ = v___x_3158_;
goto v___jp_3149_;
}
else
{
uint8_t v___x_3159_; uint8_t v_c_3160_; uint8_t v___x_3161_; 
v___x_3159_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_3160_ = lean_byte_array_fget(v_array_3147_, v_idx_3148_);
v___x_3161_ = lean_uint8_dec_eq(v_c_3160_, v___x_3159_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; 
lean_dec_ref(v_config_3122_);
v___x_3162_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3148_);
v_pos_3150_ = v_pos_3135_;
v_idx_3151_ = v_idx_3148_;
v_err_3152_ = v___x_3162_;
goto v___jp_3149_;
}
else
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3178_; 
lean_inc_ref(v_array_3147_);
v_isSharedCheck_3178_ = !lean_is_exclusive(v_pos_3135_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; lean_object* v_unused_3180_; 
v_unused_3179_ = lean_ctor_get(v_pos_3135_, 1);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v_pos_3135_, 0);
lean_dec(v_unused_3180_);
v___x_3164_ = v_pos_3135_;
v_isShared_3165_ = v_isSharedCheck_3178_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v_pos_3135_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3178_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v_it_x27_3169_; 
v___x_3166_ = lean_unsigned_to_nat(1u);
v___x_3167_ = lean_nat_add(v_idx_3148_, v___x_3166_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 1, v___x_3167_);
v_it_x27_3169_ = v___x_3164_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_array_3147_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_3167_);
v_it_x27_3169_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; 
v___x_3170_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3122_, v_it_x27_3169_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_pos_3171_; lean_object* v_res_3172_; lean_object* v___x_3173_; 
lean_dec(v_idx_3148_);
lean_dec_ref(v_a_3123_);
v_pos_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_pos_3171_);
v_res_3172_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_res_3172_);
lean_dec_ref(v___x_3170_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_res_3172_);
v_pos_3141_ = v_pos_3171_;
v_res_3142_ = v___x_3173_;
goto v___jp_3140_;
}
else
{
lean_object* v_pos_3174_; lean_object* v_err_3175_; lean_object* v_idx_3176_; 
v_pos_3174_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_pos_3174_);
v_err_3175_ = lean_ctor_get(v___x_3170_, 1);
lean_inc(v_err_3175_);
lean_dec_ref(v___x_3170_);
v_idx_3176_ = lean_ctor_get(v_pos_3174_, 1);
lean_inc(v_idx_3176_);
v_pos_3150_ = v_pos_3174_;
v_idx_3151_ = v_idx_3176_;
v_err_3152_ = v_err_3175_;
goto v___jp_3149_;
}
}
}
}
}
v___jp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_res_3136_);
lean_ctor_set(v___x_3143_, 1, v_res_3142_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 1, v___x_3143_);
lean_ctor_set(v___x_3138_, 0, v_pos_3141_);
v___x_3145_ = v___x_3138_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_pos_3141_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
v___jp_3149_:
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_nat_dec_eq(v_idx_3148_, v_idx_3151_);
lean_dec(v_idx_3151_);
lean_dec(v_idx_3148_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
lean_dec_ref(v_pos_3150_);
lean_del_object(v___x_3138_);
lean_dec(v_res_3136_);
v___x_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3154_, 0, v_a_3123_);
lean_ctor_set(v___x_3154_, 1, v_err_3152_);
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; 
lean_dec(v_err_3152_);
lean_dec_ref(v_a_3123_);
v___x_3155_ = lean_box(0);
v_pos_3141_ = v_pos_3150_;
v_res_3142_ = v___x_3155_;
goto v___jp_3140_;
}
}
}
}
else
{
lean_object* v_err_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v_config_3122_);
v_err_3182_ = lean_ctor_get(v___x_3134_, 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v___x_3134_, 0);
lean_dec(v_unused_3190_);
v___x_3184_ = v___x_3134_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_err_3182_);
lean_dec(v___x_3134_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v_a_3123_);
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3123_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_err_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
}
v___jp_3124_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin___closed__1));
v___x_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3126_, 0, v_a_3123_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
return v___x_3126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(lean_object* v_config_3191_, lean_object* v_scheme_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_array_3194_; lean_object* v_idx_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v_array_3194_ = lean_ctor_get(v_a_3193_, 0);
v_idx_3195_ = lean_ctor_get(v_a_3193_, 1);
v___x_3196_ = lean_byte_array_size(v_array_3194_);
v___x_3197_ = lean_nat_dec_lt(v_idx_3195_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_dec_ref(v_scheme_3192_);
lean_dec_ref(v_config_3191_);
v___x_3198_ = lean_box(0);
v___x_3199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_a_3193_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
return v___x_3199_;
}
else
{
uint8_t v___x_3200_; uint8_t v_c_3201_; uint8_t v___x_3202_; 
v___x_3200_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_3201_ = lean_byte_array_fget(v_array_3194_, v_idx_3195_);
v___x_3202_ = lean_uint8_dec_eq(v_c_3201_, v___x_3200_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_dec_ref(v_scheme_3192_);
lean_dec_ref(v_config_3191_);
v___x_3203_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v_a_3193_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
return v___x_3204_;
}
else
{
lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3278_; 
lean_inc(v_idx_3195_);
lean_inc_ref(v_array_3194_);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_a_3193_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; lean_object* v_unused_3280_; 
v_unused_3279_ = lean_ctor_get(v_a_3193_, 1);
lean_dec(v_unused_3279_);
v_unused_3280_ = lean_ctor_get(v_a_3193_, 0);
lean_dec(v_unused_3280_);
v___x_3206_ = v_a_3193_;
v_isShared_3207_ = v_isSharedCheck_3278_;
goto v_resetjp_3205_;
}
else
{
lean_dec(v_a_3193_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3278_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v_it_x27_3211_; 
v___x_3208_ = lean_unsigned_to_nat(1u);
v___x_3209_ = lean_nat_add(v_idx_3195_, v___x_3208_);
lean_dec(v_idx_3195_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 1, v___x_3209_);
v_it_x27_3211_ = v___x_3206_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_array_3194_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v___x_3209_);
v_it_x27_3211_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3212_; 
lean_inc_ref(v_config_3191_);
v___x_3212_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3191_, v_it_x27_3211_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_res_3213_; lean_object* v_pos_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3267_; 
v_res_3213_ = lean_ctor_get(v___x_3212_, 1);
v_pos_3214_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3216_ = v___x_3212_;
v_isShared_3217_ = v_isSharedCheck_3267_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_res_3213_);
lean_inc(v_pos_3214_);
lean_dec(v___x_3212_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3267_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v_fst_3218_; lean_object* v_snd_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3266_; 
v_fst_3218_ = lean_ctor_get(v_res_3213_, 0);
v_snd_3219_ = lean_ctor_get(v_res_3213_, 1);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_res_3213_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3221_ = v_res_3213_;
v_isShared_3222_ = v_isSharedCheck_3266_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_snd_3219_);
lean_inc(v_fst_3218_);
lean_dec(v_res_3213_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3266_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v_array_3232_; lean_object* v_idx_3233_; lean_object* v_pos_3235_; lean_object* v_idx_3236_; lean_object* v_err_3237_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_array_3232_ = lean_ctor_get(v_pos_3214_, 0);
v_idx_3233_ = lean_ctor_get(v_pos_3214_, 1);
lean_inc(v_idx_3233_);
v___x_3243_ = lean_byte_array_size(v_array_3232_);
v___x_3244_ = lean_nat_dec_lt(v_idx_3233_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
lean_dec_ref(v_config_3191_);
v___x_3245_ = lean_box(0);
lean_inc(v_idx_3233_);
v_pos_3235_ = v_pos_3214_;
v_idx_3236_ = v_idx_3233_;
v_err_3237_ = v___x_3245_;
goto v___jp_3234_;
}
else
{
uint8_t v___x_3246_; uint8_t v_c_3247_; uint8_t v___x_3248_; 
v___x_3246_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_3247_ = lean_byte_array_fget(v_array_3232_, v_idx_3233_);
v___x_3248_ = lean_uint8_dec_eq(v_c_3247_, v___x_3246_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
lean_dec_ref(v_config_3191_);
v___x_3249_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3233_);
v_pos_3235_ = v_pos_3214_;
v_idx_3236_ = v_idx_3233_;
v_err_3237_ = v___x_3249_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3263_; 
lean_inc_ref(v_array_3232_);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_pos_3214_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; lean_object* v_unused_3265_; 
v_unused_3264_ = lean_ctor_get(v_pos_3214_, 1);
lean_dec(v_unused_3264_);
v_unused_3265_ = lean_ctor_get(v_pos_3214_, 0);
lean_dec(v_unused_3265_);
v___x_3251_ = v_pos_3214_;
v_isShared_3252_ = v_isSharedCheck_3263_;
goto v_resetjp_3250_;
}
else
{
lean_dec(v_pos_3214_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3263_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v_it_x27_3255_; 
v___x_3253_ = lean_nat_add(v_idx_3233_, v___x_3208_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v___x_3253_);
v_it_x27_3255_ = v___x_3251_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_array_3232_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3253_);
v_it_x27_3255_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; 
v___x_3256_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3191_, v_it_x27_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_pos_3257_; lean_object* v_res_3258_; 
lean_dec(v_idx_3233_);
lean_del_object(v___x_3221_);
v_pos_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_pos_3257_);
v_res_3258_ = lean_ctor_get(v___x_3256_, 1);
lean_inc(v_res_3258_);
lean_dec_ref(v___x_3256_);
v___y_3224_ = v_pos_3257_;
v___y_3225_ = v_res_3258_;
goto v___jp_3223_;
}
else
{
lean_object* v_pos_3259_; lean_object* v_err_3260_; lean_object* v_idx_3261_; 
v_pos_3259_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_pos_3259_);
v_err_3260_ = lean_ctor_get(v___x_3256_, 1);
lean_inc(v_err_3260_);
lean_dec_ref(v___x_3256_);
v_idx_3261_ = lean_ctor_get(v_pos_3259_, 1);
lean_inc(v_idx_3261_);
v_pos_3235_ = v_pos_3259_;
v_idx_3236_ = v_idx_3261_;
v_err_3237_ = v_err_3260_;
goto v___jp_3234_;
}
}
}
}
}
v___jp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3227_, 0, v_scheme_3192_);
lean_ctor_set(v___x_3227_, 1, v_fst_3218_);
lean_ctor_set(v___x_3227_, 2, v_snd_3219_);
lean_ctor_set(v___x_3227_, 3, v___y_3225_);
lean_ctor_set(v___x_3227_, 4, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v___x_3228_);
lean_ctor_set(v___x_3216_, 0, v___y_3224_);
v___x_3230_ = v___x_3216_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___y_3224_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
v___jp_3234_:
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_nat_dec_eq(v_idx_3233_, v_idx_3236_);
lean_dec(v_idx_3236_);
lean_dec(v_idx_3233_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3240_; 
lean_dec(v_snd_3219_);
lean_dec(v_fst_3218_);
lean_del_object(v___x_3216_);
lean_dec_ref(v_scheme_3192_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 1);
lean_ctor_set(v___x_3221_, 1, v_err_3237_);
lean_ctor_set(v___x_3221_, 0, v_pos_3235_);
v___x_3240_ = v___x_3221_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_pos_3235_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_err_3237_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
else
{
lean_object* v___x_3242_; 
lean_dec(v_err_3237_);
lean_del_object(v___x_3221_);
v___x_3242_ = l_Std_Http_URI_Query_empty;
v___y_3224_ = v_pos_3235_;
v___y_3225_ = v___x_3242_;
goto v___jp_3223_;
}
}
}
}
}
else
{
lean_object* v_pos_3268_; lean_object* v_err_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec_ref(v_scheme_3192_);
lean_dec_ref(v_config_3191_);
v_pos_3268_ = lean_ctor_get(v___x_3212_, 0);
v_err_3269_ = lean_ctor_get(v___x_3212_, 1);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3212_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_err_3269_);
lean_inc(v_pos_3268_);
lean_dec(v___x_3212_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_pos_3268_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_err_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(lean_object* v_config_3289_, lean_object* v_a_3290_){
_start:
{
lean_object* v___x_3294_; 
lean_inc_ref(v_a_3290_);
v___x_3294_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3289_, v_a_3290_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_pos_3295_; lean_object* v_res_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3392_; 
v_pos_3295_ = lean_ctor_get(v___x_3294_, 0);
v_res_3296_ = lean_ctor_get(v___x_3294_, 1);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3298_ = v___x_3294_;
v_isShared_3299_ = v_isSharedCheck_3392_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_res_3296_);
lean_inc(v_pos_3295_);
lean_dec(v___x_3294_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3392_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v_idx_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v_pos_3315_; lean_object* v_idx_3316_; lean_object* v_err_3317_; uint8_t v___y_3322_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3388_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__4));
v___x_3389_ = lean_string_dec_eq(v_res_3296_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3390_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__5));
v___x_3391_ = lean_string_dec_eq(v_res_3296_, v___x_3390_);
v___y_3322_ = v___x_3391_;
goto v___jp_3321_;
}
else
{
v___y_3322_ = v___x_3389_;
goto v___jp_3321_;
}
v___jp_3300_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3306_, 0, v_res_3296_);
lean_ctor_set(v___x_3306_, 1, v___y_3302_);
lean_ctor_set(v___x_3306_, 2, v___y_3303_);
lean_ctor_set(v___x_3306_, 3, v___y_3304_);
lean_ctor_set(v___x_3306_, 4, v___x_3305_);
v___x_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 1, v___x_3307_);
lean_ctor_set(v___x_3298_, 0, v___y_3301_);
v___x_3309_ = v___x_3298_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___y_3301_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
v___jp_3311_:
{
uint8_t v___x_3318_; 
v___x_3318_ = lean_nat_dec_eq(v_idx_3312_, v_idx_3316_);
lean_dec(v_idx_3316_);
lean_dec(v_idx_3312_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
lean_dec_ref(v_pos_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_del_object(v___x_3298_);
lean_dec(v_res_3296_);
v___x_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3319_, 0, v_a_3290_);
lean_ctor_set(v___x_3319_, 1, v_err_3317_);
return v___x_3319_;
}
else
{
lean_object* v___x_3320_; 
lean_dec(v_err_3317_);
lean_dec_ref(v_a_3290_);
v___x_3320_ = l_Std_Http_URI_Query_empty;
v___y_3301_ = v_pos_3315_;
v___y_3302_ = v___y_3313_;
v___y_3303_ = v___y_3314_;
v___y_3304_ = v___x_3320_;
goto v___jp_3300_;
}
}
v___jp_3321_:
{
if (v___y_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_del_object(v___x_3298_);
lean_dec(v_res_3296_);
lean_dec(v_pos_3295_);
lean_dec_ref(v_config_3289_);
v___x_3323_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__3));
v___x_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3324_, 0, v_a_3290_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
return v___x_3324_;
}
else
{
lean_object* v_array_3325_; lean_object* v_idx_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3387_; 
v_array_3325_ = lean_ctor_get(v_pos_3295_, 0);
v_idx_3326_ = lean_ctor_get(v_pos_3295_, 1);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_pos_3295_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3328_ = v_pos_3295_;
v_isShared_3329_ = v_isSharedCheck_3387_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_idx_3326_);
lean_inc(v_array_3325_);
lean_dec(v_pos_3295_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3387_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3330_ = lean_byte_array_size(v_array_3325_);
v___x_3331_ = lean_nat_dec_lt(v_idx_3326_, v___x_3330_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_del_object(v___x_3328_);
lean_dec(v_idx_3326_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3298_);
lean_dec(v_res_3296_);
lean_dec_ref(v_config_3289_);
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3333_, 0, v_a_3290_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
return v___x_3333_;
}
else
{
uint8_t v___x_3334_; uint8_t v_c_3335_; uint8_t v___x_3336_; 
v___x_3334_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_3335_ = lean_byte_array_fget(v_array_3325_, v_idx_3326_);
v___x_3336_ = lean_uint8_dec_eq(v_c_3335_, v___x_3334_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_del_object(v___x_3328_);
lean_dec(v_idx_3326_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3298_);
lean_dec(v_res_3296_);
lean_dec_ref(v_config_3289_);
v___x_3337_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3338_, 0, v_a_3290_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3339_ = lean_unsigned_to_nat(1u);
v___x_3340_ = lean_nat_add(v_idx_3326_, v___x_3339_);
lean_dec(v_idx_3326_);
v___x_3341_ = lean_nat_dec_lt(v___x_3340_, v___x_3330_);
if (v___x_3341_ == 0)
{
lean_dec(v___x_3340_);
lean_del_object(v___x_3328_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3298_);
lean_dec(v_res_3296_);
lean_dec_ref(v_config_3289_);
goto v___jp_3291_;
}
else
{
uint8_t v___x_3342_; uint8_t v___x_3343_; uint8_t v___x_3344_; 
v___x_3342_ = lean_byte_array_fget(v_array_3325_, v___x_3340_);
v___x_3343_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__2);
v___x_3344_ = lean_uint8_dec_eq(v___x_3342_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_dec(v___x_3340_);
lean_del_object(v___x_3328_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3298_);
lean_dec(v_res_3296_);
lean_dec_ref(v_config_3289_);
goto v___jp_3291_;
}
else
{
if (v___x_3344_ == 0)
{
lean_dec(v___x_3340_);
lean_del_object(v___x_3328_);
lean_dec_ref(v_array_3325_);
lean_del_object(v___x_3298_);
lean_dec(v_res_3296_);
lean_dec_ref(v_config_3289_);
goto v___jp_3291_;
}
else
{
lean_object* v_it_x27_3346_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 1, v___x_3340_);
v_it_x27_3346_ = v___x_3328_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_array_3325_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v___x_3340_);
v_it_x27_3346_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3347_; 
lean_inc_ref(v_config_3289_);
v___x_3347_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHierPart(v_config_3289_, v_it_x27_3346_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_res_3348_; lean_object* v_pos_3349_; lean_object* v_fst_3350_; lean_object* v_snd_3351_; lean_object* v_array_3352_; lean_object* v_idx_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v_res_3348_ = lean_ctor_get(v___x_3347_, 1);
lean_inc(v_res_3348_);
v_pos_3349_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_pos_3349_);
lean_dec_ref(v___x_3347_);
v_fst_3350_ = lean_ctor_get(v_res_3348_, 0);
lean_inc(v_fst_3350_);
v_snd_3351_ = lean_ctor_get(v_res_3348_, 1);
lean_inc(v_snd_3351_);
lean_dec(v_res_3348_);
v_array_3352_ = lean_ctor_get(v_pos_3349_, 0);
v_idx_3353_ = lean_ctor_get(v_pos_3349_, 1);
lean_inc(v_idx_3353_);
v___x_3354_ = lean_byte_array_size(v_array_3352_);
v___x_3355_ = lean_nat_dec_lt(v_idx_3353_, v___x_3354_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref(v_config_3289_);
v___x_3356_ = lean_box(0);
lean_inc(v_idx_3353_);
v_idx_3312_ = v_idx_3353_;
v___y_3313_ = v_fst_3350_;
v___y_3314_ = v_snd_3351_;
v_pos_3315_ = v_pos_3349_;
v_idx_3316_ = v_idx_3353_;
v_err_3317_ = v___x_3356_;
goto v___jp_3311_;
}
else
{
uint8_t v___x_3357_; uint8_t v_c_3358_; uint8_t v___x_3359_; 
v___x_3357_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__3);
v_c_3358_ = lean_byte_array_fget(v_array_3352_, v_idx_3353_);
v___x_3359_ = lean_uint8_dec_eq(v_c_3358_, v___x_3357_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
lean_dec_ref(v_config_3289_);
v___x_3360_ = lean_obj_once(&l_Std_Http_URI_Parser_parseURI___closed__11, &l_Std_Http_URI_Parser_parseURI___closed__11_once, _init_l_Std_Http_URI_Parser_parseURI___closed__11);
lean_inc(v_idx_3353_);
v_idx_3312_ = v_idx_3353_;
v___y_3313_ = v_fst_3350_;
v___y_3314_ = v_snd_3351_;
v_pos_3315_ = v_pos_3349_;
v_idx_3316_ = v_idx_3353_;
v_err_3317_ = v___x_3360_;
goto v___jp_3311_;
}
else
{
lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3374_; 
lean_inc_ref(v_array_3352_);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_pos_3349_);
if (v_isSharedCheck_3374_ == 0)
{
lean_object* v_unused_3375_; lean_object* v_unused_3376_; 
v_unused_3375_ = lean_ctor_get(v_pos_3349_, 1);
lean_dec(v_unused_3375_);
v_unused_3376_ = lean_ctor_get(v_pos_3349_, 0);
lean_dec(v_unused_3376_);
v___x_3362_ = v_pos_3349_;
v_isShared_3363_ = v_isSharedCheck_3374_;
goto v_resetjp_3361_;
}
else
{
lean_dec(v_pos_3349_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3374_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3364_; lean_object* v_it_x27_3366_; 
v___x_3364_ = lean_nat_add(v_idx_3353_, v___x_3339_);
if (v_isShared_3363_ == 0)
{
lean_ctor_set(v___x_3362_, 1, v___x_3364_);
v_it_x27_3366_ = v___x_3362_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_array_3352_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v___x_3364_);
v_it_x27_3366_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; 
v___x_3367_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseQuery(v_config_3289_, v_it_x27_3366_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_pos_3368_; lean_object* v_res_3369_; 
lean_dec(v_idx_3353_);
lean_dec_ref(v_a_3290_);
v_pos_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_pos_3368_);
v_res_3369_ = lean_ctor_get(v___x_3367_, 1);
lean_inc(v_res_3369_);
lean_dec_ref(v___x_3367_);
v___y_3301_ = v_pos_3368_;
v___y_3302_ = v_fst_3350_;
v___y_3303_ = v_snd_3351_;
v___y_3304_ = v_res_3369_;
goto v___jp_3300_;
}
else
{
lean_object* v_pos_3370_; lean_object* v_err_3371_; lean_object* v_idx_3372_; 
v_pos_3370_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_pos_3370_);
v_err_3371_ = lean_ctor_get(v___x_3367_, 1);
lean_inc(v_err_3371_);
lean_dec_ref(v___x_3367_);
v_idx_3372_ = lean_ctor_get(v_pos_3370_, 1);
lean_inc(v_idx_3372_);
v_idx_3312_ = v_idx_3353_;
v___y_3313_ = v_fst_3350_;
v___y_3314_ = v_snd_3351_;
v_pos_3315_ = v_pos_3370_;
v_idx_3316_ = v_idx_3372_;
v_err_3317_ = v_err_3371_;
goto v___jp_3311_;
}
}
}
}
}
}
else
{
lean_object* v_err_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_del_object(v___x_3298_);
lean_dec(v_res_3296_);
lean_dec_ref(v_config_3289_);
v_err_3377_ = lean_ctor_get(v___x_3347_, 1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; 
v_unused_3385_ = lean_ctor_get(v___x_3347_, 0);
lean_dec(v_unused_3385_);
v___x_3379_ = v___x_3347_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_err_3377_);
lean_dec(v___x_3347_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v_a_3290_);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3290_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_err_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
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
lean_object* v_err_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v_config_3289_);
v_err_3393_ = lean_ctor_get(v___x_3294_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v___x_3294_, 0);
lean_dec(v_unused_3401_);
v___x_3395_ = v___x_3294_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_err_3393_);
lean_dec(v___x_3294_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v_a_3290_);
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3290_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_err_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
v___jp_3291_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp___closed__1));
v___x_3293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_a_3290_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(lean_object* v_config_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___x_3404_; 
lean_inc_ref(v_a_3403_);
v___x_3404_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme(v_config_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_pos_3405_; lean_object* v_res_3406_; lean_object* v___x_3407_; 
v_pos_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_pos_3405_);
v_res_3406_ = lean_ctor_get(v___x_3404_, 1);
lean_inc(v_res_3406_);
lean_dec_ref(v___x_3404_);
v___x_3407_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteFromScheme(v_config_3402_, v_res_3406_, v_pos_3405_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_dec_ref(v_a_3403_);
return v___x_3407_;
}
else
{
lean_object* v_err_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
v_err_3408_ = lean_ctor_get(v___x_3407_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v___x_3407_, 0);
lean_dec(v_unused_3416_);
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_err_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v_a_3403_);
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3403_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_err_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_err_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v_config_3402_);
v_err_3417_ = lean_ctor_get(v___x_3404_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; 
v_unused_3425_ = lean_ctor_get(v___x_3404_, 0);
lean_dec(v_unused_3425_);
v___x_3419_ = v___x_3404_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_err_3417_);
lean_dec(v___x_3404_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v_a_3403_);
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3403_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_err_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(lean_object* v_config_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___x_3428_; 
lean_inc_ref(v_a_3427_);
v___x_3428_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3426_, v_a_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_pos_3429_; lean_object* v_res_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3482_; 
v_pos_3429_ = lean_ctor_get(v___x_3428_, 0);
v_res_3430_ = lean_ctor_get(v___x_3428_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3432_ = v___x_3428_;
v_isShared_3433_ = v_isSharedCheck_3482_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_res_3430_);
lean_inc(v_pos_3429_);
lean_dec(v___x_3428_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3482_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_array_3434_; lean_object* v_idx_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3481_; 
v_array_3434_ = lean_ctor_get(v_pos_3429_, 0);
v_idx_3435_ = lean_ctor_get(v_pos_3429_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_pos_3429_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3437_ = v_pos_3429_;
v_isShared_3438_ = v_isSharedCheck_3481_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_idx_3435_);
lean_inc(v_array_3434_);
lean_dec(v_pos_3429_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3481_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3439_ = lean_byte_array_size(v_array_3434_);
v___x_3440_ = lean_nat_dec_lt(v_idx_3435_, v___x_3439_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
lean_del_object(v___x_3437_);
lean_dec(v_idx_3435_);
lean_dec_ref(v_array_3434_);
lean_dec(v_res_3430_);
v___x_3441_ = lean_box(0);
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 1);
lean_ctor_set(v___x_3432_, 1, v___x_3441_);
lean_ctor_set(v___x_3432_, 0, v_a_3427_);
v___x_3443_ = v___x_3432_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3427_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
else
{
uint8_t v___x_3445_; uint8_t v_c_3446_; uint8_t v___x_3447_; 
v___x_3445_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v_c_3446_ = lean_byte_array_fget(v_array_3434_, v_idx_3435_);
v___x_3447_ = lean_uint8_dec_eq(v_c_3446_, v___x_3445_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_del_object(v___x_3437_);
lean_dec(v_idx_3435_);
lean_dec_ref(v_array_3434_);
lean_dec(v_res_3430_);
v___x_3448_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 1);
lean_ctor_set(v___x_3432_, 1, v___x_3448_);
lean_ctor_set(v___x_3432_, 0, v_a_3427_);
v___x_3450_ = v___x_3432_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3427_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v_it_x27_3455_; 
lean_del_object(v___x_3432_);
v___x_3452_ = lean_unsigned_to_nat(1u);
v___x_3453_ = lean_nat_add(v_idx_3435_, v___x_3452_);
lean_dec(v_idx_3435_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v___x_3453_);
v_it_x27_3455_ = v___x_3437_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_array_3434_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3453_);
v_it_x27_3455_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; 
v___x_3456_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v_it_x27_3455_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_pos_3457_; lean_object* v_res_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref(v_a_3427_);
v_pos_3457_ = lean_ctor_get(v___x_3456_, 0);
v_res_3458_ = lean_ctor_get(v___x_3456_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3460_ = v___x_3456_;
v_isShared_3461_ = v_isSharedCheck_3470_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_res_3458_);
lean_inc(v_pos_3457_);
lean_dec(v___x_3456_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3470_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; uint16_t v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3462_ = lean_box(0);
v___x_3463_ = lean_alloc_ctor(2, 0, 2);
v___x_3464_ = lean_unbox(v_res_3458_);
lean_dec(v_res_3458_);
lean_ctor_set_uint16(v___x_3463_, 0, v___x_3464_);
v___x_3465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3462_);
lean_ctor_set(v___x_3465_, 1, v_res_3430_);
lean_ctor_set(v___x_3465_, 2, v___x_3463_);
v___x_3466_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v___x_3466_);
v___x_3468_ = v___x_3460_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_pos_3457_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
else
{
lean_object* v_err_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_res_3430_);
v_err_3471_ = lean_ctor_get(v___x_3456_, 1);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v___x_3456_, 0);
lean_dec(v_unused_3479_);
v___x_3473_ = v___x_3456_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_err_3471_);
lean_dec(v___x_3456_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
lean_ctor_set(v___x_3473_, 0, v_a_3427_);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3427_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_err_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
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
lean_object* v_err_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
v_err_3483_ = lean_ctor_get(v___x_3428_, 1);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3491_);
v___x_3485_ = v___x_3428_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_err_3483_);
lean_dec(v___x_3428_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v_a_3427_);
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3427_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_err_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority___boxed(lean_object* v_config_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3492_, v_a_3493_);
lean_dec_ref(v_config_3492_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseRequestTarget(lean_object* v_config_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v___x_3497_; 
lean_inc_ref(v_a_3496_);
v___x_3497_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_asterisk(v_a_3496_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_dec_ref(v_a_3496_);
lean_dec_ref(v_config_3495_);
return v___x_3497_;
}
else
{
lean_object* v_pos_3498_; lean_object* v_idx_3499_; lean_object* v_idx_3500_; uint8_t v___x_3501_; 
v_pos_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_pos_3498_);
v_idx_3499_ = lean_ctor_get(v_a_3496_, 1);
lean_inc(v_idx_3499_);
lean_dec_ref(v_a_3496_);
v_idx_3500_ = lean_ctor_get(v_pos_3498_, 1);
lean_inc(v_idx_3500_);
v___x_3501_ = lean_nat_dec_eq(v_idx_3499_, v_idx_3500_);
lean_dec(v_idx_3499_);
if (v___x_3501_ == 0)
{
lean_dec(v_idx_3500_);
lean_dec(v_pos_3498_);
lean_dec_ref(v_config_3495_);
return v___x_3497_;
}
else
{
lean_object* v___x_3502_; 
lean_dec_ref(v___x_3497_);
lean_inc_ref(v_config_3495_);
v___x_3502_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_origin(v_config_3495_, v_pos_3498_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_dec(v_idx_3500_);
lean_dec_ref(v_config_3495_);
return v___x_3502_;
}
else
{
lean_object* v_pos_3503_; lean_object* v_idx_3504_; uint8_t v___x_3505_; 
v_pos_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_pos_3503_);
v_idx_3504_ = lean_ctor_get(v_pos_3503_, 1);
lean_inc(v_idx_3504_);
v___x_3505_ = lean_nat_dec_eq(v_idx_3500_, v_idx_3504_);
lean_dec(v_idx_3500_);
if (v___x_3505_ == 0)
{
lean_dec(v_idx_3504_);
lean_dec(v_pos_3503_);
lean_dec_ref(v_config_3495_);
return v___x_3502_;
}
else
{
lean_object* v___x_3506_; 
lean_dec_ref(v___x_3502_);
lean_inc_ref(v_config_3495_);
v___x_3506_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absoluteHttp(v_config_3495_, v_pos_3503_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_dec(v_idx_3504_);
lean_dec_ref(v_config_3495_);
return v___x_3506_;
}
else
{
lean_object* v_pos_3507_; lean_object* v_idx_3508_; uint8_t v___x_3509_; 
v_pos_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_pos_3507_);
v_idx_3508_ = lean_ctor_get(v_pos_3507_, 1);
lean_inc(v_idx_3508_);
v___x_3509_ = lean_nat_dec_eq(v_idx_3504_, v_idx_3508_);
lean_dec(v_idx_3504_);
if (v___x_3509_ == 0)
{
lean_dec(v_idx_3508_);
lean_dec(v_pos_3507_);
lean_dec_ref(v_config_3495_);
return v___x_3506_;
}
else
{
lean_object* v___x_3510_; 
lean_dec_ref(v___x_3506_);
v___x_3510_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_authority(v_config_3495_, v_pos_3507_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_dec(v_idx_3508_);
lean_dec_ref(v_config_3495_);
return v___x_3510_;
}
else
{
lean_object* v_pos_3511_; lean_object* v_idx_3512_; uint8_t v___x_3513_; 
v_pos_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_pos_3511_);
v_idx_3512_ = lean_ctor_get(v_pos_3511_, 1);
v___x_3513_ = lean_nat_dec_eq(v_idx_3508_, v_idx_3512_);
lean_dec(v_idx_3508_);
if (v___x_3513_ == 0)
{
lean_dec(v_pos_3511_);
lean_dec_ref(v_config_3495_);
return v___x_3510_;
}
else
{
lean_object* v___x_3514_; 
lean_dec_ref(v___x_3510_);
v___x_3514_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseRequestTarget_absolute(v_config_3495_, v_pos_3511_);
return v___x_3514_;
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
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object* v_config_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v___y_3524_; lean_object* v___x_3527_; 
v___x_3527_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseHost(v_config_3521_, v_a_3522_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_pos_3528_; lean_object* v_res_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3602_; 
v_pos_3528_ = lean_ctor_get(v___x_3527_, 0);
v_res_3529_ = lean_ctor_get(v___x_3527_, 1);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3531_ = v___x_3527_;
v_isShared_3532_ = v_isSharedCheck_3602_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_res_3529_);
lean_inc(v_pos_3528_);
lean_dec(v___x_3527_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3602_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_port_3534_; lean_object* v___y_3535_; lean_object* v_pos_3549_; lean_object* v_array_3551_; lean_object* v_idx_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; lean_object* v___y_3556_; lean_object* v_array_3557_; lean_object* v_idx_3558_; 
v_array_3551_ = lean_ctor_get(v_pos_3528_, 0);
v_idx_3552_ = lean_ctor_get(v_pos_3528_, 1);
v___x_3553_ = lean_byte_array_size(v_array_3551_);
v___x_3554_ = lean_nat_dec_lt(v_idx_3552_, v___x_3553_);
if (v___x_3554_ == 0)
{
v_pos_3549_ = v_pos_3528_;
goto v___jp_3548_;
}
else
{
uint8_t v___x_3562_; uint8_t v___x_3563_; uint8_t v___x_3564_; 
v___x_3562_ = lean_byte_array_fget(v_array_3551_, v_idx_3552_);
v___x_3563_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseUserInfo___lam__0___closed__0);
v___x_3564_ = lean_uint8_dec_eq(v___x_3562_, v___x_3563_);
if (v___x_3564_ == 0)
{
v_pos_3549_ = v_pos_3528_;
goto v___jp_3548_;
}
else
{
if (v___x_3564_ == 0)
{
v_pos_3549_ = v_pos_3528_;
goto v___jp_3548_;
}
else
{
if (v___x_3554_ == 0)
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_del_object(v___x_3531_);
lean_dec(v_res_3529_);
v___x_3565_ = lean_box(0);
v___x_3566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3566_, 0, v_pos_3528_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
return v___x_3566_;
}
else
{
if (v___x_3564_ == 0)
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_del_object(v___x_3531_);
lean_dec(v_res_3529_);
v___x_3567_ = lean_obj_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseAuthority___closed__9);
v___x_3568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3568_, 0, v_pos_3528_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
return v___x_3568_;
}
else
{
lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3599_; 
lean_inc(v_idx_3552_);
lean_inc_ref(v_array_3551_);
v_isSharedCheck_3599_ = !lean_is_exclusive(v_pos_3528_);
if (v_isSharedCheck_3599_ == 0)
{
lean_object* v_unused_3600_; lean_object* v_unused_3601_; 
v_unused_3600_ = lean_ctor_get(v_pos_3528_, 1);
lean_dec(v_unused_3600_);
v_unused_3601_ = lean_ctor_get(v_pos_3528_, 0);
lean_dec(v_unused_3601_);
v___x_3570_ = v_pos_3528_;
v_isShared_3571_ = v_isSharedCheck_3599_;
goto v_resetjp_3569_;
}
else
{
lean_dec(v_pos_3528_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3599_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v_it_x27_3575_; 
v___x_3572_ = lean_unsigned_to_nat(1u);
v___x_3573_ = lean_nat_add(v_idx_3552_, v___x_3572_);
lean_dec(v_idx_3552_);
lean_inc(v___x_3573_);
lean_inc_ref(v_array_3551_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v___x_3573_);
v_it_x27_3575_ = v___x_3570_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_array_3551_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v___x_3573_);
v_it_x27_3575_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
uint8_t v___y_3577_; uint8_t v___x_3592_; 
v___x_3592_ = lean_nat_dec_lt(v___x_3573_, v___x_3553_);
if (v___x_3592_ == 0)
{
v___y_3556_ = v_it_x27_3575_;
v_array_3557_ = v_array_3551_;
v_idx_3558_ = v___x_3573_;
goto v___jp_3555_;
}
else
{
uint8_t v___x_3593_; uint8_t v___x_3594_; uint8_t v___x_3595_; 
v___x_3593_ = lean_byte_array_fget(v_array_3551_, v___x_3573_);
v___x_3594_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__3);
v___x_3595_ = lean_uint8_dec_le(v___x_3594_, v___x_3593_);
if (v___x_3595_ == 0)
{
v___y_3577_ = v___x_3595_;
goto v___jp_3576_;
}
else
{
uint8_t v___x_3596_; uint8_t v___x_3597_; 
v___x_3596_ = lean_uint8_once(&l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4, &l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4_once, _init_l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parseScheme___lam__1___closed__4);
v___x_3597_ = lean_uint8_dec_le(v___x_3593_, v___x_3596_);
v___y_3577_ = v___x_3597_;
goto v___jp_3576_;
}
}
v___jp_3576_:
{
if (v___y_3577_ == 0)
{
v___y_3556_ = v_it_x27_3575_;
v_array_3557_ = v_array_3551_;
v_idx_3558_ = v___x_3573_;
goto v___jp_3555_;
}
else
{
if (v___x_3554_ == 0)
{
v___y_3556_ = v_it_x27_3575_;
v_array_3557_ = v_array_3551_;
v_idx_3558_ = v___x_3573_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3578_; 
lean_dec(v___x_3573_);
lean_dec_ref(v_array_3551_);
v___x_3578_ = l___private_Std_Internal_Http_Data_URI_Parser_0__Std_Http_URI_Parser_parsePortNumber(v_it_x27_3575_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_pos_3579_; lean_object* v_res_3580_; lean_object* v___x_3581_; uint16_t v___x_3582_; 
v_pos_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_pos_3579_);
v_res_3580_ = lean_ctor_get(v___x_3578_, 1);
lean_inc(v_res_3580_);
lean_dec_ref(v___x_3578_);
v___x_3581_ = lean_alloc_ctor(2, 0, 2);
v___x_3582_ = lean_unbox(v_res_3580_);
lean_dec(v_res_3580_);
lean_ctor_set_uint16(v___x_3581_, 0, v___x_3582_);
v_port_3534_ = v___x_3581_;
v___y_3535_ = v_pos_3579_;
goto v___jp_3533_;
}
else
{
lean_object* v_pos_3583_; lean_object* v_err_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3531_);
lean_dec(v_res_3529_);
v_pos_3583_ = lean_ctor_get(v___x_3578_, 0);
v_err_3584_ = lean_ctor_get(v___x_3578_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3578_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_err_3584_);
lean_inc(v_pos_3583_);
lean_dec(v___x_3578_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_pos_3583_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_err_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
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
v___jp_3533_:
{
lean_object* v_array_3536_; lean_object* v_idx_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v_array_3536_ = lean_ctor_get(v___y_3535_, 0);
v_idx_3537_ = lean_ctor_get(v___y_3535_, 1);
v___x_3538_ = lean_byte_array_size(v_array_3536_);
v___x_3539_ = lean_nat_dec_lt(v_idx_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3540_, 0, v_res_3529_);
lean_ctor_set(v___x_3540_, 1, v_port_3534_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 1, v___x_3540_);
lean_ctor_set(v___x_3531_, 0, v___y_3535_);
v___x_3542_ = v___x_3531_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___y_3535_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
else
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
lean_dec(v_port_3534_);
lean_dec(v_res_3529_);
v___x_3544_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__3));
if (v_isShared_3532_ == 0)
{
lean_ctor_set_tag(v___x_3531_, 1);
lean_ctor_set(v___x_3531_, 1, v___x_3544_);
lean_ctor_set(v___x_3531_, 0, v___y_3535_);
v___x_3546_ = v___x_3531_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___y_3535_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
v___jp_3548_:
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_box(0);
v_port_3534_ = v___x_3550_;
v___y_3535_ = v_pos_3549_;
goto v___jp_3533_;
}
v___jp_3555_:
{
lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3559_ = lean_byte_array_size(v_array_3557_);
lean_dec_ref(v_array_3557_);
v___x_3560_ = lean_nat_dec_lt(v_idx_3558_, v___x_3559_);
lean_dec(v_idx_3558_);
if (v___x_3560_ == 0)
{
if (v___x_3554_ == 0)
{
lean_del_object(v___x_3531_);
lean_dec(v_res_3529_);
v___y_3524_ = v___y_3556_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_box(1);
v_port_3534_ = v___x_3561_;
v___y_3535_ = v___y_3556_;
goto v___jp_3533_;
}
}
else
{
lean_del_object(v___x_3531_);
lean_dec(v_res_3529_);
v___y_3524_ = v___y_3556_;
goto v___jp_3523_;
}
}
}
}
else
{
lean_object* v_pos_3603_; lean_object* v_err_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v_pos_3603_ = lean_ctor_get(v___x_3527_, 0);
v_err_3604_ = lean_ctor_get(v___x_3527_, 1);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3527_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_err_3604_);
lean_inc(v_pos_3603_);
lean_dec(v___x_3527_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_pos_3603_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_err_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
v___jp_3523_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = ((lean_object*)(l_Std_Http_URI_Parser_parseHostHeader___closed__1));
v___x_3526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___y_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
return v___x_3526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_URI_Parser_parseHostHeader___boxed(lean_object* v_config_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Std_Http_URI_Parser_parseHostHeader(v_config_3612_, v_a_3613_);
lean_dec_ref(v_config_3612_);
return v_res_3614_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Config(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_ByteArray(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_URI_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_URI_Config(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_URI_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_URI_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_URI_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_URI_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_URI_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_URI_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
