// Lean compiler output
// Module: Lake.Util.Version
// Imports: public import Lean.Data.Json public import Lake.Util.Date public import Init.Control.Do import Init.Data.String.TakeDrop import Lean.Data.Trie import Init.Data.String.Search import Init.Omega import Init.Data.String.Length
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_String_compare(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_String_Slice_beq(lean_object*, lean_object*);
lean_object* l_Lake_Date_toString(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Date_ofString_x3f(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lake_instReprDate_repr___redArg(lean_object*);
uint8_t l_Lake_instDecidableEqDate_decEq(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t l_String_decLE(lean_object*, lean_object*);
uint8_t l_Lake_instOrdDate_ord(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_Version_0__Lake_isWildVer(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_isWildVer___boxed(lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "invalid "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = " version: expected numeral, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = " version: expected numeral or wildcard, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "invalid version: '-' suffix cannot be empty"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "unexpected characters at end of version: "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_instInhabitedSemVerCore_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedSemVerCore_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedSemVerCore_default = (const lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedSemVerCore = (const lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprSemVerCore_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "major"};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprSemVerCore_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "minor"};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__11_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "patch"};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__12_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__13_value;
static const lean_string_object l_Lake_instReprSemVerCore_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lake_instReprSemVerCore_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__15;
static lean_once_cell_t l_Lake_instReprSemVerCore_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__16;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lake_instReprSemVerCore_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__14_value)}};
static const lean_object* l_Lake_instReprSemVerCore_repr___redArg___closed__18 = (const lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprSemVerCore_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprSemVerCore___closed__0 = (const lean_object*)&l_Lake_instReprSemVerCore___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprSemVerCore = (const lean_object*)&l_Lake_instReprSemVerCore___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instOrdSemVerCore_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdSemVerCore_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instOrdSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instOrdSemVerCore_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instOrdSemVerCore___closed__0 = (const lean_object*)&l_Lake_instOrdSemVerCore___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instOrdSemVerCore = (const lean_object*)&l_Lake_instOrdSemVerCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instLT;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instLE;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instMin___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instMin = (const lean_object*)&l_Lake_SemVerCore_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instMax___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instMax = (const lean_object*)&l_Lake_SemVerCore_instMax___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid version core: "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "incorrect number of components: got "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ", expected 3"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid patch version: expected numeral, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid minor version: expected numeral, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid major version: expected numeral, got '"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(lean_object*, lean_object*);
static const lean_closure_object l_Lake_SemVerCore_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_parse___closed__0 = (const lean_object*)&l_Lake_SemVerCore_parse___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_parse(lean_object*);
static const lean_string_object l_Lake_SemVerCore_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_SemVerCore_toString___closed__0 = (const lean_object*)&l_Lake_SemVerCore_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_toString(lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instToString___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instToString = (const lean_object*)&l_Lake_SemVerCore_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instToJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_instToJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instToJson___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instToJson = (const lean_object*)&l_Lake_SemVerCore_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instFromJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_SemVerCore_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_instFromJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_SemVerCore_instFromJson___closed__0 = (const lean_object*)&l_Lake_SemVerCore_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_SemVerCore_instFromJson = (const lean_object*)&l_Lake_SemVerCore_instFromJson___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedStdVer_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value),((lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value)}};
static const lean_object* l_Lake_instInhabitedStdVer_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedStdVer_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedStdVer_default = (const lean_object*)&l_Lake_instInhabitedStdVer_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedStdVer = (const lean_object*)&l_Lake_instInhabitedStdVer_default___closed__0_value;
static const lean_string_object l_Lake_instReprStdVer_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toSemVerCore"};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprStdVer_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprStdVer_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprStdVer_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprStdVer_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprStdVer_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprStdVer_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "specialDescr"};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprStdVer_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprStdVer_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprStdVer_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprStdVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprStdVer_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprStdVer___closed__0 = (const lean_object*)&l_Lake_instReprStdVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprStdVer = (const lean_object*)&l_Lake_instReprStdVer___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_StdVer_instCoeSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instCoeSemVerCore___closed__0 = (const lean_object*)&l_Lake_StdVer_instCoeSemVerCore___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instCoeSemVerCore = (const lean_object*)&l_Lake_StdVer_instCoeSemVerCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_ofSemVerCore(lean_object*);
static const lean_closure_object l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_ofSemVerCore, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instCoeSemVerCore__1___closed__0 = (const lean_object*)&l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instCoeSemVerCore__1 = (const lean_object*)&l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_StdVer_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_StdVer_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instOrd___closed__0 = (const lean_object*)&l_Lake_StdVer_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instOrd = (const lean_object*)&l_Lake_StdVer_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_instLT;
LEAN_EXPORT lean_object* l_Lake_StdVer_instLE;
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_StdVer_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instMin___closed__0 = (const lean_object*)&l_Lake_StdVer_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instMin = (const lean_object*)&l_Lake_StdVer_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_StdVer_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instMax___closed__0 = (const lean_object*)&l_Lake_StdVer_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instMax = (const lean_object*)&l_Lake_StdVer_instMax___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_parseM(lean_object*, lean_object*);
static const lean_closure_object l_Lake_StdVer_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_parse___closed__0 = (const lean_object*)&l_Lake_StdVer_parse___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_parse(lean_object*);
static const lean_string_object l_Lake_StdVer_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_StdVer_toString___closed__0 = (const lean_object*)&l_Lake_StdVer_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_toString(lean_object*);
static const lean_closure_object l_Lake_StdVer_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instToString___closed__0 = (const lean_object*)&l_Lake_StdVer_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instToString = (const lean_object*)&l_Lake_StdVer_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_instToJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_StdVer_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instToJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instToJson___closed__0 = (const lean_object*)&l_Lake_StdVer_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instToJson = (const lean_object*)&l_Lake_StdVer_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_StdVer_instFromJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_StdVer_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_instFromJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_StdVer_instFromJson___closed__0 = (const lean_object*)&l_Lake_StdVer_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_StdVer_instFromJson = (const lean_object*)&l_Lake_StdVer_instFromJson___closed__0_value;
static const lean_string_object l_Lake_toolchainFileName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lean-toolchain"};
static const lean_object* l_Lake_toolchainFileName___closed__0 = (const lean_object*)&l_Lake_toolchainFileName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_toolchainFileName = (const lean_object*)&l_Lake_toolchainFileName___closed__0_value;
static const lean_string_object l_Lake_ToolchainVer_defaultOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "leanprover/lean4"};
static const lean_object* l_Lake_ToolchainVer_defaultOrigin___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_defaultOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_defaultOrigin = (const lean_object*)&l_Lake_ToolchainVer_defaultOrigin___closed__0_value;
static const lean_string_object l_Lake_ToolchainVer_prOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "leanprover/lean4-pr-releases"};
static const lean_object* l_Lake_ToolchainVer_prOrigin___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_prOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_prOrigin = (const lean_object*)&l_Lake_ToolchainVer_prOrigin___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ToolchainVer_release___override___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "leanprover/lean4:v"};
static const lean_object* l_Lake_ToolchainVer_release___override___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_release___override___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release___override(lean_object*);
static const lean_string_object l_Lake_ToolchainVer_nightly___override___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "leanprover/lean4:nightly-"};
static const lean_object* l_Lake_ToolchainVer_nightly___override___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_nightly___override___closed__0_value;
static const lean_string_object l_Lake_ToolchainVer_nightly___override___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "-rev"};
static const lean_object* l_Lake_ToolchainVer_nightly___override___closed__1 = (const lean_object*)&l_Lake_ToolchainVer_nightly___override___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly___override(lean_object*, lean_object*);
static const lean_string_object l_Lake_ToolchainVer_pr___override___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "leanprover/lean4-pr-releases:pr-release-"};
static const lean_object* l_Lake_ToolchainVer_pr___override___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_pr___override___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr___override(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other___override(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override___boxed(lean_object*);
static const lean_string_object l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprToolchainVer_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lake.ToolchainVer.release"};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__0 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__1 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__1_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__2 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__2_value;
static lean_once_cell_t l_Lake_instReprToolchainVer_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprToolchainVer_repr___closed__3;
static lean_once_cell_t l_Lake_instReprToolchainVer_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprToolchainVer_repr___closed__4;
static const lean_string_object l_Lake_instReprToolchainVer_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lake.ToolchainVer.nightly"};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__5 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__5_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__5_value)}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__6 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__7 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__7_value;
static const lean_string_object l_Lake_instReprToolchainVer_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ToolchainVer.pr"};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__8 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__9 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__9_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__10 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__10_value;
static const lean_string_object l_Lake_instReprToolchainVer_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lake.ToolchainVer.other"};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__11 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__11_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__11_value)}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__12 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__12_value;
static const lean_ctor_object l_Lake_instReprToolchainVer_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprToolchainVer_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprToolchainVer_repr___closed__13 = (const lean_object*)&l_Lake_instReprToolchainVer_repr___closed__13_value;
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprToolchainVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprToolchainVer_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprToolchainVer___closed__0 = (const lean_object*)&l_Lake_instReprToolchainVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprToolchainVer = (const lean_object*)&l_Lake_instReprToolchainVer___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ToolchainVer_release___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ToolchainVer_instCoeLeanVer___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_instCoeLeanVer = (const lean_object*)&l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value;
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "nightly-"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pr-release-"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ToolchainVer_ofString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "-nightly"};
static const lean_object* l_Lake_ToolchainVer_ofString___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_ofString___closed__0_value;
static lean_once_cell_t l_Lake_ToolchainVer_ofString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ToolchainVer_ofString___closed__1;
static lean_once_cell_t l_Lake_ToolchainVer_ofString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ToolchainVer_ofString___closed__2;
static const lean_string_object l_Lake_ToolchainVer_ofString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l_Lake_ToolchainVer_ofString___closed__3 = (const lean_object*)&l_Lake_ToolchainVer_ofString___closed__3_value;
static lean_once_cell_t l_Lake_ToolchainVer_ofString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_ToolchainVer_ofString___closed__4;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_ToolchainVer_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ToolchainVer_toString___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ToolchainVer_instToString___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_instToString = (const lean_object*)&l_Lake_ToolchainVer_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_ToolchainVer_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ToolchainVer_instToJson___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ToolchainVer_instToJson___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_instToJson = (const lean_object*)&l_Lake_ToolchainVer_instToJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instFromJson___lam__0(lean_object*);
static const lean_closure_object l_Lake_ToolchainVer_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ToolchainVer_instFromJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ToolchainVer_instFromJson___closed__0 = (const lean_object*)&l_Lake_ToolchainVer_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ToolchainVer_instFromJson = (const lean_object*)&l_Lake_ToolchainVer_instFromJson___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instLT;
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_ble(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instLE;
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object*);
static const lean_closure_object l_Lake_instDecodeVersionSemVerCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_SemVerCore_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instDecodeVersionSemVerCore___closed__0 = (const lean_object*)&l_Lake_instDecodeVersionSemVerCore___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instDecodeVersionSemVerCore = (const lean_object*)&l_Lake_instDecodeVersionSemVerCore___closed__0_value;
static const lean_closure_object l_Lake_instDecodeVersionStdVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_StdVer_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instDecodeVersionStdVer___closed__0 = (const lean_object*)&l_Lake_instDecodeVersionStdVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instDecodeVersionStdVer = (const lean_object*)&l_Lake_instDecodeVersionStdVer___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object*);
static const lean_closure_object l_Lake_instDecodeVersionToolchainVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instDecodeVersionToolchainVer___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instDecodeVersionToolchainVer___closed__0 = (const lean_object*)&l_Lake_instDecodeVersionToolchainVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instDecodeVersionToolchainVer = (const lean_object*)&l_Lake_instDecodeVersionToolchainVer___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.lt"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__0 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__1 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__1_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.le"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__2 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__3 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__3_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.gt"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__4 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__5 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__5_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.ge"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__6 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__7 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__7_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.eq"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__8 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__9 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__9_value;
static const lean_string_object l_Lake_instReprComparatorOp_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.ComparatorOp.ne"};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__10 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__10_value;
static const lean_ctor_object l_Lake_instReprComparatorOp_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprComparatorOp_repr___closed__10_value)}};
static const lean_object* l_Lake_instReprComparatorOp_repr___closed__11 = (const lean_object*)&l_Lake_instReprComparatorOp_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprComparatorOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprComparatorOp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprComparatorOp___closed__0 = (const lean_object*)&l_Lake_instReprComparatorOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprComparatorOp = (const lean_object*)&l_Lake_instReprComparatorOp___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instInhabitedComparatorOp_default;
LEAN_EXPORT uint8_t l_Lake_instInhabitedComparatorOp;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≠"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!="};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≥"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ">="};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "<="};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8_value;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17;
static lean_once_cell_t l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "(internal) comparison operator parse produced invalid position"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "expected comparison operator"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_ComparatorOp_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_ComparatorOp_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_ComparatorOp_instToString___closed__0 = (const lean_object*)&l_Lake_ComparatorOp_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_ComparatorOp_instToString = (const lean_object*)&l_Lake_ComparatorOp_instToString___closed__0_value;
static const lean_string_object l_Lake_instReprVerComparator_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ver"};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprVerComparator_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprVerComparator_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "op"};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprVerComparator_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprVerComparator_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "includeSuffixes"};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprVerComparator_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprVerComparator_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lake_instReprVerComparator_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerComparator_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprVerComparator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprVerComparator_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprVerComparator___closed__0 = (const lean_object*)&l_Lake_instReprVerComparator___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprVerComparator = (const lean_object*)&l_Lake_instReprVerComparator___closed__0_value;
static const lean_ctor_object l_Lake_VerComparator_wild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedSemVerCore_default___closed__0_value),((lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value)}};
static const lean_object* l_Lake_VerComparator_wild___closed__0 = (const lean_object*)&l_Lake_VerComparator_wild___closed__0_value;
static const lean_ctor_object l_Lake_VerComparator_wild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_VerComparator_wild___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_VerComparator_wild___closed__1 = (const lean_object*)&l_Lake_VerComparator_wild___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_VerComparator_wild = (const lean_object*)&l_Lake_VerComparator_wild___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_VerComparator_instInhabited = (const lean_object*)&l_Lake_VerComparator_wild___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object*, lean_object*);
static const lean_closure_object l_Lake_VerComparator_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_VerComparator_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerComparator_parse___closed__0 = (const lean_object*)&l_Lake_VerComparator_parse___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object*);
LEAN_EXPORT uint8_t l_Lake_VerComparator_test(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object*);
static const lean_closure_object l_Lake_VerComparator_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_VerComparator_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerComparator_instToString___closed__0 = (const lean_object*)&l_Lake_VerComparator_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_VerComparator_instToString = (const lean_object*)&l_Lake_VerComparator_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprVerRange_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lake_instReprVerRange_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprVerRange_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprVerRange_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__2_value),((lean_object*)&l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lake_instReprVerRange_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerRange_repr___redArg___closed__4;
static const lean_string_object l_Lake_instReprVerRange_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "clauses"};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprVerRange_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprVerRange_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprVerRange_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprVerRange_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprVerRange_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprVerRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprVerRange_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprVerRange___closed__0 = (const lean_object*)&l_Lake_instReprVerRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprVerRange = (const lean_object*)&l_Lake_instReprVerRange___closed__0_value;
static const lean_array_object l_Lake_instInhabitedVerRange_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedVerRange_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedVerRange_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedVerRange_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value),((lean_object*)&l_Lake_instInhabitedVerRange_default___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedVerRange_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedVerRange_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedVerRange_default = (const lean_object*)&l_Lake_instInhabitedVerRange_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedVerRange = (const lean_object*)&l_Lake_instInhabitedVerRange_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_VerRange_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_VerRange_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerRange_instToString___closed__0 = (const lean_object*)&l_Lake_VerRange_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_VerRange_instToString = (const lean_object*)&l_Lake_VerRange_instToString___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<empty>"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " || "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "invalid tilde range: incorrect number of components: got "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ", expected 1-3"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "invalid caret range: incorrect number of components: got "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "invalid caret range: `^0.0.0` is degenerate; use `=0.0.0` instead"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = "invalid version range: bare versions are not supported; if you want to pin a specific version, use '=' before the full version; otherwise, use '≥' to support it and future versions"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "invalid patch version: components after a wildcard must be wildcards"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "invalid minor version: components after a wildcard must be wildcards"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "invalid wildcard range: incorrect number of components: got "};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "invalid wildcard range: wildcard versions do not support suffixes"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "expected version range"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0_value;
static const lean_string_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "expected '|' after first '|'"};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1_value;
static const lean_array_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0 = (const lean_object*)&l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object*, lean_object*);
static const lean_closure_object l_Lake_VerRange_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Util_Version_0__Lake_VerRange_parseM, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_VerRange_parse___closed__0 = (const lean_object*)&l_Lake_VerRange_parse___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_VerRange_test(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(lean_object* v_s_1_, lean_object* v_cs_2_, lean_object* v_iniPos_3_, lean_object* v_p_4_){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_string_utf8_byte_size(v_s_1_);
v___x_9_ = lean_nat_dec_eq(v_p_4_, v___x_8_);
if (v___x_9_ == 0)
{
uint32_t v_c_10_; uint8_t v___y_12_; uint8_t v___y_19_; uint32_t v___x_29_; uint8_t v___x_30_; 
v_c_10_ = lean_string_utf8_get_fast(v_s_1_, v_p_4_);
v___x_29_ = 46;
v___x_30_ = lean_uint32_dec_eq(v_c_10_, v___x_29_);
if (v___x_30_ == 0)
{
uint32_t v___x_31_; uint8_t v___x_32_; 
v___x_31_ = 65;
v___x_32_ = lean_uint32_dec_le(v___x_31_, v_c_10_);
if (v___x_32_ == 0)
{
goto v___jp_24_;
}
else
{
uint32_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = 90;
v___x_34_ = lean_uint32_dec_le(v_c_10_, v___x_33_);
if (v___x_34_ == 0)
{
goto v___jp_24_;
}
else
{
goto v___jp_5_;
}
}
}
else
{
lean_object* v_c_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_inc(v_p_4_);
lean_inc_ref(v_s_1_);
v_c_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_35_, 0, v_s_1_);
lean_ctor_set(v_c_35_, 1, v_iniPos_3_);
lean_ctor_set(v_c_35_, 2, v_p_4_);
v___x_36_ = lean_array_push(v_cs_2_, v_c_35_);
v___x_37_ = lean_string_utf8_next_fast(v_s_1_, v_p_4_);
lean_dec(v_p_4_);
v_cs_2_ = v___x_36_;
v_iniPos_3_ = v___x_37_;
v_p_4_ = v___x_37_;
goto _start;
}
v___jp_11_:
{
if (v___y_12_ == 0)
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 42;
v___x_14_ = lean_uint32_dec_eq(v_c_10_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v_c_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
lean_inc(v_p_4_);
v_c_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_15_, 0, v_s_1_);
lean_ctor_set(v_c_15_, 1, v_iniPos_3_);
lean_ctor_set(v_c_15_, 2, v_p_4_);
v___x_16_ = lean_array_push(v_cs_2_, v_c_15_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_p_4_);
return v___x_17_;
}
else
{
goto v___jp_5_;
}
}
else
{
goto v___jp_5_;
}
}
v___jp_18_:
{
if (v___y_19_ == 0)
{
uint32_t v___x_20_; uint8_t v___x_21_; 
v___x_20_ = 48;
v___x_21_ = lean_uint32_dec_le(v___x_20_, v_c_10_);
if (v___x_21_ == 0)
{
v___y_12_ = v___x_21_;
goto v___jp_11_;
}
else
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = 57;
v___x_23_ = lean_uint32_dec_le(v_c_10_, v___x_22_);
v___y_12_ = v___x_23_;
goto v___jp_11_;
}
}
else
{
goto v___jp_5_;
}
}
v___jp_24_:
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 97;
v___x_26_ = lean_uint32_dec_le(v___x_25_, v_c_10_);
if (v___x_26_ == 0)
{
v___y_19_ = v___x_26_;
goto v___jp_18_;
}
else
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 122;
v___x_28_ = lean_uint32_dec_le(v_c_10_, v___x_27_);
v___y_19_ = v___x_28_;
goto v___jp_18_;
}
}
}
else
{
lean_object* v_c_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc(v_p_4_);
v_c_39_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_c_39_, 0, v_s_1_);
lean_ctor_set(v_c_39_, 1, v_iniPos_3_);
lean_ctor_set(v_c_39_, 2, v_p_4_);
v___x_40_ = lean_array_push(v_cs_2_, v_c_39_);
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v_p_4_);
return v___x_41_;
}
v___jp_5_:
{
lean_object* v___x_6_; 
v___x_6_ = lean_string_utf8_next_fast(v_s_1_, v_p_4_);
lean_dec(v_p_4_);
v_p_4_ = v___x_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents_go(lean_object* v_s_42_, lean_object* v_cs_43_, lean_object* v_iniPos_44_, lean_object* v_p_45_, lean_object* v_iniPos__le_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_42_, v_cs_43_, v_iniPos_44_, v_p_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponents(lean_object* v_s_50_, lean_object* v_p_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_p_51_);
v___x_53_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_50_, v___x_52_, v_p_51_, v_p_51_);
return v___x_53_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Version_0__Lake_isWildVer(lean_object* v_s_54_){
_start:
{
lean_object* v_str_55_; lean_object* v_startInclusive_56_; lean_object* v_endExclusive_57_; lean_object* v_p_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v_str_55_ = lean_ctor_get(v_s_54_, 0);
v_startInclusive_56_ = lean_ctor_get(v_s_54_, 1);
v_endExclusive_57_ = lean_ctor_get(v_s_54_, 2);
v_p_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_nat_sub(v_endExclusive_57_, v_startInclusive_56_);
v___x_60_ = lean_nat_dec_eq(v_p_58_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_61_ = lean_string_utf8_next_fast(v_str_55_, v_startInclusive_56_);
v___x_62_ = lean_nat_sub(v___x_61_, v_startInclusive_56_);
v___x_63_ = lean_nat_dec_eq(v___x_62_, v___x_59_);
lean_dec(v___x_59_);
lean_dec(v___x_62_);
if (v___x_63_ == 0)
{
return v___x_63_;
}
else
{
uint32_t v_c_64_; uint8_t v___y_66_; uint32_t v___x_69_; uint8_t v___x_70_; 
v_c_64_ = lean_string_utf8_get_fast(v_str_55_, v_startInclusive_56_);
v___x_69_ = 120;
v___x_70_ = lean_uint32_dec_eq(v_c_64_, v___x_69_);
if (v___x_70_ == 0)
{
uint32_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 88;
v___x_72_ = lean_uint32_dec_eq(v_c_64_, v___x_71_);
v___y_66_ = v___x_72_;
goto v___jp_65_;
}
else
{
v___y_66_ = v___x_70_;
goto v___jp_65_;
}
v___jp_65_:
{
if (v___y_66_ == 0)
{
uint32_t v___x_67_; uint8_t v___x_68_; 
v___x_67_ = 42;
v___x_68_ = lean_uint32_dec_eq(v_c_64_, v___x_67_);
return v___x_68_;
}
else
{
return v___y_66_;
}
}
}
}
else
{
uint8_t v___x_73_; 
lean_dec(v___x_59_);
v___x_73_ = 0;
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_isWildVer___boxed(lean_object* v_s_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_s_74_);
lean_dec_ref(v_s_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(lean_object* v_what_80_, lean_object* v_s_81_, lean_object* v_a_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_String_Slice_toNat_x3f(v_s_81_);
if (lean_obj_tag(v___x_83_) == 1)
{
lean_object* v_val_84_; lean_object* v___x_85_; 
v_val_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_val_84_);
lean_dec_ref(v___x_83_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_val_84_);
lean_ctor_set(v___x_85_, 1, v_a_82_);
return v___x_85_;
}
else
{
lean_object* v_str_86_; lean_object* v_startInclusive_87_; lean_object* v_endExclusive_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
lean_dec(v___x_83_);
v_str_86_ = lean_ctor_get(v_s_81_, 0);
v_startInclusive_87_ = lean_ctor_get(v_s_81_, 1);
v_endExclusive_88_ = lean_ctor_get(v_s_81_, 2);
v___x_89_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_90_ = lean_string_append(v___x_89_, v_what_80_);
v___x_91_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1));
v___x_92_ = lean_string_append(v___x_90_, v___x_91_);
v___x_93_ = lean_string_utf8_extract(v_str_86_, v_startInclusive_87_, v_endExclusive_88_);
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
lean_dec_ref(v___x_93_);
v___x_95_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_96_ = lean_string_append(v___x_94_, v___x_95_);
v___x_97_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_a_82_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___boxed(lean_object* v_what_98_, lean_object* v_s_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(v_what_98_, v_s_99_, v_a_100_);
lean_dec_ref(v_s_99_);
lean_dec_ref(v_what_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat(lean_object* v_00_u03c3_102_, lean_object* v_what_103_, lean_object* v_s_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_String_Slice_toNat_x3f(v_s_104_);
if (lean_obj_tag(v___x_106_) == 1)
{
lean_object* v_val_107_; lean_object* v___x_108_; 
v_val_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_val_107_);
lean_dec_ref(v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_val_107_);
lean_ctor_set(v___x_108_, 1, v_a_105_);
return v___x_108_;
}
else
{
lean_object* v_str_109_; lean_object* v_startInclusive_110_; lean_object* v_endExclusive_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v___x_106_);
v_str_109_ = lean_ctor_get(v_s_104_, 0);
v_startInclusive_110_ = lean_ctor_get(v_s_104_, 1);
v_endExclusive_111_ = lean_ctor_get(v_s_104_, 2);
v___x_112_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_113_ = lean_string_append(v___x_112_, v_what_103_);
v___x_114_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1));
v___x_115_ = lean_string_append(v___x_113_, v___x_114_);
v___x_116_ = lean_string_utf8_extract(v_str_109_, v_startInclusive_110_, v_endExclusive_111_);
v___x_117_ = lean_string_append(v___x_115_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_a_105_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerNat___boxed(lean_object* v_00_u03c3_121_, lean_object* v_what_122_, lean_object* v_s_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lake_Util_Version_0__Lake_parseVerNat(v_00_u03c3_121_, v_what_122_, v_s_123_, v_a_124_);
lean_dec_ref(v_s_123_);
lean_dec_ref(v_what_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(lean_object* v_x_126_){
_start:
{
switch(lean_obj_tag(v_x_126_))
{
case 0:
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(0u);
return v___x_127_;
}
case 1:
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(1u);
return v___x_128_;
}
default: 
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(2u);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___boxed(lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(v_x_130_);
lean_dec(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(lean_object* v_t_132_, lean_object* v_k_133_){
_start:
{
if (lean_obj_tag(v_t_132_) == 2)
{
lean_object* v_n_134_; lean_object* v___x_135_; 
v_n_134_ = lean_ctor_get(v_t_132_, 0);
lean_inc(v_n_134_);
lean_dec_ref(v_t_132_);
v___x_135_ = lean_apply_1(v_k_133_, v_n_134_);
return v___x_135_;
}
else
{
lean_dec(v_t_132_);
return v_k_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_138_, v_k_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___boxed(lean_object* v_motive_142_, lean_object* v_ctorIdx_143_, lean_object* v_t_144_, lean_object* v_h_145_, lean_object* v_k_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(v_motive_142_, v_ctorIdx_143_, v_t_144_, v_h_145_, v_k_146_);
lean_dec(v_ctorIdx_143_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim___redArg(lean_object* v_t_148_, lean_object* v_none_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_148_, v_none_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_none_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_152_, v_none_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim___redArg(lean_object* v_t_156_, lean_object* v_wild_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_156_, v_wild_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim(lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_wild_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_160_, v_wild_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim___redArg(lean_object* v_t_164_, lean_object* v_nat_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_164_, v_nat_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim(lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_nat_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_168_, v_nat_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(lean_object* v_what_173_, lean_object* v_s_x3f_174_, lean_object* v_a_175_){
_start:
{
if (lean_obj_tag(v_s_x3f_174_) == 1)
{
lean_object* v_val_176_; uint8_t v___x_177_; 
v_val_176_ = lean_ctor_get(v_s_x3f_174_, 0);
v___x_177_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_val_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = l_String_Slice_toNat_x3f(v_val_176_);
if (lean_obj_tag(v___x_178_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_val_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 2);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_val_179_);
v___x_184_ = v_reuseFailAlloc_186_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_a_175_);
return v___x_185_;
}
}
}
else
{
lean_object* v_str_188_; lean_object* v_startInclusive_189_; lean_object* v_endExclusive_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v___x_178_);
v_str_188_ = lean_ctor_get(v_val_176_, 0);
v_startInclusive_189_ = lean_ctor_get(v_val_176_, 1);
v_endExclusive_190_ = lean_ctor_get(v_val_176_, 2);
v___x_191_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0));
v___x_192_ = lean_string_append(v___x_191_, v_what_173_);
v___x_193_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
v___x_195_ = lean_string_utf8_extract(v_str_188_, v_startInclusive_189_, v_endExclusive_190_);
v___x_196_ = lean_string_append(v___x_194_, v___x_195_);
lean_dec_ref(v___x_195_);
v___x_197_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_198_ = lean_string_append(v___x_196_, v___x_197_);
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v_a_175_);
return v___x_199_;
}
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_box(1);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_a_175_);
return v___x_201_;
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_box(0);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_a_175_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___boxed(lean_object* v_what_204_, lean_object* v_s_x3f_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v_what_204_, v_s_x3f_205_, v_a_206_);
lean_dec(v_s_x3f_205_);
lean_dec_ref(v_what_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent(lean_object* v_00_u03c3_208_, lean_object* v_what_209_, lean_object* v_s_x3f_210_, lean_object* v_a_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v_what_209_, v_s_x3f_210_, v_a_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseVerComponent___boxed(lean_object* v_00_u03c3_213_, lean_object* v_what_214_, lean_object* v_s_x3f_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent(v_00_u03c3_213_, v_what_214_, v_s_x3f_215_, v_a_216_);
lean_dec(v_s_x3f_215_);
lean_dec_ref(v_what_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(lean_object* v_s_218_, lean_object* v_p_219_){
_start:
{
uint8_t v___y_221_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = lean_string_utf8_byte_size(v_s_218_);
v___x_225_ = lean_nat_dec_eq(v_p_219_, v___x_224_);
if (v___x_225_ == 0)
{
uint32_t v___x_226_; uint8_t v___y_228_; uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_226_ = lean_string_utf8_get_fast(v_s_218_, v_p_219_);
v___x_233_ = 32;
v___x_234_ = lean_uint32_dec_eq(v___x_226_, v___x_233_);
if (v___x_234_ == 0)
{
uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 9;
v___x_236_ = lean_uint32_dec_eq(v___x_226_, v___x_235_);
v___y_228_ = v___x_236_;
goto v___jp_227_;
}
else
{
v___y_228_ = v___x_234_;
goto v___jp_227_;
}
v___jp_227_:
{
if (v___y_228_ == 0)
{
uint32_t v___x_229_; uint8_t v___x_230_; 
v___x_229_ = 13;
v___x_230_ = lean_uint32_dec_eq(v___x_226_, v___x_229_);
if (v___x_230_ == 0)
{
uint32_t v___x_231_; uint8_t v___x_232_; 
v___x_231_ = 10;
v___x_232_ = lean_uint32_dec_eq(v___x_226_, v___x_231_);
v___y_221_ = v___x_232_;
goto v___jp_220_;
}
else
{
v___y_221_ = v___x_230_;
goto v___jp_220_;
}
}
else
{
return v_p_219_;
}
}
}
else
{
return v_p_219_;
}
v___jp_220_:
{
if (v___y_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = lean_string_utf8_next_fast(v_s_218_, v_p_219_);
lean_dec(v_p_219_);
v_p_219_ = v___x_222_;
goto _start;
}
else
{
return v_p_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace___boxed(lean_object* v_s_237_, lean_object* v_p_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(v_s_237_, v_p_238_);
lean_dec_ref(v_s_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(lean_object* v_s_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_string_utf8_byte_size(v_s_240_);
v___x_243_ = lean_nat_dec_eq(v_a_241_, v___x_242_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_string_utf8_get_fast(v_s_240_, v_a_241_);
v___x_245_ = 45;
v___x_246_ = lean_uint32_dec_eq(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_241_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_249_ = lean_string_utf8_next_fast(v_s_240_, v_a_241_);
lean_dec(v_a_241_);
v___x_250_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(v_s_240_, v___x_249_);
v___x_251_ = lean_string_utf8_extract(v_s_240_, v___x_249_, v___x_250_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_250_);
return v___x_253_;
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_a_241_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f___boxed(lean_object* v_s_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_256_, v_a_257_);
lean_dec_ref(v_s_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(lean_object* v_s_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; lean_object* v_a_264_; 
v___x_263_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_261_, v_a_262_);
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
if (lean_obj_tag(v_a_264_) == 1)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_280_; 
v_a_265_ = lean_ctor_get(v___x_263_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_281_);
v___x_267_ = v___x_263_;
v_isShared_268_ = v_isSharedCheck_280_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_263_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_280_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_val_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_val_269_ = lean_ctor_get(v_a_264_, 0);
lean_inc(v_val_269_);
lean_dec_ref(v_a_264_);
v___x_270_ = lean_string_utf8_byte_size(v_val_269_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_274_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v_val_269_);
v___x_274_ = v___x_267_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_val_269_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_a_265_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_278_; 
lean_dec(v_val_269_);
v___x_276_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0));
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 1);
lean_ctor_set(v___x_267_, 0, v___x_276_);
v___x_278_ = v___x_267_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_a_265_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_a_264_);
v_a_282_ = lean_ctor_get(v___x_263_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; 
v_unused_291_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_291_);
v___x_284_ = v___x_263_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_263_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_a_282_);
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___boxed(lean_object* v_s_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_292_, v_a_293_);
lean_dec_ref(v_s_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(lean_object* v_s_296_, lean_object* v_x_297_, lean_object* v_startPos_298_, lean_object* v_endPos_299_){
_start:
{
lean_object* v___x_300_; 
lean_inc_ref(v_s_296_);
v___x_300_ = lean_apply_2(v_x_297_, v_s_296_, v_startPos_298_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_a_302_; uint8_t v___x_303_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
v_a_302_ = lean_ctor_get(v___x_300_, 1);
lean_inc(v_a_302_);
lean_dec_ref(v___x_300_);
v___x_303_ = lean_nat_dec_eq(v_a_302_, v_endPos_299_);
if (v___x_303_ == 0)
{
lean_object* v_tail_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_a_301_);
v_tail_304_ = lean_string_utf8_extract(v_s_296_, v_a_302_, v_endPos_299_);
lean_dec(v_a_302_);
lean_dec_ref(v_s_296_);
v___x_305_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0));
v___x_306_ = lean_string_append(v___x_305_, v_tail_304_);
lean_dec_ref(v_tail_304_);
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v___x_308_; 
lean_dec(v_a_302_);
lean_dec_ref(v_s_296_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v_a_301_);
return v___x_308_;
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_310_; 
lean_dec_ref(v_s_296_);
v_a_309_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_300_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v_a_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___boxed(lean_object* v_s_311_, lean_object* v_x_312_, lean_object* v_startPos_313_, lean_object* v_endPos_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_311_, v_x_312_, v_startPos_313_, v_endPos_314_);
lean_dec(v_endPos_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse(lean_object* v_00_u03b1_316_, lean_object* v_s_317_, lean_object* v_x_318_, lean_object* v_startPos_319_, lean_object* v_endPos_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_317_, v_x_318_, v_startPos_319_, v_endPos_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_runVerParse___boxed(lean_object* v_00_u03b1_322_, lean_object* v_s_323_, lean_object* v_x_324_, lean_object* v_startPos_325_, lean_object* v_endPos_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lake_Util_Version_0__Lake_runVerParse(v_00_u03b1_322_, v_s_323_, v_x_324_, v_startPos_325_, v_endPos_326_);
lean_dec(v_endPos_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprSemVerCore_repr_spec__0(lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_nat_to_int(v_a_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(9u);
v___x_348_ = lean_nat_to_int(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__0));
v___x_360_ = lean_string_length(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__15, &l_Lake_instReprSemVerCore_repr___redArg___closed__15_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15);
v___x_362_ = lean_nat_to_int(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___redArg(lean_object* v_x_367_){
_start:
{
lean_object* v_major_368_; lean_object* v_minor_369_; lean_object* v_patch_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_major_368_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_major_368_);
v_minor_369_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_minor_369_);
v_patch_370_ = lean_ctor_get(v_x_367_, 2);
lean_inc(v_patch_370_);
lean_dec_ref(v_x_367_);
v___x_371_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_372_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__6));
v___x_373_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__7, &l_Lake_instReprSemVerCore_repr___redArg___closed__7_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7);
v___x_374_ = l_Nat_reprFast(v_major_368_);
v___x_375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
v___x_376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_373_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = 0;
v___x_378_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*1, v___x_377_);
v___x_379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_372_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_box(1);
v___x_383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__11));
v___x_385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_371_);
v___x_387_ = l_Nat_reprFast(v_minor_369_);
v___x_388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
v___x_389_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_373_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*1, v___x_377_);
v___x_391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_386_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_380_);
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_382_);
v___x_394_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__13));
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_371_);
v___x_397_ = l_Nat_reprFast(v_patch_370_);
v___x_398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
v___x_399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_373_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*1, v___x_377_);
v___x_401_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_396_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_403_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_401_);
v___x_405_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_406_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_402_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*1, v___x_377_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr(lean_object* v_x_409_, lean_object* v_prec_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lake_instReprSemVerCore_repr___redArg(v_x_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprSemVerCore_repr___boxed(lean_object* v_x_412_, lean_object* v_prec_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lake_instReprSemVerCore_repr(v_x_412_, v_prec_413_);
lean_dec(v_prec_413_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore_decEq(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_major_419_; lean_object* v_minor_420_; lean_object* v_patch_421_; lean_object* v_major_422_; lean_object* v_minor_423_; lean_object* v_patch_424_; uint8_t v___x_425_; 
v_major_419_ = lean_ctor_get(v_x_417_, 0);
v_minor_420_ = lean_ctor_get(v_x_417_, 1);
v_patch_421_ = lean_ctor_get(v_x_417_, 2);
v_major_422_ = lean_ctor_get(v_x_418_, 0);
v_minor_423_ = lean_ctor_get(v_x_418_, 1);
v_patch_424_ = lean_ctor_get(v_x_418_, 2);
v___x_425_ = lean_nat_dec_eq(v_major_419_, v_major_422_);
if (v___x_425_ == 0)
{
return v___x_425_;
}
else
{
uint8_t v___x_426_; 
v___x_426_ = lean_nat_dec_eq(v_minor_420_, v_minor_423_);
if (v___x_426_ == 0)
{
return v___x_426_;
}
else
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_eq(v_patch_421_, v_patch_424_);
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore_decEq___boxed(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_428_, v_x_429_);
lean_dec_ref(v_x_429_);
lean_dec_ref(v_x_428_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqSemVerCore(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_432_, v_x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqSemVerCore___boxed(lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Lake_instDecidableEqSemVerCore(v_x_435_, v_x_436_);
lean_dec_ref(v_x_436_);
lean_dec_ref(v_x_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdSemVerCore_ord(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_major_441_; lean_object* v_minor_442_; lean_object* v_patch_443_; lean_object* v_major_444_; lean_object* v_minor_445_; lean_object* v_patch_446_; uint8_t v___x_447_; 
v_major_441_ = lean_ctor_get(v_x_439_, 0);
v_minor_442_ = lean_ctor_get(v_x_439_, 1);
v_patch_443_ = lean_ctor_get(v_x_439_, 2);
v_major_444_ = lean_ctor_get(v_x_440_, 0);
v_minor_445_ = lean_ctor_get(v_x_440_, 1);
v_patch_446_ = lean_ctor_get(v_x_440_, 2);
v___x_447_ = lean_nat_dec_lt(v_major_441_, v_major_444_);
if (v___x_447_ == 0)
{
uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_eq(v_major_441_, v_major_444_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
v___x_449_ = 2;
return v___x_449_;
}
else
{
uint8_t v___x_450_; 
v___x_450_ = lean_nat_dec_lt(v_minor_442_, v_minor_445_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_eq(v_minor_442_, v_minor_445_);
if (v___x_451_ == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 2;
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = lean_nat_dec_lt(v_patch_443_, v_patch_446_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_eq(v_patch_443_, v_patch_446_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = 2;
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 1;
return v___x_456_;
}
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
}
}
else
{
uint8_t v___x_458_; 
v___x_458_ = 0;
return v___x_458_;
}
}
}
else
{
uint8_t v___x_459_; 
v___x_459_ = 0;
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdSemVerCore_ord___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Lake_instOrdSemVerCore_ord(v_x_460_, v_x_461_);
lean_dec_ref(v_x_461_);
lean_dec_ref(v_x_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLT(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
return v___x_466_;
}
}
static lean_object* _init_l_Lake_SemVerCore_instLE(void){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = lean_box(0);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0(lean_object* v_x_468_, lean_object* v_y_469_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = l_Lake_instOrdSemVerCore_ord(v_x_468_, v_y_469_);
if (v___x_470_ == 2)
{
lean_inc_ref(v_y_469_);
return v_y_469_;
}
else
{
lean_inc_ref(v_x_468_);
return v_x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMin___lam__0___boxed(lean_object* v_x_471_, lean_object* v_y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lake_SemVerCore_instMin___lam__0(v_x_471_, v_y_472_);
lean_dec_ref(v_y_472_);
lean_dec_ref(v_x_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0(lean_object* v_x_476_, lean_object* v_y_477_){
_start:
{
uint8_t v___x_478_; 
v___x_478_ = l_Lake_instOrdSemVerCore_ord(v_x_476_, v_y_477_);
if (v___x_478_ == 2)
{
lean_inc_ref(v_x_476_);
return v_x_476_;
}
else
{
lean_inc_ref(v_y_477_);
return v_y_477_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instMax___lam__0___boxed(lean_object* v_x_479_, lean_object* v_y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lake_SemVerCore_instMax___lam__0(v_x_479_, v_y_480_);
lean_dec_ref(v_y_480_);
lean_dec_ref(v_x_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(lean_object* v_s_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_a_493_; lean_object* v_a_494_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_a_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_553_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_491_);
v___x_500_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_490_, v___x_499_, v_a_491_, v_a_491_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_a_502_ = lean_ctor_get(v___x_500_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_553_ == 0)
{
v___x_504_ = v___x_500_;
v_isShared_505_ = v_isSharedCheck_553_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_553_;
goto v_resetjp_503_;
}
v___jp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0));
v___x_496_ = lean_string_append(v___x_495_, v_a_493_);
lean_dec_ref(v_a_493_);
v___x_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_a_494_);
return v___x_497_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = lean_array_get_size(v_a_501_);
v___x_507_ = lean_unsigned_to_nat(3u);
v___x_508_ = lean_nat_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_del_object(v___x_504_);
lean_dec(v_a_501_);
v___x_509_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1));
v___x_510_ = l_Nat_reprFast(v___x_506_);
v___x_511_ = lean_string_append(v___x_509_, v___x_510_);
lean_dec_ref(v___x_510_);
v___x_512_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2));
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
v_a_493_ = v___x_513_;
v_a_494_ = v_a_502_;
goto v___jp_492_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_array_fget_borrowed(v_a_501_, v___x_498_);
v___x_515_ = l_String_Slice_toNat_x3f(v___x_514_);
if (lean_obj_tag(v___x_515_) == 1)
{
lean_object* v_val_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_val_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_val_516_);
lean_dec_ref(v___x_515_);
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_array_fget_borrowed(v_a_501_, v___x_517_);
v___x_519_ = l_String_Slice_toNat_x3f(v___x_518_);
if (lean_obj_tag(v___x_519_) == 1)
{
lean_object* v_val_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_val_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_val_520_);
lean_dec_ref(v___x_519_);
v___x_521_ = lean_unsigned_to_nat(2u);
v___x_522_ = lean_array_fget(v_a_501_, v___x_521_);
lean_dec(v_a_501_);
v___x_523_ = l_String_Slice_toNat_x3f(v___x_522_);
if (lean_obj_tag(v___x_523_) == 1)
{
lean_object* v_val_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec(v___x_522_);
v_val_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_val_524_);
lean_dec_ref(v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v_val_516_);
lean_ctor_set(v___x_525_, 1, v_val_520_);
lean_ctor_set(v___x_525_, 2, v_val_524_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_525_);
v___x_527_ = v___x_504_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_a_502_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_object* v_str_529_; lean_object* v_startInclusive_530_; lean_object* v_endExclusive_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___x_523_);
lean_dec(v_val_520_);
lean_dec(v_val_516_);
lean_del_object(v___x_504_);
v_str_529_ = lean_ctor_get(v___x_522_, 0);
lean_inc_ref(v_str_529_);
v_startInclusive_530_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_startInclusive_530_);
v_endExclusive_531_ = lean_ctor_get(v___x_522_, 2);
lean_inc(v_endExclusive_531_);
lean_dec(v___x_522_);
v___x_532_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_533_ = lean_string_utf8_extract(v_str_529_, v_startInclusive_530_, v_endExclusive_531_);
lean_dec(v_endExclusive_531_);
lean_dec(v_startInclusive_530_);
lean_dec_ref(v_str_529_);
v___x_534_ = lean_string_append(v___x_532_, v___x_533_);
lean_dec_ref(v___x_533_);
v___x_535_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_536_ = lean_string_append(v___x_534_, v___x_535_);
v_a_493_ = v___x_536_;
v_a_494_ = v_a_502_;
goto v___jp_492_;
}
}
else
{
lean_object* v_str_537_; lean_object* v_startInclusive_538_; lean_object* v_endExclusive_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
lean_inc(v___x_518_);
lean_dec(v___x_519_);
lean_dec(v_val_516_);
lean_del_object(v___x_504_);
lean_dec(v_a_501_);
v_str_537_ = lean_ctor_get(v___x_518_, 0);
lean_inc_ref(v_str_537_);
v_startInclusive_538_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_startInclusive_538_);
v_endExclusive_539_ = lean_ctor_get(v___x_518_, 2);
lean_inc(v_endExclusive_539_);
lean_dec(v___x_518_);
v___x_540_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_541_ = lean_string_utf8_extract(v_str_537_, v_startInclusive_538_, v_endExclusive_539_);
lean_dec(v_endExclusive_539_);
lean_dec(v_startInclusive_538_);
lean_dec_ref(v_str_537_);
v___x_542_ = lean_string_append(v___x_540_, v___x_541_);
lean_dec_ref(v___x_541_);
v___x_543_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
v_a_493_ = v___x_544_;
v_a_494_ = v_a_502_;
goto v___jp_492_;
}
}
else
{
lean_object* v_str_545_; lean_object* v_startInclusive_546_; lean_object* v_endExclusive_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc(v___x_514_);
lean_dec(v___x_515_);
lean_del_object(v___x_504_);
lean_dec(v_a_501_);
v_str_545_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_str_545_);
v_startInclusive_546_ = lean_ctor_get(v___x_514_, 1);
lean_inc(v_startInclusive_546_);
v_endExclusive_547_ = lean_ctor_get(v___x_514_, 2);
lean_inc(v_endExclusive_547_);
lean_dec(v___x_514_);
v___x_548_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_549_ = lean_string_utf8_extract(v_str_545_, v_startInclusive_546_, v_endExclusive_547_);
lean_dec(v_endExclusive_547_);
lean_dec(v_startInclusive_546_);
lean_dec_ref(v_str_545_);
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_552_ = lean_string_append(v___x_550_, v___x_551_);
v_a_493_ = v___x_552_;
v_a_494_ = v_a_502_;
goto v___jp_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_parse(lean_object* v_s_555_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_556_ = ((lean_object*)(l_Lake_SemVerCore_parse___closed__0));
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_string_utf8_byte_size(v_s_555_);
v___x_559_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_555_, v___x_556_, v___x_557_, v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_toString(lean_object* v_ver_561_){
_start:
{
lean_object* v_major_562_; lean_object* v_minor_563_; lean_object* v_patch_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_major_562_ = lean_ctor_get(v_ver_561_, 0);
lean_inc(v_major_562_);
v_minor_563_ = lean_ctor_get(v_ver_561_, 1);
lean_inc(v_minor_563_);
v_patch_564_ = lean_ctor_get(v_ver_561_, 2);
lean_inc(v_patch_564_);
lean_dec_ref(v_ver_561_);
v___x_565_ = l_Nat_reprFast(v_major_562_);
v___x_566_ = ((lean_object*)(l_Lake_SemVerCore_toString___closed__0));
v___x_567_ = lean_string_append(v___x_565_, v___x_566_);
v___x_568_ = l_Nat_reprFast(v_minor_563_);
v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
lean_dec_ref(v___x_568_);
v___x_570_ = lean_string_append(v___x_569_, v___x_566_);
v___x_571_ = l_Nat_reprFast(v_patch_564_);
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
lean_dec_ref(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instToJson___lam__0(lean_object* v_x_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = l_Lake_SemVerCore_toString(v_x_575_);
v___x_577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lake_SemVerCore_instFromJson___lam__0(lean_object* v_x_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Json_getStr_x3f(v_x_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_a_590_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_581_);
v___x_591_ = ((lean_object*)(l_Lake_SemVerCore_parse___closed__0));
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_string_utf8_byte_size(v_a_590_);
v___x_594_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_a_590_, v___x_591_, v___x_592_, v___x_593_);
return v___x_594_;
}
}
}
static lean_object* _init_l_Lake_instReprStdVer_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(16u);
v___x_612_ = lean_nat_to_int(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___redArg(lean_object* v_x_616_){
_start:
{
lean_object* v_toSemVerCore_617_; lean_object* v_specialDescr_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_651_; 
v_toSemVerCore_617_ = lean_ctor_get(v_x_616_, 0);
v_specialDescr_618_ = lean_ctor_get(v_x_616_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_651_ == 0)
{
v___x_620_ = v_x_616_;
v_isShared_621_ = v_isSharedCheck_651_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_specialDescr_618_);
lean_inc(v_toSemVerCore_617_);
lean_dec(v_x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_651_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_622_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_623_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__3));
v___x_624_ = lean_obj_once(&l_Lake_instReprStdVer_repr___redArg___closed__4, &l_Lake_instReprStdVer_repr___redArg___closed__4_once, _init_l_Lake_instReprStdVer_repr___redArg___closed__4);
v___x_625_ = l_Lake_instReprSemVerCore_repr___redArg(v_toSemVerCore_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 4);
lean_ctor_set(v___x_620_, 1, v___x_625_);
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_650_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_628_ = 0;
v___x_629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
v___x_630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_623_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_632_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_box(1);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = ((lean_object*)(l_Lake_instReprStdVer_repr___redArg___closed__6));
v___x_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_622_);
v___x_638_ = l_String_quote(v_specialDescr_618_);
v___x_639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___x_640_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_624_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_628_);
v___x_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_644_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v___x_642_);
v___x_646_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_643_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set_uint8(v___x_649_, sizeof(void*)*1, v___x_628_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr(lean_object* v_x_652_, lean_object* v_prec_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lake_instReprStdVer_repr___redArg(v_x_652_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprStdVer_repr___boxed(lean_object* v_x_655_, lean_object* v_prec_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lake_instReprStdVer_repr(v_x_655_, v_prec_656_);
lean_dec(v_prec_656_);
return v_res_657_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer_decEq(lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_toSemVerCore_662_; lean_object* v_specialDescr_663_; lean_object* v_toSemVerCore_664_; lean_object* v_specialDescr_665_; uint8_t v___x_666_; 
v_toSemVerCore_662_ = lean_ctor_get(v_x_660_, 0);
v_specialDescr_663_ = lean_ctor_get(v_x_660_, 1);
v_toSemVerCore_664_ = lean_ctor_get(v_x_661_, 0);
v_specialDescr_665_ = lean_ctor_get(v_x_661_, 1);
v___x_666_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_662_, v_toSemVerCore_664_);
if (v___x_666_ == 0)
{
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = lean_string_dec_eq(v_specialDescr_663_, v_specialDescr_665_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer_decEq___boxed(lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Lake_instDecidableEqStdVer_decEq(v_x_668_, v_x_669_);
lean_dec_ref(v_x_669_);
lean_dec_ref(v_x_668_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqStdVer(lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = l_Lake_instDecidableEqStdVer_decEq(v_x_672_, v_x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqStdVer___boxed(lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Lake_instDecidableEqStdVer(v_x_675_, v_x_676_);
lean_dec_ref(v_x_676_);
lean_dec_ref(v_x_675_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0(lean_object* v_self_679_){
_start:
{
lean_object* v_toSemVerCore_680_; 
v_toSemVerCore_680_ = lean_ctor_get(v_self_679_, 0);
lean_inc_ref(v_toSemVerCore_680_);
return v_toSemVerCore_680_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed(lean_object* v_self_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lake_StdVer_instCoeSemVerCore___lam__0(v_self_681_);
lean_dec_ref(v_self_681_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_ofSemVerCore(lean_object* v_ver_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_ver_685_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT uint8_t l_Lake_StdVer_compare(lean_object* v_a_690_, lean_object* v_b_691_){
_start:
{
lean_object* v_toSemVerCore_692_; lean_object* v_specialDescr_693_; lean_object* v_toSemVerCore_694_; lean_object* v_specialDescr_695_; uint8_t v___x_696_; 
v_toSemVerCore_692_ = lean_ctor_get(v_a_690_, 0);
v_specialDescr_693_ = lean_ctor_get(v_a_690_, 1);
v_toSemVerCore_694_ = lean_ctor_get(v_b_691_, 0);
v_specialDescr_695_ = lean_ctor_get(v_b_691_, 1);
v___x_696_ = l_Lake_instOrdSemVerCore_ord(v_toSemVerCore_692_, v_toSemVerCore_694_);
if (v___x_696_ == 1)
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_698_ = lean_string_dec_eq(v_specialDescr_693_, v___x_697_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
v___x_699_ = lean_string_dec_eq(v_specialDescr_695_, v___x_697_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = l_String_compare(v_specialDescr_693_, v_specialDescr_695_);
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
}
else
{
uint8_t v___x_702_; 
v___x_702_ = lean_string_dec_eq(v_specialDescr_695_, v___x_697_);
if (v___x_702_ == 0)
{
uint8_t v___x_703_; 
v___x_703_ = 2;
return v___x_703_;
}
else
{
return v___x_696_;
}
}
}
else
{
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_compare___boxed(lean_object* v_a_704_, lean_object* v_b_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Lake_StdVer_compare(v_a_704_, v_b_705_);
lean_dec_ref(v_b_705_);
lean_dec_ref(v_a_704_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
static lean_object* _init_l_Lake_StdVer_instLT(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(0);
return v___x_710_;
}
}
static lean_object* _init_l_Lake_StdVer_instLE(void){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_box(0);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0(lean_object* v_x_712_, lean_object* v_y_713_){
_start:
{
uint8_t v___x_714_; 
v___x_714_ = l_Lake_StdVer_compare(v_x_712_, v_y_713_);
if (v___x_714_ == 2)
{
lean_inc_ref(v_y_713_);
return v_y_713_;
}
else
{
lean_inc_ref(v_x_712_);
return v_x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMin___lam__0___boxed(lean_object* v_x_715_, lean_object* v_y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lake_StdVer_instMin___lam__0(v_x_715_, v_y_716_);
lean_dec_ref(v_y_716_);
lean_dec_ref(v_x_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0(lean_object* v_x_720_, lean_object* v_y_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lake_StdVer_compare(v_x_720_, v_y_721_);
if (v___x_722_ == 2)
{
lean_inc_ref(v_x_720_);
return v_x_720_;
}
else
{
lean_inc_ref(v_y_721_);
return v_y_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instMax___lam__0___boxed(lean_object* v_x_723_, lean_object* v_y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lake_StdVer_instMax___lam__0(v_x_723_, v_y_724_);
lean_dec_ref(v_y_724_);
lean_dec_ref(v_x_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parseM(lean_object* v_s_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; 
lean_inc_ref(v_s_728_);
v___x_730_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_728_, v_a_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
v_a_732_ = lean_ctor_get(v___x_730_, 1);
lean_inc(v_a_732_);
lean_dec_ref(v___x_730_);
v___x_733_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_728_, v_a_732_);
lean_dec_ref(v_s_728_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_a_735_ = lean_ctor_get(v___x_733_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_743_ == 0)
{
v___x_737_ = v___x_733_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_731_);
lean_ctor_set(v___x_739_, 1, v_a_734_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_a_735_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_a_731_);
v_a_744_ = lean_ctor_get(v___x_733_, 0);
v_a_745_ = lean_ctor_get(v___x_733_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_733_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_inc(v_a_744_);
lean_dec(v___x_733_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_744_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v_s_728_);
v_a_753_ = lean_ctor_get(v___x_730_, 0);
v_a_754_ = lean_ctor_get(v___x_730_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_730_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_730_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_753_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_parse(lean_object* v_s_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_764_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_string_utf8_byte_size(v_s_763_);
v___x_767_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_763_, v___x_764_, v___x_765_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_toString(lean_object* v_ver_769_){
_start:
{
lean_object* v_toSemVerCore_770_; lean_object* v_specialDescr_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_toSemVerCore_770_ = lean_ctor_get(v_ver_769_, 0);
lean_inc_ref(v_toSemVerCore_770_);
v_specialDescr_771_ = lean_ctor_get(v_ver_769_, 1);
lean_inc_ref(v_specialDescr_771_);
lean_dec_ref(v_ver_769_);
v___x_772_ = lean_string_utf8_byte_size(v_specialDescr_771_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = l_Lake_SemVerCore_toString(v_toSemVerCore_770_);
v___x_776_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v___x_778_ = lean_string_append(v___x_777_, v_specialDescr_771_);
lean_dec_ref(v_specialDescr_771_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; 
lean_dec_ref(v_specialDescr_771_);
v___x_779_ = l_Lake_SemVerCore_toString(v_toSemVerCore_770_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instToJson___lam__0(lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = l_Lake_StdVer_toString(v_x_782_);
v___x_784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lake_StdVer_instFromJson___lam__0(lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Json_getStr_x3f(v_x_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_a_797_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v___x_788_);
v___x_798_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_string_utf8_byte_size(v_a_797_);
v___x_801_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_a_797_, v___x_798_, v___x_799_, v___x_800_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx(lean_object* v_x_810_){
_start:
{
switch(lean_obj_tag(v_x_810_))
{
case 0:
{
lean_object* v___x_811_; 
v___x_811_ = lean_unsigned_to_nat(0u);
return v___x_811_;
}
case 1:
{
lean_object* v___x_812_; 
v___x_812_ = lean_unsigned_to_nat(1u);
return v___x_812_;
}
case 2:
{
lean_object* v___x_813_; 
v___x_813_ = lean_unsigned_to_nat(2u);
return v___x_813_;
}
default: 
{
lean_object* v___x_814_; 
v___x_814_ = lean_unsigned_to_nat(3u);
return v___x_814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorIdx___boxed(lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lake_ToolchainVer_ctorIdx(v_x_815_);
lean_dec_ref(v_x_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___redArg(lean_object* v_t_817_, lean_object* v_k_818_){
_start:
{
switch(lean_obj_tag(v_t_817_))
{
case 1:
{
lean_object* v_date_819_; lean_object* v_rev_820_; lean_object* v___x_821_; 
v_date_819_ = lean_ctor_get(v_t_817_, 0);
lean_inc_ref(v_date_819_);
v_rev_820_ = lean_ctor_get(v_t_817_, 1);
lean_inc(v_rev_820_);
lean_dec_ref(v_t_817_);
v___x_821_ = lean_apply_2(v_k_818_, v_date_819_, v_rev_820_);
return v___x_821_;
}
case 2:
{
lean_object* v_n_822_; lean_object* v___x_823_; 
v_n_822_ = lean_ctor_get(v_t_817_, 0);
lean_inc(v_n_822_);
lean_dec_ref(v_t_817_);
v___x_823_ = lean_apply_1(v_k_818_, v_n_822_);
return v___x_823_;
}
default: 
{
lean_object* v_ver_824_; lean_object* v___x_825_; 
v_ver_824_ = lean_ctor_get(v_t_817_, 0);
lean_inc_ref(v_ver_824_);
lean_dec_ref(v_t_817_);
v___x_825_ = lean_apply_1(v_k_818_, v_ver_824_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim(lean_object* v_motive_826_, lean_object* v_ctorIdx_827_, lean_object* v_t_828_, lean_object* v_h_829_, lean_object* v_k_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_828_, v_k_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ctorElim___boxed(lean_object* v_motive_832_, lean_object* v_ctorIdx_833_, lean_object* v_t_834_, lean_object* v_h_835_, lean_object* v_k_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lake_ToolchainVer_ctorElim(v_motive_832_, v_ctorIdx_833_, v_t_834_, v_h_835_, v_k_836_);
lean_dec(v_ctorIdx_833_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim___redArg(lean_object* v_t_838_, lean_object* v_release_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_838_, v_release_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release_elim(lean_object* v_motive_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_release_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_842_, v_release_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim___redArg(lean_object* v_t_846_, lean_object* v_nightly_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_846_, v_nightly_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly_elim(lean_object* v_motive_849_, lean_object* v_t_850_, lean_object* v_h_851_, lean_object* v_nightly_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_850_, v_nightly_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim___redArg(lean_object* v_t_854_, lean_object* v_pr_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_854_, v_pr_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr_elim(lean_object* v_motive_857_, lean_object* v_t_858_, lean_object* v_h_859_, lean_object* v_pr_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_858_, v_pr_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim___redArg(lean_object* v_t_862_, lean_object* v_other_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_862_, v_other_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other_elim(lean_object* v_motive_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_other_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_866_, v_other_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override___redArg(lean_object* v_t_870_, lean_object* v_release_871_, lean_object* v_nightly_872_, lean_object* v_pr_873_, lean_object* v_other_874_){
_start:
{
switch(lean_obj_tag(v_t_870_))
{
case 0:
{
lean_object* v_ver_875_; lean_object* v___x_876_; 
lean_dec(v_other_874_);
lean_dec(v_pr_873_);
lean_dec(v_nightly_872_);
v_ver_875_ = lean_ctor_get(v_t_870_, 1);
lean_inc_ref(v_ver_875_);
lean_dec_ref(v_t_870_);
v___x_876_ = lean_apply_1(v_release_871_, v_ver_875_);
return v___x_876_;
}
case 1:
{
lean_object* v_date_877_; lean_object* v_rev_878_; lean_object* v___x_879_; 
lean_dec(v_other_874_);
lean_dec(v_pr_873_);
lean_dec(v_release_871_);
v_date_877_ = lean_ctor_get(v_t_870_, 1);
lean_inc_ref(v_date_877_);
v_rev_878_ = lean_ctor_get(v_t_870_, 2);
lean_inc(v_rev_878_);
lean_dec_ref(v_t_870_);
v___x_879_ = lean_apply_2(v_nightly_872_, v_date_877_, v_rev_878_);
return v___x_879_;
}
case 2:
{
lean_object* v_n_880_; lean_object* v___x_881_; 
lean_dec(v_other_874_);
lean_dec(v_nightly_872_);
lean_dec(v_release_871_);
v_n_880_ = lean_ctor_get(v_t_870_, 1);
lean_inc(v_n_880_);
lean_dec_ref(v_t_870_);
v___x_881_ = lean_apply_1(v_pr_873_, v_n_880_);
return v___x_881_;
}
default: 
{
lean_object* v_v_882_; lean_object* v___x_883_; 
lean_dec(v_pr_873_);
lean_dec(v_nightly_872_);
lean_dec(v_release_871_);
v_v_882_ = lean_ctor_get(v_t_870_, 1);
lean_inc_ref(v_v_882_);
lean_dec_ref(v_t_870_);
v___x_883_ = lean_apply_1(v_other_874_, v_v_882_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_casesOn___override(lean_object* v_motive_884_, lean_object* v_t_885_, lean_object* v_release_886_, lean_object* v_nightly_887_, lean_object* v_pr_888_, lean_object* v_other_889_){
_start:
{
switch(lean_obj_tag(v_t_885_))
{
case 0:
{
lean_object* v_ver_890_; lean_object* v___x_891_; 
lean_dec(v_other_889_);
lean_dec(v_pr_888_);
lean_dec(v_nightly_887_);
v_ver_890_ = lean_ctor_get(v_t_885_, 1);
lean_inc_ref(v_ver_890_);
lean_dec_ref(v_t_885_);
v___x_891_ = lean_apply_1(v_release_886_, v_ver_890_);
return v___x_891_;
}
case 1:
{
lean_object* v_date_892_; lean_object* v_rev_893_; lean_object* v___x_894_; 
lean_dec(v_other_889_);
lean_dec(v_pr_888_);
lean_dec(v_release_886_);
v_date_892_ = lean_ctor_get(v_t_885_, 1);
lean_inc_ref(v_date_892_);
v_rev_893_ = lean_ctor_get(v_t_885_, 2);
lean_inc(v_rev_893_);
lean_dec_ref(v_t_885_);
v___x_894_ = lean_apply_2(v_nightly_887_, v_date_892_, v_rev_893_);
return v___x_894_;
}
case 2:
{
lean_object* v_n_895_; lean_object* v___x_896_; 
lean_dec(v_other_889_);
lean_dec(v_nightly_887_);
lean_dec(v_release_886_);
v_n_895_ = lean_ctor_get(v_t_885_, 1);
lean_inc(v_n_895_);
lean_dec_ref(v_t_885_);
v___x_896_ = lean_apply_1(v_pr_888_, v_n_895_);
return v___x_896_;
}
default: 
{
lean_object* v_v_897_; lean_object* v___x_898_; 
lean_dec(v_pr_888_);
lean_dec(v_nightly_887_);
lean_dec(v_release_886_);
v_v_897_ = lean_ctor_get(v_t_885_, 1);
lean_inc_ref(v_v_897_);
lean_dec_ref(v_t_885_);
v___x_898_ = lean_apply_1(v_other_889_, v_v_897_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_release___override(lean_object* v_ver_900_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_901_ = ((lean_object*)(l_Lake_ToolchainVer_release___override___closed__0));
lean_inc_ref(v_ver_900_);
v___x_902_ = l_Lake_StdVer_toString(v_ver_900_);
v___x_903_ = lean_string_append(v___x_901_, v___x_902_);
lean_dec_ref(v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_ver_900_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_nightly___override(lean_object* v_date_907_, lean_object* v_rev_908_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___y_913_; 
v___x_909_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__0));
lean_inc_ref(v_date_907_);
v___x_910_ = l_Lake_Date_toString(v_date_907_);
v___x_911_ = lean_string_append(v___x_909_, v___x_910_);
lean_dec_ref(v___x_910_);
if (lean_obj_tag(v_rev_908_) == 0)
{
lean_object* v___x_916_; 
v___x_916_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___y_913_ = v___x_916_;
goto v___jp_912_;
}
else
{
lean_object* v_val_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_val_917_ = lean_ctor_get(v_rev_908_, 0);
v___x_918_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
lean_inc(v_val_917_);
v___x_919_ = l_Nat_reprFast(v_val_917_);
v___x_920_ = lean_string_append(v___x_918_, v___x_919_);
lean_dec_ref(v___x_919_);
v___y_913_ = v___x_920_;
goto v___jp_912_;
}
v___jp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_string_append(v___x_911_, v___y_913_);
lean_dec_ref(v___y_913_);
v___x_915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v_date_907_);
lean_ctor_set(v___x_915_, 2, v_rev_908_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_pr___override(lean_object* v_n_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = ((lean_object*)(l_Lake_ToolchainVer_pr___override___closed__0));
lean_inc(v_n_922_);
v___x_924_ = l_Nat_reprFast(v_n_922_);
v___x_925_ = lean_string_append(v___x_923_, v___x_924_);
lean_dec_ref(v___x_924_);
v___x_926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v_n_922_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_other___override(lean_object* v_v_927_){
_start:
{
lean_object* v___x_928_; 
lean_inc_ref(v_v_927_);
v___x_928_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_928_, 0, v_v_927_);
lean_ctor_set(v___x_928_, 1, v_v_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override(lean_object* v_x_929_){
_start:
{
lean_object* v_toString_930_; 
v_toString_930_ = lean_ctor_get(v_x_929_, 0);
lean_inc_ref(v_toString_930_);
return v_toString_930_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_toString___override___boxed(lean_object* v_x_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lake_ToolchainVer_toString___override(v_x_931_);
lean_dec_ref(v_x_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1));
return v___x_941_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_953_; 
v_val_942_ = lean_ctor_get(v_x_939_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_939_);
if (v_isSharedCheck_953_ == 0)
{
v___x_944_ = v_x_939_;
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_x_939_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_946_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3));
v___x_947_ = l_Nat_reprFast(v_val_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 3);
lean_ctor_set(v___x_944_, 0, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_952_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_946_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Repr_addAppParen(v___x_950_, v_x_940_);
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_x_954_, v_x_955_);
lean_dec(v_x_955_);
return v_res_956_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__3(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(2u);
v___x_964_ = lean_nat_to_int(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lake_instReprToolchainVer_repr___closed__4(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_nat_to_int(v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr(lean_object* v_x_985_, lean_object* v_prec_986_){
_start:
{
switch(lean_obj_tag(v_x_985_))
{
case 0:
{
lean_object* v_ver_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1006_; 
v_ver_987_ = lean_ctor_get(v_x_985_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v_x_985_, 0);
lean_dec(v_unused_1007_);
v___x_989_ = v_x_985_;
v_isShared_990_ = v_isSharedCheck_1006_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_ver_987_);
lean_dec(v_x_985_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1006_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___y_992_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(1024u);
v___x_1003_ = lean_nat_dec_le(v___x_1002_, v_prec_986_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_992_ = v___x_1004_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1005_; 
v___x_1005_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_992_ = v___x_1005_;
goto v___jp_991_;
}
v___jp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_993_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__2));
v___x_994_ = l_Lake_instReprStdVer_repr___redArg(v_ver_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 5);
lean_ctor_set(v___x_989_, 1, v___x_994_);
lean_ctor_set(v___x_989_, 0, v___x_993_);
v___x_996_ = v___x_989_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_994_);
v___x_996_ = v_reuseFailAlloc_1001_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_inc(v___y_992_);
v___x_997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_997_, 0, v___y_992_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = 0;
v___x_999_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*1, v___x_998_);
v___x_1000_ = l_Repr_addAppParen(v___x_999_, v_prec_986_);
return v___x_1000_;
}
}
}
}
case 1:
{
lean_object* v_date_1008_; lean_object* v_rev_1009_; lean_object* v___y_1011_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_date_1008_ = lean_ctor_get(v_x_985_, 1);
lean_inc_ref(v_date_1008_);
v_rev_1009_ = lean_ctor_get(v_x_985_, 2);
lean_inc(v_rev_1009_);
lean_dec_ref(v_x_985_);
v___x_1024_ = lean_unsigned_to_nat(1024u);
v___x_1025_ = lean_nat_dec_le(v___x_1024_, v_prec_986_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1011_ = v___x_1026_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1011_ = v___x_1027_;
goto v___jp_1010_;
}
v___jp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1012_ = lean_box(1);
v___x_1013_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__7));
v___x_1014_ = lean_unsigned_to_nat(1024u);
v___x_1015_ = l_Lake_instReprDate_repr___redArg(v_date_1008_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1013_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_1012_);
v___x_1018_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_rev_1009_, v___x_1014_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_inc(v___y_1011_);
v___x_1020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___y_1011_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = 0;
v___x_1022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*1, v___x_1021_);
v___x_1023_ = l_Repr_addAppParen(v___x_1022_, v_prec_986_);
return v___x_1023_;
}
}
case 2:
{
lean_object* v_n_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1048_; 
v_n_1028_ = lean_ctor_get(v_x_985_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_x_985_, 0);
lean_dec(v_unused_1049_);
v___x_1030_ = v_x_985_;
v_isShared_1031_ = v_isSharedCheck_1048_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_n_1028_);
lean_dec(v_x_985_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1048_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___y_1033_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_unsigned_to_nat(1024u);
v___x_1045_ = lean_nat_dec_le(v___x_1044_, v_prec_986_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1033_ = v___x_1046_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1033_ = v___x_1047_;
goto v___jp_1032_;
}
v___jp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1034_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__10));
v___x_1035_ = l_Nat_reprFast(v_n_1028_);
v___x_1036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 5);
lean_ctor_set(v___x_1030_, 1, v___x_1036_);
lean_ctor_set(v___x_1030_, 0, v___x_1034_);
v___x_1038_ = v___x_1030_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_inc(v___y_1033_);
v___x_1039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___y_1033_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = 0;
v___x_1041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set_uint8(v___x_1041_, sizeof(void*)*1, v___x_1040_);
v___x_1042_ = l_Repr_addAppParen(v___x_1041_, v_prec_986_);
return v___x_1042_;
}
}
}
}
default: 
{
lean_object* v_v_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1070_; 
v_v_1050_ = lean_ctor_get(v_x_985_, 1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_985_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_x_985_, 0);
lean_dec(v_unused_1071_);
v___x_1052_ = v_x_985_;
v_isShared_1053_ = v_isSharedCheck_1070_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_v_1050_);
lean_dec(v_x_985_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1070_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___y_1055_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(1024u);
v___x_1067_ = lean_nat_dec_le(v___x_1066_, v_prec_986_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1055_ = v___x_1068_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1055_ = v___x_1069_;
goto v___jp_1054_;
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1056_ = ((lean_object*)(l_Lake_instReprToolchainVer_repr___closed__13));
v___x_1057_ = l_String_quote(v_v_1050_);
v___x_1058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 5);
lean_ctor_set(v___x_1052_, 1, v___x_1058_);
lean_ctor_set(v___x_1052_, 0, v___x_1056_);
v___x_1060_ = v___x_1052_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_inc(v___y_1055_);
v___x_1061_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1055_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = 0;
v___x_1063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*1, v___x_1062_);
v___x_1064_ = l_Repr_addAppParen(v___x_1063_, v_prec_986_);
return v___x_1064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprToolchainVer_repr___boxed(lean_object* v_x_1072_, lean_object* v_prec_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lake_instReprToolchainVer_repr(v_x_1072_, v_prec_1073_);
lean_dec(v_prec_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer_decEq(lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
switch(lean_obj_tag(v_x_1077_))
{
case 0:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
lean_object* v_ver_1079_; lean_object* v_ver_1080_; uint8_t v___x_1081_; 
v_ver_1079_ = lean_ctor_get(v_x_1077_, 1);
lean_inc_ref(v_ver_1079_);
lean_dec_ref(v_x_1077_);
v_ver_1080_ = lean_ctor_get(v_x_1078_, 1);
lean_inc_ref(v_ver_1080_);
lean_dec_ref(v_x_1078_);
v___x_1081_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_1079_, v_ver_1080_);
lean_dec_ref(v_ver_1080_);
lean_dec_ref(v_ver_1079_);
return v___x_1081_;
}
else
{
uint8_t v___x_1082_; 
lean_dec_ref(v_x_1077_);
lean_dec_ref(v_x_1078_);
v___x_1082_ = 0;
return v___x_1082_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1078_) == 1)
{
lean_object* v_date_1083_; lean_object* v_rev_1084_; lean_object* v_date_1085_; lean_object* v_rev_1086_; uint8_t v___x_1087_; 
v_date_1083_ = lean_ctor_get(v_x_1077_, 1);
lean_inc_ref(v_date_1083_);
v_rev_1084_ = lean_ctor_get(v_x_1077_, 2);
lean_inc(v_rev_1084_);
lean_dec_ref(v_x_1077_);
v_date_1085_ = lean_ctor_get(v_x_1078_, 1);
lean_inc_ref(v_date_1085_);
v_rev_1086_ = lean_ctor_get(v_x_1078_, 2);
lean_inc(v_rev_1086_);
lean_dec_ref(v_x_1078_);
v___x_1087_ = l_Lake_instDecidableEqDate_decEq(v_date_1083_, v_date_1085_);
lean_dec_ref(v_date_1085_);
lean_dec_ref(v_date_1083_);
if (v___x_1087_ == 0)
{
lean_dec(v_rev_1086_);
lean_dec(v_rev_1084_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_1089_ = l_Option_instDecidableEq___redArg(v___x_1088_, v_rev_1084_, v_rev_1086_);
return v___x_1089_;
}
}
else
{
uint8_t v___x_1090_; 
lean_dec_ref(v_x_1077_);
lean_dec_ref(v_x_1078_);
v___x_1090_ = 0;
return v___x_1090_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1078_) == 2)
{
lean_object* v_n_1091_; lean_object* v_n_1092_; uint8_t v___x_1093_; 
v_n_1091_ = lean_ctor_get(v_x_1077_, 1);
lean_inc(v_n_1091_);
lean_dec_ref(v_x_1077_);
v_n_1092_ = lean_ctor_get(v_x_1078_, 1);
lean_inc(v_n_1092_);
lean_dec_ref(v_x_1078_);
v___x_1093_ = lean_nat_dec_eq(v_n_1091_, v_n_1092_);
lean_dec(v_n_1092_);
lean_dec(v_n_1091_);
return v___x_1093_;
}
else
{
uint8_t v___x_1094_; 
lean_dec_ref(v_x_1077_);
lean_dec_ref(v_x_1078_);
v___x_1094_ = 0;
return v___x_1094_;
}
}
default: 
{
if (lean_obj_tag(v_x_1078_) == 3)
{
lean_object* v_v_1095_; lean_object* v_v_1096_; uint8_t v___x_1097_; 
v_v_1095_ = lean_ctor_get(v_x_1077_, 1);
lean_inc_ref(v_v_1095_);
lean_dec_ref(v_x_1077_);
v_v_1096_ = lean_ctor_get(v_x_1078_, 1);
lean_inc_ref(v_v_1096_);
lean_dec_ref(v_x_1078_);
v___x_1097_ = lean_string_dec_eq(v_v_1095_, v_v_1096_);
lean_dec_ref(v_v_1096_);
lean_dec_ref(v_v_1095_);
return v___x_1097_;
}
else
{
uint8_t v___x_1098_; 
lean_dec_ref(v_x_1077_);
lean_dec_ref(v_x_1078_);
v___x_1098_ = 0;
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer_decEq___boxed(lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
uint8_t v_res_1101_; lean_object* v_r_1102_; 
v_res_1101_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1099_, v_x_1100_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqToolchainVer(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_1103_, v_x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqToolchainVer___boxed(lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
uint8_t v_res_1108_; lean_object* v_r_1109_; 
v_res_1108_ = l_Lake_instDecidableEqToolchainVer(v_x_1106_, v_x_1107_);
v_r_1109_ = lean_box(v_res_1108_);
return v_r_1109_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1114_ = lean_string_utf8_byte_size(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(lean_object* v_s_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1116_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0));
v___x_1117_ = lean_string_utf8_byte_size(v_s_1115_);
v___x_1118_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1);
v___x_1119_ = lean_nat_dec_le(v___x_1118_, v___x_1117_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_s_1115_);
v___x_1120_ = lean_box(0);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_string_memcmp(v_s_1115_, v___x_1116_, v___x_1121_, v___x_1121_, v___x_1118_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v_s_1115_);
v___x_1123_ = lean_box(0);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_inc_ref(v_s_1115_);
v___x_1124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1124_, 0, v_s_1115_);
lean_ctor_set(v___x_1124_, 1, v___x_1121_);
lean_ctor_set(v___x_1124_, 2, v___x_1117_);
v___x_1125_ = l_String_Slice_pos_x21(v___x_1124_, v___x_1118_);
lean_dec_ref(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1126_, 0, v_s_1115_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_ctor_set(v___x_1126_, 2, v___x_1117_);
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(lean_object* v_s_1128_, lean_object* v_pat_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v_s_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(lean_object* v_s_1131_, lean_object* v_pat_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(v_s_1131_, v_pat_1132_);
lean_dec_ref(v_pat_1132_);
return v_res_1133_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1135_ = lean_string_utf8_byte_size(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(lean_object* v_s_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1137_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1138_ = lean_string_utf8_byte_size(v_s_1136_);
v___x_1139_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0);
v___x_1140_ = lean_nat_dec_le(v___x_1139_, v___x_1138_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref(v_s_1136_);
v___x_1141_ = lean_box(0);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_string_memcmp(v_s_1136_, v___x_1137_, v___x_1142_, v___x_1142_, v___x_1139_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_s_1136_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_inc_ref(v_s_1136_);
v___x_1145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1145_, 0, v_s_1136_);
lean_ctor_set(v___x_1145_, 1, v___x_1142_);
lean_ctor_set(v___x_1145_, 2, v___x_1138_);
v___x_1146_ = l_String_Slice_pos_x21(v___x_1145_, v___x_1139_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1147_, 0, v_s_1136_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
lean_ctor_set(v___x_1147_, 2, v___x_1138_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(lean_object* v_s_1149_, lean_object* v_pat_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v_s_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(lean_object* v_s_1152_, lean_object* v_pat_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(v_s_1152_, v_pat_1153_);
lean_dec_ref(v_pat_1153_);
return v_res_1154_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0));
v___x_1157_ = lean_string_utf8_byte_size(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg(lean_object* v_s_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1159_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__0));
v___x_1160_ = lean_string_utf8_byte_size(v_s_1158_);
v___x_1161_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg___closed__1);
v___x_1162_ = lean_nat_dec_le(v___x_1161_, v___x_1160_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_dec_ref(v_s_1158_);
v___x_1163_ = lean_box(0);
return v___x_1163_;
}
else
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_unsigned_to_nat(0u);
v___x_1165_ = lean_string_memcmp(v_s_1158_, v___x_1159_, v___x_1164_, v___x_1164_, v___x_1161_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref(v_s_1158_);
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_inc_ref(v_s_1158_);
v___x_1167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1167_, 0, v_s_1158_);
lean_ctor_set(v___x_1167_, 1, v___x_1164_);
lean_ctor_set(v___x_1167_, 2, v___x_1160_);
v___x_1168_ = l_String_Slice_pos_x21(v___x_1167_, v___x_1161_);
lean_dec_ref(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1169_, 0, v_s_1158_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
lean_ctor_set(v___x_1169_, 2, v___x_1160_);
v___x_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2(lean_object* v_s_1171_, lean_object* v_pat_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v_s_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___boxed(lean_object* v_s_1174_, lean_object* v_pat_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2(v_s_1174_, v_pat_1175_);
lean_dec_ref(v_pat_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(lean_object* v___x_1177_, lean_object* v_ver_1178_, lean_object* v_a_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v_startInclusive_1181_; lean_object* v_endExclusive_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_startInclusive_1181_ = lean_ctor_get(v___x_1177_, 1);
v_endExclusive_1182_ = lean_ctor_get(v___x_1177_, 2);
v___x_1183_ = lean_nat_sub(v_endExclusive_1182_, v_startInclusive_1181_);
v___x_1184_ = lean_nat_dec_eq(v_a_1179_, v___x_1183_);
lean_dec(v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1185_ = lean_string_utf8_get_fast(v_ver_1178_, v_a_1179_);
v___x_1186_ = 58;
v___x_1187_ = lean_uint32_dec_eq(v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_string_utf8_next_fast(v_ver_1178_, v_a_1179_);
lean_dec(v_a_1179_);
v_a_1179_ = v___x_1189_;
v_b_1180_ = v___x_1188_;
goto _start;
}
else
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_a_1179_);
return v___x_1191_;
}
}
else
{
lean_dec(v_a_1179_);
lean_inc(v_b_1180_);
return v_b_1180_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg___boxed(lean_object* v___x_1192_, lean_object* v_ver_1193_, lean_object* v_a_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___x_1192_, v_ver_1193_, v_a_1194_, v_b_1195_);
lean_dec(v_b_1195_);
lean_dec_ref(v_ver_1193_);
lean_dec_ref(v___x_1192_);
return v_res_1196_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__1(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1199_ = lean_string_utf8_byte_size(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__2(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1201_ = lean_string_utf8_byte_size(v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_ofString___closed__4(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1204_ = lean_string_utf8_byte_size(v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofString(lean_object* v_ver_1205_){
_start:
{
lean_object* v___y_1207_; uint8_t v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1247_; uint8_t v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___y_1325_; lean_object* v_searcher_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_searcher_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_string_utf8_byte_size(v_ver_1205_);
lean_inc_ref(v_ver_1205_);
v___x_1335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1335_, 0, v_ver_1205_);
lean_ctor_set(v___x_1335_, 1, v_searcher_1333_);
lean_ctor_set(v___x_1335_, 2, v___x_1334_);
v___x_1336_ = lean_box(0);
v___x_1337_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___x_1335_, v_ver_1205_, v_searcher_1333_, v___x_1336_);
lean_dec_ref(v___x_1335_);
if (lean_obj_tag(v___x_1337_) == 0)
{
v___y_1325_ = v___x_1334_;
goto v___jp_1324_;
}
else
{
lean_object* v_val_1338_; 
v_val_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1338_);
lean_dec_ref(v___x_1337_);
v___y_1325_ = v_val_1338_;
goto v___jp_1324_;
}
v___jp_1206_:
{
if (v___y_1208_ == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v___y_1207_);
if (lean_obj_tag(v___x_1212_) == 1)
{
lean_object* v_val_1213_; lean_object* v_startInclusive_1214_; lean_object* v_endExclusive_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_val_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v___x_1212_);
v_startInclusive_1214_ = lean_ctor_get(v_val_1213_, 1);
v_endExclusive_1215_ = lean_ctor_get(v_val_1213_, 2);
v___x_1216_ = lean_nat_sub(v_endExclusive_1215_, v_startInclusive_1214_);
v___x_1217_ = lean_nat_dec_eq(v___x_1216_, v___y_1211_);
lean_dec(v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1218_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__0));
v___x_1219_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__1, &l_Lake_ToolchainVer_ofString___closed__1_once, _init_l_Lake_ToolchainVer_ofString___closed__1);
v___x_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v___y_1211_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v___x_1221_ = l_String_Slice_beq(v_val_1213_, v___x_1220_);
lean_dec_ref(v___x_1220_);
lean_dec(v_val_1213_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_inc_ref(v_ver_1205_);
v___x_1222_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_ver_1205_);
lean_ctor_set(v___x_1222_, 1, v_ver_1205_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; 
lean_dec_ref(v_ver_1205_);
v___x_1223_ = l_Lake_ToolchainVer_nightly___override(v___y_1210_, v___y_1209_);
return v___x_1223_;
}
}
else
{
lean_object* v___x_1224_; 
lean_dec(v_val_1213_);
lean_dec(v___y_1211_);
lean_dec_ref(v_ver_1205_);
v___x_1224_ = l_Lake_ToolchainVer_nightly___override(v___y_1210_, v___y_1209_);
return v___x_1224_;
}
}
else
{
lean_object* v___x_1225_; 
lean_dec(v___x_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_inc_ref(v_ver_1205_);
v___x_1225_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_ver_1205_);
lean_ctor_set(v___x_1225_, 1, v_ver_1205_);
return v___x_1225_;
}
}
else
{
lean_object* v___x_1226_; 
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v_ver_1205_);
v___x_1226_ = l_Lake_ToolchainVer_nightly___override(v___y_1210_, v___y_1209_);
return v___x_1226_;
}
}
v___jp_1227_:
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_string_length(v___y_1228_);
lean_dec_ref(v___y_1228_);
v___x_1236_ = lean_nat_dec_le(v___x_1235_, v___y_1232_);
lean_dec(v___y_1232_);
if (v___x_1236_ == 0)
{
if (lean_obj_tag(v___y_1234_) == 0)
{
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_inc_ref(v_ver_1205_);
v___x_1237_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_ver_1205_);
lean_ctor_set(v___x_1237_, 1, v_ver_1205_);
return v___x_1237_;
}
else
{
v___y_1207_ = v___y_1230_;
v___y_1208_ = v___y_1229_;
v___y_1209_ = v___y_1234_;
v___y_1210_ = v___y_1231_;
v___y_1211_ = v___y_1233_;
goto v___jp_1206_;
}
}
else
{
v___y_1207_ = v___y_1230_;
v___y_1208_ = v___y_1229_;
v___y_1209_ = v___y_1234_;
v___y_1210_ = v___y_1231_;
v___y_1211_ = v___y_1233_;
goto v___jp_1206_;
}
}
else
{
v___y_1207_ = v___y_1230_;
v___y_1208_ = v___y_1229_;
v___y_1209_ = v___y_1234_;
v___y_1210_ = v___y_1231_;
v___y_1211_ = v___y_1233_;
goto v___jp_1206_;
}
}
v___jp_1238_:
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_box(0);
v___y_1228_ = v___y_1239_;
v___y_1229_ = v___y_1241_;
v___y_1230_ = v___y_1240_;
v___y_1231_ = v___y_1242_;
v___y_1232_ = v___y_1244_;
v___y_1233_ = v___y_1243_;
v___y_1234_ = v___x_1245_;
goto v___jp_1227_;
}
v___jp_1246_:
{
lean_object* v___x_1251_; 
lean_inc_ref(v___y_1249_);
v___x_1251_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v___y_1249_);
if (lean_obj_tag(v___x_1251_) == 1)
{
lean_object* v_val_1252_; lean_object* v_rest_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v___y_1249_);
v_val_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_val_1252_);
lean_dec_ref(v___x_1251_);
v_rest_1253_ = l_String_Slice_toString(v_val_1252_);
lean_dec(v_val_1252_);
v___x_1254_ = lean_unsigned_to_nat(10u);
v___x_1255_ = lean_string_utf8_byte_size(v_rest_1253_);
lean_inc_n(v___y_1250_, 3);
lean_inc_ref_n(v_rest_1253_, 2);
v___x_1256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1256_, 0, v_rest_1253_);
lean_ctor_set(v___x_1256_, 1, v___y_1250_);
lean_ctor_set(v___x_1256_, 2, v___x_1255_);
v___x_1257_ = l_String_Slice_Pos_nextn(v___x_1256_, v___y_1250_, v___x_1254_);
lean_dec_ref(v___x_1256_);
lean_inc(v___x_1257_);
v___x_1258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1258_, 0, v_rest_1253_);
lean_ctor_set(v___x_1258_, 1, v___y_1250_);
lean_ctor_set(v___x_1258_, 2, v___x_1257_);
v___x_1259_ = l_String_Slice_toString(v___x_1258_);
lean_dec_ref(v___x_1258_);
v___x_1260_ = l_Lake_Date_ofString_x3f(v___x_1259_);
if (lean_obj_tag(v___x_1260_) == 1)
{
lean_object* v_val_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_val_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_val_1261_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = ((lean_object*)(l_Lake_ToolchainVer_nightly___override___closed__1));
v___x_1263_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__2, &l_Lake_ToolchainVer_ofString___closed__2_once, _init_l_Lake_ToolchainVer_ofString___closed__2);
v___x_1264_ = lean_nat_sub(v___x_1255_, v___x_1257_);
v___x_1265_ = lean_nat_dec_le(v___x_1263_, v___x_1264_);
lean_dec(v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec(v___x_1257_);
v___y_1239_ = v_rest_1253_;
v___y_1240_ = v___y_1247_;
v___y_1241_ = v___y_1248_;
v___y_1242_ = v_val_1261_;
v___y_1243_ = v___y_1250_;
v___y_1244_ = v___x_1254_;
goto v___jp_1238_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_string_memcmp(v_rest_1253_, v___x_1262_, v___x_1257_, v___y_1250_, v___x_1263_);
if (v___x_1266_ == 0)
{
lean_dec(v___x_1257_);
v___y_1239_ = v_rest_1253_;
v___y_1240_ = v___y_1247_;
v___y_1241_ = v___y_1248_;
v___y_1242_ = v_val_1261_;
v___y_1243_ = v___y_1250_;
v___y_1244_ = v___x_1254_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_inc(v___x_1257_);
lean_inc_ref_n(v_rest_1253_, 2);
v___x_1267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1267_, 0, v_rest_1253_);
lean_ctor_set(v___x_1267_, 1, v___x_1257_);
lean_ctor_set(v___x_1267_, 2, v___x_1255_);
v___x_1268_ = l_String_Slice_pos_x21(v___x_1267_, v___x_1263_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = lean_nat_add(v___x_1257_, v___x_1268_);
lean_dec(v___x_1268_);
lean_dec(v___x_1257_);
v___x_1270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1270_, 0, v_rest_1253_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
lean_ctor_set(v___x_1270_, 2, v___x_1255_);
v___x_1271_ = l_String_Slice_toString(v___x_1270_);
lean_dec_ref(v___x_1270_);
v___x_1272_ = lean_string_utf8_byte_size(v___x_1271_);
lean_inc(v___y_1250_);
v___x_1273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___y_1250_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
v___x_1274_ = l_String_Slice_toNat_x3f(v___x_1273_);
lean_dec_ref(v___x_1273_);
v___y_1228_ = v_rest_1253_;
v___y_1229_ = v___y_1248_;
v___y_1230_ = v___y_1247_;
v___y_1231_ = v_val_1261_;
v___y_1232_ = v___x_1254_;
v___y_1233_ = v___y_1250_;
v___y_1234_ = v___x_1274_;
goto v___jp_1227_;
}
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v___x_1260_);
lean_dec(v___x_1257_);
lean_dec_ref(v_rest_1253_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1247_);
lean_inc_ref(v_ver_1205_);
v___x_1275_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_ver_1205_);
lean_ctor_set(v___x_1275_, 1, v_ver_1205_);
return v___x_1275_;
}
}
else
{
lean_object* v___x_1276_; 
lean_dec(v___x_1251_);
v___x_1276_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___y_1249_);
if (lean_obj_tag(v___x_1276_) == 1)
{
lean_object* v_val_1277_; lean_object* v___x_1278_; 
lean_dec(v___y_1250_);
v_val_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_val_1277_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = l_String_Slice_toNat_x3f(v_val_1277_);
lean_dec(v_val_1277_);
if (lean_obj_tag(v___x_1278_) == 1)
{
if (v___y_1248_ == 0)
{
lean_object* v_val_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_val_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_val_1279_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = ((lean_object*)(l_Lake_ToolchainVer_prOrigin___closed__0));
v___x_1281_ = lean_string_dec_eq(v___y_1247_, v___x_1280_);
lean_dec_ref(v___y_1247_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_val_1279_);
lean_inc_ref(v_ver_1205_);
v___x_1282_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_ver_1205_);
lean_ctor_set(v___x_1282_, 1, v_ver_1205_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; 
lean_dec_ref(v_ver_1205_);
v___x_1283_ = l_Lake_ToolchainVer_pr___override(v_val_1279_);
return v___x_1283_;
}
}
else
{
lean_object* v_val_1284_; lean_object* v___x_1285_; 
lean_dec_ref(v___y_1247_);
lean_dec_ref(v_ver_1205_);
v_val_1284_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_val_1284_);
lean_dec_ref(v___x_1278_);
v___x_1285_ = l_Lake_ToolchainVer_pr___override(v_val_1284_);
return v___x_1285_;
}
}
else
{
lean_object* v___x_1286_; 
lean_dec(v___x_1278_);
lean_dec_ref(v___y_1247_);
lean_inc_ref(v_ver_1205_);
v___x_1286_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_ver_1205_);
lean_ctor_set(v___x_1286_, 1, v_ver_1205_);
return v___x_1286_;
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec(v___x_1276_);
v___x_1287_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_1288_ = lean_string_utf8_byte_size(v_ver_1205_);
lean_inc_ref(v_ver_1205_);
v___x_1289_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_ver_1205_, v___x_1287_, v___y_1250_, v___x_1288_);
if (lean_obj_tag(v___x_1289_) == 1)
{
if (v___y_1248_ == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref(v___x_1289_);
v___x_1291_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1292_ = lean_string_dec_eq(v___y_1247_, v___x_1291_);
lean_dec_ref(v___y_1247_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_dec(v_a_1290_);
lean_inc_ref(v_ver_1205_);
v___x_1293_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1293_, 0, v_ver_1205_);
lean_ctor_set(v___x_1293_, 1, v_ver_1205_);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; 
lean_dec_ref(v_ver_1205_);
v___x_1294_ = l_Lake_ToolchainVer_release___override(v_a_1290_);
return v___x_1294_;
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v___y_1247_);
lean_dec_ref(v_ver_1205_);
v_a_1295_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1295_);
lean_dec_ref(v___x_1289_);
v___x_1296_ = l_Lake_ToolchainVer_release___override(v_a_1295_);
return v___x_1296_;
}
}
else
{
lean_object* v___x_1297_; 
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___y_1247_);
lean_inc_ref(v_ver_1205_);
v___x_1297_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1297_, 0, v_ver_1205_);
lean_ctor_set(v___x_1297_, 1, v_ver_1205_);
return v___x_1297_;
}
}
}
}
v___jp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v_noOrigin_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1301_ = lean_string_utf8_byte_size(v_fst_1299_);
v___x_1302_ = lean_unsigned_to_nat(0u);
v_noOrigin_1303_ = lean_nat_dec_eq(v___x_1301_, v___x_1302_);
v___x_1304_ = ((lean_object*)(l_Lake_ToolchainVer_ofString___closed__3));
v___x_1305_ = lean_string_utf8_byte_size(v_snd_1300_);
v___x_1306_ = lean_obj_once(&l_Lake_ToolchainVer_ofString___closed__4, &l_Lake_ToolchainVer_ofString___closed__4_once, _init_l_Lake_ToolchainVer_ofString___closed__4);
v___x_1307_ = lean_nat_dec_le(v___x_1306_, v___x_1305_);
if (v___x_1307_ == 0)
{
v___y_1247_ = v_fst_1299_;
v___y_1248_ = v_noOrigin_1303_;
v___y_1249_ = v_snd_1300_;
v___y_1250_ = v___x_1302_;
goto v___jp_1246_;
}
else
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_string_memcmp(v_snd_1300_, v___x_1304_, v___x_1302_, v___x_1302_, v___x_1306_);
if (v___x_1308_ == 0)
{
v___y_1247_ = v_fst_1299_;
v___y_1248_ = v_noOrigin_1303_;
v___y_1249_ = v_snd_1300_;
v___y_1250_ = v___x_1302_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1309_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_snd_1300_);
v___x_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1310_, 0, v_snd_1300_);
lean_ctor_set(v___x_1310_, 1, v___x_1302_);
lean_ctor_set(v___x_1310_, 2, v___x_1305_);
v___x_1311_ = l_String_Slice_Pos_nextn(v___x_1310_, v___x_1302_, v___x_1309_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = lean_string_utf8_extract(v_snd_1300_, v___x_1311_, v___x_1305_);
lean_dec(v___x_1311_);
lean_dec_ref(v_snd_1300_);
v___x_1313_ = ((lean_object*)(l_Lake_StdVer_parse___closed__0));
v___x_1314_ = lean_string_utf8_byte_size(v___x_1312_);
v___x_1315_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v___x_1312_, v___x_1313_, v___x_1302_, v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 1)
{
if (v_noOrigin_1303_ == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((lean_object*)(l_Lake_ToolchainVer_defaultOrigin___closed__0));
v___x_1318_ = lean_string_dec_eq(v_fst_1299_, v___x_1317_);
lean_dec_ref(v_fst_1299_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
lean_dec(v_a_1316_);
lean_inc_ref(v_ver_1205_);
v___x_1319_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1319_, 0, v_ver_1205_);
lean_ctor_set(v___x_1319_, 1, v_ver_1205_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
lean_dec_ref(v_ver_1205_);
v___x_1320_ = l_Lake_ToolchainVer_release___override(v_a_1316_);
return v___x_1320_;
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v_fst_1299_);
lean_dec_ref(v_ver_1205_);
v_a_1321_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v___x_1315_);
v___x_1322_ = l_Lake_ToolchainVer_release___override(v_a_1321_);
return v___x_1322_;
}
}
else
{
lean_object* v___x_1323_; 
lean_dec_ref(v___x_1315_);
lean_dec_ref(v_fst_1299_);
lean_inc_ref(v_ver_1205_);
v___x_1323_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_ver_1205_);
lean_ctor_set(v___x_1323_, 1, v_ver_1205_);
return v___x_1323_;
}
}
}
}
v___jp_1324_:
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = lean_string_utf8_byte_size(v_ver_1205_);
v___x_1327_ = lean_nat_dec_eq(v___y_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v_pos_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_pos_1328_ = lean_string_utf8_next_fast(v_ver_1205_, v___y_1325_);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_string_utf8_extract(v_ver_1205_, v___x_1329_, v___y_1325_);
lean_dec(v___y_1325_);
v___x_1331_ = lean_string_utf8_extract(v_ver_1205_, v_pos_1328_, v___x_1326_);
v_fst_1299_ = v___x_1330_;
v_snd_1300_ = v___x_1331_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1332_; 
lean_dec(v___y_1325_);
v___x_1332_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
lean_inc_ref(v_ver_1205_);
v_fst_1299_ = v___x_1332_;
v_snd_1300_ = v_ver_1205_;
goto v___jp_1298_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3(lean_object* v___x_1339_, lean_object* v_ver_1340_, lean_object* v_inst_1341_, lean_object* v_R_1342_, lean_object* v_a_1343_, lean_object* v_b_1344_, lean_object* v_c_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___x_1339_, v_ver_1340_, v_a_1343_, v_b_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3___boxed(lean_object* v___x_1347_, lean_object* v_ver_1348_, lean_object* v_inst_1349_, lean_object* v_R_1350_, lean_object* v_a_1351_, lean_object* v_b_1352_, lean_object* v_c_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__3(v___x_1347_, v_ver_1348_, v_inst_1349_, v_R_1350_, v_a_1351_, v_b_1352_, v_c_1353_);
lean_dec(v_b_1352_);
lean_dec_ref(v_ver_1348_);
lean_dec_ref(v___x_1347_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f(lean_object* v_toolchainFile_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_IO_FS_readFile(v_toolchainFile_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1375_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1375_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1375_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_str_1366_; lean_object* v_startInclusive_1367_; lean_object* v_endExclusive_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_string_utf8_byte_size(v_a_1358_);
v___x_1364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1358_);
lean_ctor_set(v___x_1364_, 1, v___x_1362_);
lean_ctor_set(v___x_1364_, 2, v___x_1363_);
v___x_1365_ = l_String_Slice_trimAscii(v___x_1364_);
v_str_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc_ref(v_str_1366_);
v_startInclusive_1367_ = lean_ctor_get(v___x_1365_, 1);
lean_inc(v_startInclusive_1367_);
v_endExclusive_1368_ = lean_ctor_get(v___x_1365_, 2);
lean_inc(v_endExclusive_1368_);
lean_dec_ref(v___x_1365_);
v___x_1369_ = lean_string_utf8_extract(v_str_1366_, v_startInclusive_1367_, v_endExclusive_1368_);
lean_dec(v_endExclusive_1368_);
lean_dec(v_startInclusive_1367_);
lean_dec_ref(v_str_1366_);
v___x_1370_ = l_Lake_ToolchainVer_ofString(v___x_1369_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1371_);
v___x_1373_ = v___x_1360_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1387_; 
v_a_1376_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1378_ = v___x_1357_;
v_isShared_1379_ = v_isSharedCheck_1387_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1357_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1387_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
if (lean_obj_tag(v_a_1376_) == 11)
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_dec_ref(v_a_1376_);
v___x_1380_ = lean_box(0);
if (v_isShared_1379_ == 0)
{
lean_ctor_set_tag(v___x_1378_, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1380_);
v___x_1382_ = v___x_1378_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
else
{
lean_object* v___x_1385_; 
if (v_isShared_1379_ == 0)
{
v___x_1385_ = v___x_1378_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1376_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofFile_x3f___boxed(lean_object* v_toolchainFile_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_1388_);
lean_dec_ref(v_toolchainFile_1388_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f(lean_object* v_dir_1391_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = ((lean_object*)(l_Lake_toolchainFileName___closed__0));
v___x_1394_ = l_System_FilePath_join(v_dir_1391_, v___x_1393_);
v___x_1395_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1394_);
lean_dec_ref(v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ofDir_x3f___boxed(lean_object* v_dir_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lake_ToolchainVer_ofDir_x3f(v_dir_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0(lean_object* v_x_1401_){
_start:
{
lean_object* v_toString_1402_; lean_object* v___x_1403_; 
v_toString_1402_ = lean_ctor_get(v_x_1401_, 0);
lean_inc_ref(v_toString_1402_);
v___x_1403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_toString_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instToJson___lam__0___boxed(lean_object* v_x_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lake_ToolchainVer_instToJson___lam__0(v_x_1404_);
lean_dec_ref(v_x_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_instFromJson___lam__0(lean_object* v_x_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Json_getStr_x3f(v_x_1408_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
v_a_1418_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1420_ = v___x_1409_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1409_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = l_Lake_ToolchainVer_ofString(v_a_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_blt(lean_object* v_a_1429_, lean_object* v_b_1430_){
_start:
{
switch(lean_obj_tag(v_a_1429_))
{
case 0:
{
if (lean_obj_tag(v_b_1430_) == 0)
{
lean_object* v_ver_1431_; lean_object* v_ver_1432_; uint8_t v___x_1433_; 
v_ver_1431_ = lean_ctor_get(v_a_1429_, 1);
v_ver_1432_ = lean_ctor_get(v_b_1430_, 1);
v___x_1433_ = l_Lake_StdVer_compare(v_ver_1431_, v_ver_1432_);
if (v___x_1433_ == 0)
{
uint8_t v___x_1434_; 
v___x_1434_ = 1;
return v___x_1434_;
}
else
{
uint8_t v___x_1435_; 
v___x_1435_ = 0;
return v___x_1435_;
}
}
else
{
uint8_t v___x_1436_; 
v___x_1436_ = 0;
return v___x_1436_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1430_) == 1)
{
lean_object* v_date_1437_; lean_object* v_rev_1438_; lean_object* v_date_1439_; lean_object* v_rev_1440_; lean_object* v___y_1442_; uint8_t v___x_1447_; 
v_date_1437_ = lean_ctor_get(v_a_1429_, 1);
v_rev_1438_ = lean_ctor_get(v_a_1429_, 2);
v_date_1439_ = lean_ctor_get(v_b_1430_, 1);
v_rev_1440_ = lean_ctor_get(v_b_1430_, 2);
v___x_1447_ = l_Lake_instOrdDate_ord(v_date_1437_, v_date_1439_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; 
v___x_1448_ = 1;
return v___x_1448_;
}
else
{
uint8_t v___x_1449_; 
v___x_1449_ = l_Lake_instDecidableEqDate_decEq(v_date_1437_, v_date_1439_);
if (v___x_1449_ == 0)
{
return v___x_1449_;
}
else
{
if (lean_obj_tag(v_rev_1438_) == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___y_1442_ = v___x_1450_;
goto v___jp_1441_;
}
else
{
lean_object* v_val_1451_; 
v_val_1451_ = lean_ctor_get(v_rev_1438_, 0);
v___y_1442_ = v_val_1451_;
goto v___jp_1441_;
}
}
}
v___jp_1441_:
{
if (lean_obj_tag(v_rev_1440_) == 0)
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_nat_dec_lt(v___y_1442_, v___x_1443_);
return v___x_1444_;
}
else
{
lean_object* v_val_1445_; uint8_t v___x_1446_; 
v_val_1445_ = lean_ctor_get(v_rev_1440_, 0);
v___x_1446_ = lean_nat_dec_lt(v___y_1442_, v_val_1445_);
return v___x_1446_;
}
}
}
else
{
uint8_t v___x_1452_; 
v___x_1452_ = 0;
return v___x_1452_;
}
}
default: 
{
uint8_t v___x_1453_; 
v___x_1453_ = 0;
return v___x_1453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_blt___boxed(lean_object* v_a_1454_, lean_object* v_b_1455_){
_start:
{
uint8_t v_res_1456_; lean_object* v_r_1457_; 
v_res_1456_ = l_Lake_ToolchainVer_blt(v_a_1454_, v_b_1455_);
lean_dec_ref(v_b_1455_);
lean_dec_ref(v_a_1454_);
v_r_1457_ = lean_box(v_res_1456_);
return v_r_1457_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLT(void){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_box(0);
return v___x_1458_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLt(lean_object* v_a_1459_, lean_object* v_b_1460_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = l_Lake_ToolchainVer_blt(v_a_1459_, v_b_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLt___boxed(lean_object* v_a_1462_, lean_object* v_b_1463_){
_start:
{
uint8_t v_res_1464_; lean_object* v_r_1465_; 
v_res_1464_ = l_Lake_ToolchainVer_decLt(v_a_1462_, v_b_1463_);
lean_dec_ref(v_b_1463_);
lean_dec_ref(v_a_1462_);
v_r_1465_ = lean_box(v_res_1464_);
return v_r_1465_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_ble(lean_object* v_a_1466_, lean_object* v_b_1467_){
_start:
{
switch(lean_obj_tag(v_a_1466_))
{
case 0:
{
if (lean_obj_tag(v_b_1467_) == 0)
{
lean_object* v_ver_1468_; lean_object* v_ver_1469_; uint8_t v___x_1470_; 
v_ver_1468_ = lean_ctor_get(v_a_1466_, 1);
v_ver_1469_ = lean_ctor_get(v_b_1467_, 1);
v___x_1470_ = l_Lake_StdVer_compare(v_ver_1468_, v_ver_1469_);
if (v___x_1470_ == 2)
{
uint8_t v___x_1471_; 
v___x_1471_ = 0;
return v___x_1471_;
}
else
{
uint8_t v___x_1472_; 
v___x_1472_ = 1;
return v___x_1472_;
}
}
else
{
uint8_t v___x_1473_; 
v___x_1473_ = 0;
return v___x_1473_;
}
}
case 1:
{
if (lean_obj_tag(v_b_1467_) == 1)
{
lean_object* v_date_1474_; lean_object* v_rev_1475_; lean_object* v_date_1476_; lean_object* v_rev_1477_; lean_object* v___y_1479_; uint8_t v___x_1484_; 
v_date_1474_ = lean_ctor_get(v_a_1466_, 1);
v_rev_1475_ = lean_ctor_get(v_a_1466_, 2);
v_date_1476_ = lean_ctor_get(v_b_1467_, 1);
v_rev_1477_ = lean_ctor_get(v_b_1467_, 2);
v___x_1484_ = l_Lake_instOrdDate_ord(v_date_1474_, v_date_1476_);
if (v___x_1484_ == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = 1;
return v___x_1485_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = l_Lake_instDecidableEqDate_decEq(v_date_1474_, v_date_1476_);
if (v___x_1486_ == 0)
{
return v___x_1486_;
}
else
{
if (lean_obj_tag(v_rev_1475_) == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_unsigned_to_nat(0u);
v___y_1479_ = v___x_1487_;
goto v___jp_1478_;
}
else
{
lean_object* v_val_1488_; 
v_val_1488_ = lean_ctor_get(v_rev_1475_, 0);
v___y_1479_ = v_val_1488_;
goto v___jp_1478_;
}
}
}
v___jp_1478_:
{
if (lean_obj_tag(v_rev_1477_) == 0)
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = lean_nat_dec_le(v___y_1479_, v___x_1480_);
return v___x_1481_;
}
else
{
lean_object* v_val_1482_; uint8_t v___x_1483_; 
v_val_1482_ = lean_ctor_get(v_rev_1477_, 0);
v___x_1483_ = lean_nat_dec_le(v___y_1479_, v_val_1482_);
return v___x_1483_;
}
}
}
else
{
uint8_t v___x_1489_; 
v___x_1489_ = 0;
return v___x_1489_;
}
}
case 2:
{
if (lean_obj_tag(v_b_1467_) == 2)
{
lean_object* v_n_1490_; lean_object* v_n_1491_; uint8_t v___x_1492_; 
v_n_1490_ = lean_ctor_get(v_a_1466_, 1);
v_n_1491_ = lean_ctor_get(v_b_1467_, 1);
v___x_1492_ = lean_nat_dec_eq(v_n_1490_, v_n_1491_);
return v___x_1492_;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = 0;
return v___x_1493_;
}
}
default: 
{
if (lean_obj_tag(v_b_1467_) == 3)
{
lean_object* v_v_1494_; lean_object* v_v_1495_; uint8_t v___x_1496_; 
v_v_1494_ = lean_ctor_get(v_a_1466_, 1);
v_v_1495_ = lean_ctor_get(v_b_1467_, 1);
v___x_1496_ = lean_string_dec_eq(v_v_1494_, v_v_1495_);
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = 0;
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_ble___boxed(lean_object* v_a_1498_, lean_object* v_b_1499_){
_start:
{
uint8_t v_res_1500_; lean_object* v_r_1501_; 
v_res_1500_ = l_Lake_ToolchainVer_ble(v_a_1498_, v_b_1499_);
lean_dec_ref(v_b_1499_);
lean_dec_ref(v_a_1498_);
v_r_1501_ = lean_box(v_res_1500_);
return v_r_1501_;
}
}
static lean_object* _init_l_Lake_ToolchainVer_instLE(void){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_box(0);
return v___x_1502_;
}
}
LEAN_EXPORT uint8_t l_Lake_ToolchainVer_decLe(lean_object* v_a_1503_, lean_object* v_b_1504_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = l_Lake_ToolchainVer_ble(v_a_1503_, v_b_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lake_ToolchainVer_decLe___boxed(lean_object* v_a_1506_, lean_object* v_b_1507_){
_start:
{
uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_res_1508_ = l_Lake_ToolchainVer_decLe(v_a_1506_, v_b_1507_);
lean_dec_ref(v_b_1507_);
lean_dec_ref(v_a_1506_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
LEAN_EXPORT lean_object* l_Lake_normalizeToolchain(lean_object* v_s_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v_toString_1512_; 
v___x_1511_ = l_Lake_ToolchainVer_ofString(v_s_1510_);
v_toString_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc_ref(v_toString_1512_);
lean_dec_ref(v___x_1511_);
return v_toString_1512_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeVersionToolchainVer___lam__0(lean_object* v_x_1517_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = l_Lake_ToolchainVer_ofString(v_x_1517_);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx(uint8_t v_x_1522_){
_start:
{
switch(v_x_1522_)
{
case 0:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_unsigned_to_nat(0u);
return v___x_1523_;
}
case 1:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_unsigned_to_nat(1u);
return v___x_1524_;
}
case 2:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_unsigned_to_nat(2u);
return v___x_1525_;
}
case 3:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_unsigned_to_nat(3u);
return v___x_1526_;
}
case 4:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_unsigned_to_nat(4u);
return v___x_1527_;
}
default: 
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_unsigned_to_nat(5u);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorIdx___boxed(lean_object* v_x_1529_){
_start:
{
uint8_t v_x_boxed_1530_; lean_object* v_res_1531_; 
v_x_boxed_1530_ = lean_unbox(v_x_1529_);
v_res_1531_ = l_Lake_ComparatorOp_ctorIdx(v_x_boxed_1530_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx(uint8_t v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lake_ComparatorOp_ctorIdx(v_x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toCtorIdx___boxed(lean_object* v_x_1534_){
_start:
{
uint8_t v_x_4__boxed_1535_; lean_object* v_res_1536_; 
v_x_4__boxed_1535_ = lean_unbox(v_x_1534_);
v_res_1536_ = l_Lake_ComparatorOp_toCtorIdx(v_x_4__boxed_1535_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg(lean_object* v_k_1537_){
_start:
{
lean_inc(v_k_1537_);
return v_k_1537_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___redArg___boxed(lean_object* v_k_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lake_ComparatorOp_ctorElim___redArg(v_k_1538_);
lean_dec(v_k_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim(lean_object* v_motive_1540_, lean_object* v_ctorIdx_1541_, uint8_t v_t_1542_, lean_object* v_h_1543_, lean_object* v_k_1544_){
_start:
{
lean_inc(v_k_1544_);
return v_k_1544_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ctorElim___boxed(lean_object* v_motive_1545_, lean_object* v_ctorIdx_1546_, lean_object* v_t_1547_, lean_object* v_h_1548_, lean_object* v_k_1549_){
_start:
{
uint8_t v_t_boxed_1550_; lean_object* v_res_1551_; 
v_t_boxed_1550_ = lean_unbox(v_t_1547_);
v_res_1551_ = l_Lake_ComparatorOp_ctorElim(v_motive_1545_, v_ctorIdx_1546_, v_t_boxed_1550_, v_h_1548_, v_k_1549_);
lean_dec(v_k_1549_);
lean_dec(v_ctorIdx_1546_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg(lean_object* v_lt_1552_){
_start:
{
lean_inc(v_lt_1552_);
return v_lt_1552_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___redArg___boxed(lean_object* v_lt_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lake_ComparatorOp_lt_elim___redArg(v_lt_1553_);
lean_dec(v_lt_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim(lean_object* v_motive_1555_, uint8_t v_t_1556_, lean_object* v_h_1557_, lean_object* v_lt_1558_){
_start:
{
lean_inc(v_lt_1558_);
return v_lt_1558_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_lt_elim___boxed(lean_object* v_motive_1559_, lean_object* v_t_1560_, lean_object* v_h_1561_, lean_object* v_lt_1562_){
_start:
{
uint8_t v_t_boxed_1563_; lean_object* v_res_1564_; 
v_t_boxed_1563_ = lean_unbox(v_t_1560_);
v_res_1564_ = l_Lake_ComparatorOp_lt_elim(v_motive_1559_, v_t_boxed_1563_, v_h_1561_, v_lt_1562_);
lean_dec(v_lt_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg(lean_object* v_le_1565_){
_start:
{
lean_inc(v_le_1565_);
return v_le_1565_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___redArg___boxed(lean_object* v_le_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lake_ComparatorOp_le_elim___redArg(v_le_1566_);
lean_dec(v_le_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim(lean_object* v_motive_1568_, uint8_t v_t_1569_, lean_object* v_h_1570_, lean_object* v_le_1571_){
_start:
{
lean_inc(v_le_1571_);
return v_le_1571_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_le_elim___boxed(lean_object* v_motive_1572_, lean_object* v_t_1573_, lean_object* v_h_1574_, lean_object* v_le_1575_){
_start:
{
uint8_t v_t_boxed_1576_; lean_object* v_res_1577_; 
v_t_boxed_1576_ = lean_unbox(v_t_1573_);
v_res_1577_ = l_Lake_ComparatorOp_le_elim(v_motive_1572_, v_t_boxed_1576_, v_h_1574_, v_le_1575_);
lean_dec(v_le_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg(lean_object* v_gt_1578_){
_start:
{
lean_inc(v_gt_1578_);
return v_gt_1578_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___redArg___boxed(lean_object* v_gt_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lake_ComparatorOp_gt_elim___redArg(v_gt_1579_);
lean_dec(v_gt_1579_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim(lean_object* v_motive_1581_, uint8_t v_t_1582_, lean_object* v_h_1583_, lean_object* v_gt_1584_){
_start:
{
lean_inc(v_gt_1584_);
return v_gt_1584_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_gt_elim___boxed(lean_object* v_motive_1585_, lean_object* v_t_1586_, lean_object* v_h_1587_, lean_object* v_gt_1588_){
_start:
{
uint8_t v_t_boxed_1589_; lean_object* v_res_1590_; 
v_t_boxed_1589_ = lean_unbox(v_t_1586_);
v_res_1590_ = l_Lake_ComparatorOp_gt_elim(v_motive_1585_, v_t_boxed_1589_, v_h_1587_, v_gt_1588_);
lean_dec(v_gt_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg(lean_object* v_ge_1591_){
_start:
{
lean_inc(v_ge_1591_);
return v_ge_1591_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___redArg___boxed(lean_object* v_ge_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lake_ComparatorOp_ge_elim___redArg(v_ge_1592_);
lean_dec(v_ge_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim(lean_object* v_motive_1594_, uint8_t v_t_1595_, lean_object* v_h_1596_, lean_object* v_ge_1597_){
_start:
{
lean_inc(v_ge_1597_);
return v_ge_1597_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ge_elim___boxed(lean_object* v_motive_1598_, lean_object* v_t_1599_, lean_object* v_h_1600_, lean_object* v_ge_1601_){
_start:
{
uint8_t v_t_boxed_1602_; lean_object* v_res_1603_; 
v_t_boxed_1602_ = lean_unbox(v_t_1599_);
v_res_1603_ = l_Lake_ComparatorOp_ge_elim(v_motive_1598_, v_t_boxed_1602_, v_h_1600_, v_ge_1601_);
lean_dec(v_ge_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg(lean_object* v_eq_1604_){
_start:
{
lean_inc(v_eq_1604_);
return v_eq_1604_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___redArg___boxed(lean_object* v_eq_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lake_ComparatorOp_eq_elim___redArg(v_eq_1605_);
lean_dec(v_eq_1605_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim(lean_object* v_motive_1607_, uint8_t v_t_1608_, lean_object* v_h_1609_, lean_object* v_eq_1610_){
_start:
{
lean_inc(v_eq_1610_);
return v_eq_1610_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_eq_elim___boxed(lean_object* v_motive_1611_, lean_object* v_t_1612_, lean_object* v_h_1613_, lean_object* v_eq_1614_){
_start:
{
uint8_t v_t_boxed_1615_; lean_object* v_res_1616_; 
v_t_boxed_1615_ = lean_unbox(v_t_1612_);
v_res_1616_ = l_Lake_ComparatorOp_eq_elim(v_motive_1611_, v_t_boxed_1615_, v_h_1613_, v_eq_1614_);
lean_dec(v_eq_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg(lean_object* v_ne_1617_){
_start:
{
lean_inc(v_ne_1617_);
return v_ne_1617_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___redArg___boxed(lean_object* v_ne_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lake_ComparatorOp_ne_elim___redArg(v_ne_1618_);
lean_dec(v_ne_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim(lean_object* v_motive_1620_, uint8_t v_t_1621_, lean_object* v_h_1622_, lean_object* v_ne_1623_){
_start:
{
lean_inc(v_ne_1623_);
return v_ne_1623_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ne_elim___boxed(lean_object* v_motive_1624_, lean_object* v_t_1625_, lean_object* v_h_1626_, lean_object* v_ne_1627_){
_start:
{
uint8_t v_t_boxed_1628_; lean_object* v_res_1629_; 
v_t_boxed_1628_ = lean_unbox(v_t_1625_);
v_res_1629_ = l_Lake_ComparatorOp_ne_elim(v_motive_1624_, v_t_boxed_1628_, v_h_1626_, v_ne_1627_);
lean_dec(v_ne_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr(uint8_t v_x_1648_, lean_object* v_prec_1649_){
_start:
{
lean_object* v___y_1651_; lean_object* v___y_1658_; lean_object* v___y_1665_; lean_object* v___y_1672_; lean_object* v___y_1679_; lean_object* v___y_1686_; 
switch(v_x_1648_)
{
case 0:
{
lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1692_ = lean_unsigned_to_nat(1024u);
v___x_1693_ = lean_nat_dec_le(v___x_1692_, v_prec_1649_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1651_ = v___x_1694_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1651_ = v___x_1695_;
goto v___jp_1650_;
}
}
case 1:
{
lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = lean_unsigned_to_nat(1024u);
v___x_1697_ = lean_nat_dec_le(v___x_1696_, v_prec_1649_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1658_ = v___x_1698_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1658_ = v___x_1699_;
goto v___jp_1657_;
}
}
case 2:
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = lean_unsigned_to_nat(1024u);
v___x_1701_ = lean_nat_dec_le(v___x_1700_, v_prec_1649_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1665_ = v___x_1702_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1665_ = v___x_1703_;
goto v___jp_1664_;
}
}
case 3:
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = lean_unsigned_to_nat(1024u);
v___x_1705_ = lean_nat_dec_le(v___x_1704_, v_prec_1649_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1672_ = v___x_1706_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1672_ = v___x_1707_;
goto v___jp_1671_;
}
}
case 4:
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_unsigned_to_nat(1024u);
v___x_1709_ = lean_nat_dec_le(v___x_1708_, v_prec_1649_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1679_ = v___x_1710_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1679_ = v___x_1711_;
goto v___jp_1678_;
}
}
default: 
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = lean_unsigned_to_nat(1024u);
v___x_1713_ = lean_nat_dec_le(v___x_1712_, v_prec_1649_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__3, &l_Lake_instReprToolchainVer_repr___closed__3_once, _init_l_Lake_instReprToolchainVer_repr___closed__3);
v___y_1686_ = v___x_1714_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_obj_once(&l_Lake_instReprToolchainVer_repr___closed__4, &l_Lake_instReprToolchainVer_repr___closed__4_once, _init_l_Lake_instReprToolchainVer_repr___closed__4);
v___y_1686_ = v___x_1715_;
goto v___jp_1685_;
}
}
}
v___jp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1652_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__1));
lean_inc(v___y_1651_);
v___x_1653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___y_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = 0;
v___x_1655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*1, v___x_1654_);
v___x_1656_ = l_Repr_addAppParen(v___x_1655_, v_prec_1649_);
return v___x_1656_;
}
v___jp_1657_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1659_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__3));
lean_inc(v___y_1658_);
v___x_1660_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___y_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = 0;
v___x_1662_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set_uint8(v___x_1662_, sizeof(void*)*1, v___x_1661_);
v___x_1663_ = l_Repr_addAppParen(v___x_1662_, v_prec_1649_);
return v___x_1663_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1666_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__5));
lean_inc(v___y_1665_);
v___x_1667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___y_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = 0;
v___x_1669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*1, v___x_1668_);
v___x_1670_ = l_Repr_addAppParen(v___x_1669_, v_prec_1649_);
return v___x_1670_;
}
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1673_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__7));
lean_inc(v___y_1672_);
v___x_1674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = 0;
v___x_1676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set_uint8(v___x_1676_, sizeof(void*)*1, v___x_1675_);
v___x_1677_ = l_Repr_addAppParen(v___x_1676_, v_prec_1649_);
return v___x_1677_;
}
v___jp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1680_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__9));
lean_inc(v___y_1679_);
v___x_1681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___y_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = 0;
v___x_1683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*1, v___x_1682_);
v___x_1684_ = l_Repr_addAppParen(v___x_1683_, v_prec_1649_);
return v___x_1684_;
}
v___jp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1687_ = ((lean_object*)(l_Lake_instReprComparatorOp_repr___closed__11));
lean_inc(v___y_1686_);
v___x_1688_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___y_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = 0;
v___x_1690_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*1, v___x_1689_);
v___x_1691_ = l_Repr_addAppParen(v___x_1690_, v_prec_1649_);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprComparatorOp_repr___boxed(lean_object* v_x_1716_, lean_object* v_prec_1717_){
_start:
{
uint8_t v_x_341__boxed_1718_; lean_object* v_res_1719_; 
v_x_341__boxed_1718_ = lean_unbox(v_x_1716_);
v_res_1719_ = l_Lake_instReprComparatorOp_repr(v_x_341__boxed_1718_, v_prec_1717_);
lean_dec(v_prec_1717_);
return v_res_1719_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp_default(void){
_start:
{
uint8_t v___x_1722_; 
v___x_1722_ = 0;
return v___x_1722_;
}
}
static uint8_t _init_l_Lake_instInhabitedComparatorOp(void){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = 0;
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(lean_object* v_sym_1724_, uint8_t v_cmp_1725_, lean_object* v_t_1726_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_box(v_cmp_1725_);
lean_inc_ref(v_sym_1724_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_sym_1724_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_Data_Trie_insert___redArg(v_t_1726_, v_sym_1724_, v___x_1728_);
lean_dec_ref(v_sym_1724_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(lean_object* v_sym_1730_, lean_object* v_cmp_1731_, lean_object* v_t_1732_){
_start:
{
uint8_t v_cmp_boxed_1733_; lean_object* v_res_1734_; 
v_cmp_boxed_1733_ = lean_unbox(v_cmp_1731_);
v_res_1734_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v_sym_1730_, v_cmp_boxed_1733_, v_t_1732_);
return v_res_1734_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9(void){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_1744_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10(void){
_start:
{
lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9);
v___x_1746_ = 0;
v___x_1747_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
v___x_1748_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1747_, v___x_1746_, v___x_1745_);
return v___x_1748_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11(void){
_start:
{
lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1749_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10);
v___x_1750_ = 1;
v___x_1751_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7));
v___x_1752_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1751_, v___x_1750_, v___x_1749_);
return v___x_1752_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12(void){
_start:
{
lean_object* v___x_1753_; uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1753_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11);
v___x_1754_ = 1;
v___x_1755_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
v___x_1756_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1755_, v___x_1754_, v___x_1753_);
return v___x_1756_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13(void){
_start:
{
lean_object* v___x_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1757_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12);
v___x_1758_ = 2;
v___x_1759_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
v___x_1760_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1759_, v___x_1758_, v___x_1757_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14(void){
_start:
{
lean_object* v___x_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1761_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13);
v___x_1762_ = 3;
v___x_1763_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4));
v___x_1764_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1763_, v___x_1762_, v___x_1761_);
return v___x_1764_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15(void){
_start:
{
lean_object* v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1765_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14);
v___x_1766_ = 3;
v___x_1767_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
v___x_1768_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1767_, v___x_1766_, v___x_1765_);
return v___x_1768_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16(void){
_start:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1769_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15);
v___x_1770_ = 4;
v___x_1771_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
v___x_1772_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1771_, v___x_1770_, v___x_1769_);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17(void){
_start:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1773_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16);
v___x_1774_ = 5;
v___x_1775_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1));
v___x_1776_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1775_, v___x_1774_, v___x_1773_);
return v___x_1776_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18(void){
_start:
{
lean_object* v___x_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1777_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17);
v___x_1778_ = 5;
v___x_1779_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
v___x_1780_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(v___x_1779_, v___x_1778_, v___x_1777_);
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie(void){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_obj_once(&l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18, &l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once, _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(lean_object* v_s_1784_, lean_object* v_p_1785_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
v___x_1787_ = lean_string_utf8_byte_size(v_s_1784_);
lean_inc(v_p_1785_);
v___x_1788_ = l_Lean_Data_Trie_matchPrefix___redArg(v_s_1784_, v___x_1786_, v_p_1785_, v___x_1787_);
if (lean_obj_tag(v___x_1788_) == 1)
{
lean_object* v_val_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1805_; 
v_val_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_val_1789_);
lean_dec_ref(v___x_1788_);
v_fst_1790_ = lean_ctor_get(v_val_1789_, 0);
v_snd_1791_ = lean_ctor_get(v_val_1789_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_val_1789_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1793_ = v_val_1789_;
v_isShared_1794_ = v_isSharedCheck_1805_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_val_1789_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1805_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v_p_x27_1796_; uint8_t v___x_1797_; 
v___x_1795_ = lean_string_utf8_byte_size(v_fst_1790_);
lean_dec(v_fst_1790_);
v_p_x27_1796_ = lean_nat_add(v_p_1785_, v___x_1795_);
v___x_1797_ = lean_string_is_valid_pos(v_s_1784_, v_p_x27_1796_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
lean_dec(v_p_x27_1796_);
lean_dec(v_snd_1791_);
v___x_1798_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0));
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 1);
lean_ctor_set(v___x_1793_, 1, v_p_1785_);
lean_ctor_set(v___x_1793_, 0, v___x_1798_);
v___x_1800_ = v___x_1793_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_p_1785_);
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
lean_object* v___x_1803_; 
lean_dec(v_p_1785_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v_p_x27_1796_);
lean_ctor_set(v___x_1793_, 0, v_snd_1791_);
v___x_1803_ = v___x_1793_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_snd_1791_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_p_x27_1796_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec(v___x_1788_);
v___x_1806_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1));
v___x_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v_p_1785_);
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(lean_object* v_s_1808_, lean_object* v_p_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1808_, v_p_1809_);
lean_dec_ref(v_s_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f(lean_object* v_s_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1811_, v___x_1812_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v_a_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
v_a_1815_ = lean_ctor_get(v___x_1813_, 1);
lean_inc(v_a_1815_);
lean_dec_ref(v___x_1813_);
v___x_1816_ = lean_string_utf8_byte_size(v_s_1811_);
v___x_1817_ = lean_nat_dec_eq(v_a_1815_, v___x_1816_);
lean_dec(v_a_1815_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec(v_a_1814_);
v___x_1818_ = lean_box(0);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_a_1814_);
return v___x_1819_;
}
}
else
{
lean_object* v___x_1820_; 
lean_dec_ref(v___x_1813_);
v___x_1820_ = lean_box(0);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_ofString_x3f___boxed(lean_object* v_s_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lake_ComparatorOp_ofString_x3f(v_s_1821_);
lean_dec_ref(v_s_1821_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString(uint8_t v_self_1823_){
_start:
{
switch(v_self_1823_)
{
case 0:
{
lean_object* v___x_1824_; 
v___x_1824_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8));
return v___x_1824_;
}
case 1:
{
lean_object* v___x_1825_; 
v___x_1825_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6));
return v___x_1825_;
}
case 2:
{
lean_object* v___x_1826_; 
v___x_1826_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5));
return v___x_1826_;
}
case 3:
{
lean_object* v___x_1827_; 
v___x_1827_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3));
return v___x_1827_;
}
case 4:
{
lean_object* v___x_1828_; 
v___x_1828_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2));
return v___x_1828_;
}
default: 
{
lean_object* v___x_1829_; 
v___x_1829_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0));
return v___x_1829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ComparatorOp_toString___boxed(lean_object* v_self_1830_){
_start:
{
uint8_t v_self_boxed_1831_; lean_object* v_res_1832_; 
v_self_boxed_1831_ = lean_unbox(v_self_1830_);
v_res_1832_ = l_Lake_ComparatorOp_toString(v_self_boxed_1831_);
return v_res_1832_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_unsigned_to_nat(7u);
v___x_1845_ = lean_nat_to_int(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_unsigned_to_nat(6u);
v___x_1850_ = lean_nat_to_int(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lake_instReprVerComparator_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_unsigned_to_nat(19u);
v___x_1855_ = lean_nat_to_int(v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___redArg(lean_object* v_x_1856_){
_start:
{
lean_object* v_ver_1857_; uint8_t v_op_1858_; uint8_t v_includeSuffixes_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_ver_1857_ = lean_ctor_get(v_x_1856_, 0);
lean_inc_ref(v_ver_1857_);
v_op_1858_ = lean_ctor_get_uint8(v_x_1856_, sizeof(void*)*1);
v_includeSuffixes_1859_ = lean_ctor_get_uint8(v_x_1856_, sizeof(void*)*1 + 1);
lean_dec_ref(v_x_1856_);
v___x_1860_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_1861_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__3));
v___x_1862_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__4, &l_Lake_instReprVerComparator_repr___redArg___closed__4_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__4);
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = l_Lake_instReprStdVer_repr___redArg(v_ver_1857_);
v___x_1865_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1862_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = 0;
v___x_1867_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1861_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_1870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_box(1);
v___x_1872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__6));
v___x_1874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1860_);
v___x_1876_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__7, &l_Lake_instReprVerComparator_repr___redArg___closed__7_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__7);
v___x_1877_ = l_Lake_instReprComparatorOp_repr(v_op_1858_, v___x_1863_);
v___x_1878_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set_uint8(v___x_1879_, sizeof(void*)*1, v___x_1866_);
v___x_1880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1875_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1869_);
v___x_1882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___x_1871_);
v___x_1883_ = ((lean_object*)(l_Lake_instReprVerComparator_repr___redArg___closed__9));
v___x_1884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v___x_1860_);
v___x_1886_ = lean_obj_once(&l_Lake_instReprVerComparator_repr___redArg___closed__10, &l_Lake_instReprVerComparator_repr___redArg___closed__10_once, _init_l_Lake_instReprVerComparator_repr___redArg___closed__10);
v___x_1887_ = l_Bool_repr___redArg(v_includeSuffixes_1859_);
v___x_1888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*1, v___x_1866_);
v___x_1890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1885_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_1892_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_1893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1890_);
v___x_1894_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_1895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1891_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*1, v___x_1866_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr(lean_object* v_x_1898_, lean_object* v_prec_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lake_instReprVerComparator_repr___redArg(v_x_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerComparator_repr___boxed(lean_object* v_x_1901_, lean_object* v_prec_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lake_instReprVerComparator_repr(v_x_1901_, v_prec_1902_);
lean_dec(v_prec_1902_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(lean_object* v_s_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_1915_, v_a_1916_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
v_a_1919_ = lean_ctor_get(v___x_1917_, 1);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1917_);
lean_inc_ref(v_s_1915_);
v___x_1920_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_1915_, v_a_1919_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v_a_1924_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
v_a_1922_ = lean_ctor_get(v___x_1920_, 1);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1920_);
v___x_1923_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_1915_, v_a_1922_);
lean_dec_ref(v_s_1915_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
if (lean_obj_tag(v_a_1924_) == 1)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1946_; 
v_a_1925_ = lean_ctor_get(v___x_1923_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v___x_1923_, 0);
lean_dec(v_unused_1947_);
v___x_1927_ = v___x_1923_;
v_isShared_1928_ = v_isSharedCheck_1946_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1923_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1946_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_val_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_val_1929_ = lean_ctor_get(v_a_1924_, 0);
lean_inc(v_val_1929_);
lean_dec_ref(v_a_1924_);
v___x_1930_ = lean_string_utf8_byte_size(v_val_1929_);
v___x_1931_ = lean_unsigned_to_nat(0u);
v___x_1932_ = lean_nat_dec_eq(v___x_1930_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1937_; 
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_a_1921_);
lean_ctor_set(v___x_1933_, 1, v_val_1929_);
v___x_1934_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
v___x_1935_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*1, v___x_1935_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*1 + 1, v___x_1932_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1934_);
v___x_1937_ = v___x_1927_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_a_1925_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1944_; 
lean_dec(v_val_1929_);
v___x_1939_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1921_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
v___x_1942_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*1, v___x_1942_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*1 + 1, v___x_1932_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1941_);
v___x_1944_ = v___x_1927_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_a_1925_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_a_1924_);
v_a_1948_ = lean_ctor_get(v___x_1923_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v___x_1923_, 0);
lean_dec(v_unused_1961_);
v___x_1950_ = v___x_1923_;
v_isShared_1951_ = v_isSharedCheck_1960_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1923_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1960_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1958_; 
v___x_1952_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1921_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = 0;
v___x_1955_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
v___x_1956_ = lean_unbox(v_a_1918_);
lean_dec(v_a_1918_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*1, v___x_1956_);
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*1 + 1, v___x_1954_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1955_);
v___x_1958_ = v___x_1950_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_a_1948_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_a_1918_);
lean_dec_ref(v_s_1915_);
v_a_1962_ = lean_ctor_get(v___x_1920_, 0);
v_a_1963_ = lean_ctor_get(v___x_1920_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1920_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_inc(v_a_1962_);
lean_dec(v___x_1920_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1962_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v_s_1915_);
v_a_1971_ = lean_ctor_get(v___x_1917_, 0);
v_a_1972_ = lean_ctor_get(v___x_1917_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1917_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_inc(v_a_1971_);
lean_dec(v___x_1917_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1971_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_parse(lean_object* v_s_1981_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = ((lean_object*)(l_Lake_VerComparator_parse___closed__0));
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = lean_string_utf8_byte_size(v_s_1981_);
v___x_1985_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_1981_, v___x_1982_, v___x_1983_, v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerComparator_test(lean_object* v_self_1986_, lean_object* v_ver_1987_){
_start:
{
uint8_t v___y_1989_; uint8_t v___y_1990_; lean_object* v___y_1991_; uint8_t v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; uint8_t v___y_1995_; lean_object* v___y_2000_; uint8_t v___y_2001_; uint8_t v___y_2002_; uint8_t v___y_2003_; lean_object* v___y_2004_; uint8_t v___y_2005_; uint8_t v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2019_; uint8_t v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v_ver_2026_; uint8_t v_op_2027_; uint8_t v_includeSuffixes_2028_; lean_object* v_ver_2030_; 
v_ver_2026_ = lean_ctor_get(v_self_1986_, 0);
v_op_2027_ = lean_ctor_get_uint8(v_self_1986_, sizeof(void*)*1);
v_includeSuffixes_2028_ = lean_ctor_get_uint8(v_self_1986_, sizeof(void*)*1 + 1);
if (v_includeSuffixes_2028_ == 0)
{
lean_object* v_toSemVerCore_2034_; lean_object* v_specialDescr_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_toSemVerCore_2034_ = lean_ctor_get(v_ver_1987_, 0);
v_specialDescr_2035_ = lean_ctor_get(v_ver_1987_, 1);
v___x_2036_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v___x_2037_ = lean_string_dec_eq(v_specialDescr_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v_toSemVerCore_2038_; lean_object* v_specialDescr_2039_; uint8_t v___x_2040_; 
v_toSemVerCore_2038_ = lean_ctor_get(v_ver_2026_, 0);
v_specialDescr_2039_ = lean_ctor_get(v_ver_2026_, 1);
v___x_2040_ = lean_string_dec_eq(v_specialDescr_2039_, v___x_2036_);
if (v___x_2040_ == 0)
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_2038_, v_toSemVerCore_2034_);
if (v___x_2041_ == 0)
{
return v_includeSuffixes_2028_;
}
else
{
switch(v_op_2027_)
{
case 0:
{
uint8_t v___x_2042_; 
v___x_2042_ = lean_string_dec_lt(v_specialDescr_2035_, v_specialDescr_2039_);
return v___x_2042_;
}
case 1:
{
uint8_t v___x_2043_; 
v___x_2043_ = l_String_decLE(v_specialDescr_2035_, v_specialDescr_2039_);
return v___x_2043_;
}
case 2:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_string_dec_lt(v_specialDescr_2039_, v_specialDescr_2035_);
return v___x_2044_;
}
case 3:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_String_decLE(v_specialDescr_2039_, v_specialDescr_2035_);
return v___x_2045_;
}
case 4:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_string_dec_eq(v_specialDescr_2035_, v_specialDescr_2039_);
return v___x_2046_;
}
default: 
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_string_dec_eq(v_specialDescr_2035_, v_specialDescr_2039_);
if (v___x_2047_ == 0)
{
return v___x_2041_;
}
else
{
return v___x_2040_;
}
}
}
}
}
else
{
return v_includeSuffixes_2028_;
}
}
else
{
v_ver_2030_ = v_ver_1987_;
goto v___jp_2029_;
}
}
else
{
v_ver_2030_ = v_ver_1987_;
goto v___jp_2029_;
}
v___jp_1988_:
{
uint8_t v___x_1996_; 
v___x_1996_ = l_Lake_instDecidableEqStdVer_decEq(v___y_1991_, v___y_1994_);
switch(v___y_1992_)
{
case 0:
{
return v___y_1990_;
}
case 1:
{
return v___y_1993_;
}
case 2:
{
return v___y_1989_;
}
case 3:
{
return v___y_1995_;
}
case 4:
{
return v___x_1996_;
}
default: 
{
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = 1;
return v___x_1997_;
}
else
{
uint8_t v___x_1998_; 
v___x_1998_ = 0;
return v___x_1998_;
}
}
}
}
v___jp_1999_:
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lake_StdVer_compare(v___y_2004_, v___y_2000_);
if (v___x_2006_ == 2)
{
uint8_t v___x_2007_; 
v___x_2007_ = 0;
v___y_1989_ = v___y_2005_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___y_2000_;
v___y_1992_ = v___y_2002_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___x_2007_;
goto v___jp_1988_;
}
else
{
uint8_t v___x_2008_; 
v___x_2008_ = 1;
v___y_1989_ = v___y_2005_;
v___y_1990_ = v___y_2001_;
v___y_1991_ = v___y_2000_;
v___y_1992_ = v___y_2002_;
v___y_1993_ = v___y_2003_;
v___y_1994_ = v___y_2004_;
v___y_1995_ = v___x_2008_;
goto v___jp_1988_;
}
}
v___jp_2009_:
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lake_StdVer_compare(v___y_2013_, v___y_2011_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = 1;
v___y_2000_ = v___y_2011_;
v___y_2001_ = v___y_2010_;
v___y_2002_ = v___y_2012_;
v___y_2003_ = v___y_2014_;
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___x_2016_;
goto v___jp_1999_;
}
else
{
uint8_t v___x_2017_; 
v___x_2017_ = 0;
v___y_2000_ = v___y_2011_;
v___y_2001_ = v___y_2010_;
v___y_2002_ = v___y_2012_;
v___y_2003_ = v___y_2014_;
v___y_2004_ = v___y_2013_;
v___y_2005_ = v___x_2017_;
goto v___jp_1999_;
}
}
v___jp_2018_:
{
uint8_t v___x_2023_; 
v___x_2023_ = l_Lake_StdVer_compare(v___y_2019_, v___y_2021_);
if (v___x_2023_ == 2)
{
uint8_t v___x_2024_; 
v___x_2024_ = 0;
v___y_2010_ = v___y_2022_;
v___y_2011_ = v___y_2019_;
v___y_2012_ = v___y_2020_;
v___y_2013_ = v___y_2021_;
v___y_2014_ = v___x_2024_;
goto v___jp_2009_;
}
else
{
uint8_t v___x_2025_; 
v___x_2025_ = 1;
v___y_2010_ = v___y_2022_;
v___y_2011_ = v___y_2019_;
v___y_2012_ = v___y_2020_;
v___y_2013_ = v___y_2021_;
v___y_2014_ = v___x_2025_;
goto v___jp_2009_;
}
}
v___jp_2029_:
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Lake_StdVer_compare(v_ver_2030_, v_ver_2026_);
if (v___x_2031_ == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = 1;
v___y_2019_ = v_ver_2030_;
v___y_2020_ = v_op_2027_;
v___y_2021_ = v_ver_2026_;
v___y_2022_ = v___x_2032_;
goto v___jp_2018_;
}
else
{
uint8_t v___x_2033_; 
v___x_2033_ = 0;
v___y_2019_ = v_ver_2030_;
v___y_2020_ = v_op_2027_;
v___y_2021_ = v_ver_2026_;
v___y_2022_ = v___x_2033_;
goto v___jp_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_test___boxed(lean_object* v_self_2048_, lean_object* v_ver_2049_){
_start:
{
uint8_t v_res_2050_; lean_object* v_r_2051_; 
v_res_2050_ = l_Lake_VerComparator_test(v_self_2048_, v_ver_2049_);
lean_dec_ref(v_ver_2049_);
lean_dec_ref(v_self_2048_);
v_r_2051_ = lean_box(v_res_2050_);
return v_r_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerComparator_toString(lean_object* v_self_2052_){
_start:
{
lean_object* v_ver_2053_; uint8_t v_op_2054_; uint8_t v_includeSuffixes_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_ver_2053_ = lean_ctor_get(v_self_2052_, 0);
lean_inc_ref(v_ver_2053_);
v_op_2054_ = lean_ctor_get_uint8(v_self_2052_, sizeof(void*)*1);
v_includeSuffixes_2055_ = lean_ctor_get_uint8(v_self_2052_, sizeof(void*)*1 + 1);
lean_dec_ref(v_self_2052_);
v___x_2056_ = l_Lake_ComparatorOp_toString(v_op_2054_);
v___x_2057_ = l_Lake_StdVer_toString(v_ver_2053_);
v___x_2058_ = lean_string_append(v___x_2056_, v___x_2057_);
lean_dec_ref(v___x_2057_);
if (v_includeSuffixes_2055_ == 0)
{
return v___x_2058_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l_Lake_StdVer_toString___closed__0));
v___x_2060_ = lean_string_append(v___x_2058_, v___x_2059_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
if (lean_obj_tag(v_x_2065_) == 0)
{
lean_dec(v_x_2063_);
return v_x_2064_;
}
else
{
lean_object* v_head_2066_; lean_object* v_tail_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2077_; 
v_head_2066_ = lean_ctor_get(v_x_2065_, 0);
v_tail_2067_ = lean_ctor_get(v_x_2065_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_x_2065_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2069_ = v_x_2065_;
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_tail_2067_);
lean_inc(v_head_2066_);
lean_dec(v_x_2065_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
lean_inc(v_x_2063_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 5);
lean_ctor_set(v___x_2069_, 1, v_x_2063_);
lean_ctor_set(v___x_2069_, 0, v_x_2064_);
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_x_2064_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_x_2063_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2066_);
v___x_2074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v_x_2064_ = v___x_2074_;
v_x_2065_ = v_tail_2067_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_){
_start:
{
if (lean_obj_tag(v_x_2080_) == 0)
{
lean_dec(v_x_2078_);
return v_x_2079_;
}
else
{
lean_object* v_head_2081_; lean_object* v_tail_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2092_; 
v_head_2081_ = lean_ctor_get(v_x_2080_, 0);
v_tail_2082_ = lean_ctor_get(v_x_2080_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2080_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2084_ = v_x_2080_;
v_isShared_2085_ = v_isSharedCheck_2092_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_tail_2082_);
lean_inc(v_head_2081_);
lean_dec(v_x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2092_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
lean_inc(v_x_2078_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 5);
lean_ctor_set(v___x_2084_, 1, v_x_2078_);
lean_ctor_set(v___x_2084_, 0, v_x_2079_);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_x_2079_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_x_2078_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2081_);
v___x_2089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_2078_, v___x_2089_, v_tail_2082_);
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(lean_object* v_x_2093_, lean_object* v_x_2094_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v___x_2095_; 
lean_dec(v_x_2094_);
v___x_2095_ = lean_box(0);
return v___x_2095_;
}
else
{
lean_object* v_tail_2096_; 
v_tail_2096_ = lean_ctor_get(v_x_2093_, 1);
if (lean_obj_tag(v_tail_2096_) == 0)
{
lean_object* v_head_2097_; lean_object* v___x_2098_; 
lean_dec(v_x_2094_);
v_head_2097_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_head_2097_);
lean_dec_ref(v_x_2093_);
v___x_2098_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2097_);
return v___x_2098_;
}
else
{
lean_object* v_head_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_inc(v_tail_2096_);
v_head_2099_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_head_2099_);
lean_dec_ref(v_x_2093_);
v___x_2100_ = l_Lake_instReprVerComparator_repr___redArg(v_head_2099_);
v___x_2101_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(v_x_2094_, v___x_2100_, v_tail_2096_);
return v___x_2101_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0));
v___x_2108_ = lean_string_length(v___x_2107_);
return v___x_2108_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3);
v___x_2110_ = lean_nat_to_int(v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(lean_object* v_xs_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2119_ = lean_array_get_size(v_xs_2118_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_nat_dec_eq(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2122_ = lean_array_to_list(v_xs_2118_);
v___x_2123_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2124_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(v___x_2122_, v___x_2123_);
v___x_2125_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2126_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2124_);
v___x_2128_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2125_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Std_Format_fill(v___x_2130_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; 
lean_dec_ref(v_xs_2118_);
v___x_2132_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(lean_object* v_x_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
lean_dec(v_x_2133_);
return v_x_2134_;
}
else
{
lean_object* v_head_2136_; lean_object* v_tail_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2147_; 
v_head_2136_ = lean_ctor_get(v_x_2135_, 0);
v_tail_2137_ = lean_ctor_get(v_x_2135_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_x_2135_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2139_ = v_x_2135_;
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_tail_2137_);
lean_inc(v_head_2136_);
lean_dec(v_x_2135_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
lean_inc(v_x_2133_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set_tag(v___x_2139_, 5);
lean_ctor_set(v___x_2139_, 1, v_x_2133_);
lean_ctor_set(v___x_2139_, 0, v_x_2134_);
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_x_2134_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_x_2133_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2136_);
v___x_2144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2142_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v_x_2134_ = v___x_2144_;
v_x_2135_ = v_tail_2137_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
lean_object* v___x_2150_; 
lean_dec(v_x_2149_);
v___x_2150_ = lean_box(0);
return v___x_2150_;
}
else
{
lean_object* v_tail_2151_; 
v_tail_2151_ = lean_ctor_get(v_x_2148_, 1);
if (lean_obj_tag(v_tail_2151_) == 0)
{
lean_object* v_head_2152_; lean_object* v___x_2153_; 
lean_dec(v_x_2149_);
v_head_2152_ = lean_ctor_get(v_x_2148_, 0);
lean_inc(v_head_2152_);
lean_dec_ref(v_x_2148_);
v___x_2153_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2152_);
return v___x_2153_;
}
else
{
lean_object* v_head_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_inc(v_tail_2151_);
v_head_2154_ = lean_ctor_get(v_x_2148_, 0);
lean_inc(v_head_2154_);
lean_dec_ref(v_x_2148_);
v___x_2155_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_2154_);
v___x_2156_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(v_x_2149_, v___x_2155_, v_tail_2151_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(lean_object* v_xs_2157_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2158_ = lean_array_get_size(v_xs_2157_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = lean_nat_dec_eq(v___x_2158_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2161_ = lean_array_to_list(v_xs_2157_);
v___x_2162_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1));
v___x_2163_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(v___x_2161_, v___x_2162_);
v___x_2164_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
v___x_2165_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5));
v___x_2166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2163_);
v___x_2167_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6));
v___x_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2164_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Std_Format_fill(v___x_2169_);
return v___x_2170_;
}
else
{
lean_object* v___x_2171_; 
lean_dec_ref(v_xs_2157_);
v___x_2171_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8));
return v___x_2171_;
}
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(12u);
v___x_2182_ = lean_nat_to_int(v___x_2181_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lake_instReprVerRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_unsigned_to_nat(11u);
v___x_2187_ = lean_nat_to_int(v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object* v_x_2188_){
_start:
{
lean_object* v_toString_2189_; lean_object* v_clauses_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2224_; 
v_toString_2189_ = lean_ctor_get(v_x_2188_, 0);
v_clauses_2190_ = lean_ctor_get(v_x_2188_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_x_2188_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2192_ = v_x_2188_;
v_isShared_2193_ = v_isSharedCheck_2224_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_clauses_2190_);
lean_inc(v_toString_2189_);
lean_dec(v_x_2188_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2224_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2194_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__5));
v___x_2195_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__3));
v___x_2196_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__4, &l_Lake_instReprVerRange_repr___redArg___closed__4_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__4);
v___x_2197_ = l_String_quote(v_toString_2189_);
v___x_2198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 4);
lean_ctor_set(v___x_2192_, 1, v___x_2198_);
lean_ctor_set(v___x_2192_, 0, v___x_2196_);
v___x_2200_ = v___x_2192_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2201_ = 0;
v___x_2202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set_uint8(v___x_2202_, sizeof(void*)*1, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2195_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__9));
v___x_2205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_box(1);
v___x_2207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = ((lean_object*)(l_Lake_instReprVerRange_repr___redArg___closed__6));
v___x_2209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2194_);
v___x_2211_ = lean_obj_once(&l_Lake_instReprVerRange_repr___redArg___closed__7, &l_Lake_instReprVerRange_repr___redArg___closed__7_once, _init_l_Lake_instReprVerRange_repr___redArg___closed__7);
v___x_2212_ = l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(v_clauses_2190_);
v___x_2213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*1, v___x_2201_);
v___x_2215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2210_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_obj_once(&l_Lake_instReprSemVerCore_repr___redArg___closed__16, &l_Lake_instReprSemVerCore_repr___redArg___closed__16_once, _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16);
v___x_2217_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__17));
v___x_2218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2215_);
v___x_2219_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__18));
v___x_2220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2216_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*1, v___x_2201_);
return v___x_2222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr(lean_object* v_x_2225_, lean_object* v_prec_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lake_instReprVerRange_repr___redArg(v_x_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprVerRange_repr___boxed(lean_object* v_x_2228_, lean_object* v_prec_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lake_instReprVerRange_repr(v_x_2228_, v_prec_2229_);
lean_dec(v_prec_2229_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0(lean_object* v_self_2240_){
_start:
{
lean_object* v_toString_2241_; 
v_toString_2241_ = lean_ctor_get(v_self_2240_, 0);
lean_inc_ref(v_toString_2241_);
return v_toString_2241_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_instToString___lam__0___boxed(lean_object* v_self_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lake_VerRange_instToString___lam__0(v_self_2242_);
lean_dec_ref(v_self_2242_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(lean_object* v_as_2247_, size_t v_i_2248_, size_t v_stop_2249_, lean_object* v_b_2250_){
_start:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_usize_dec_eq(v_i_2248_, v_stop_2249_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; size_t v___x_2257_; size_t v___x_2258_; 
v___x_2252_ = lean_array_uget_borrowed(v_as_2247_, v_i_2248_);
v___x_2253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0));
v___x_2254_ = lean_string_append(v_b_2250_, v___x_2253_);
lean_inc(v___x_2252_);
v___x_2255_ = l_Lake_VerComparator_toString(v___x_2252_);
v___x_2256_ = lean_string_append(v___x_2254_, v___x_2255_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_add(v_i_2248_, v___x_2257_);
v_i_2248_ = v___x_2258_;
v_b_2250_ = v___x_2256_;
goto _start;
}
else
{
return v_b_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(lean_object* v_as_2260_, lean_object* v_i_2261_, lean_object* v_stop_2262_, lean_object* v_b_2263_){
_start:
{
size_t v_i_boxed_2264_; size_t v_stop_boxed_2265_; lean_object* v_res_2266_; 
v_i_boxed_2264_ = lean_unbox_usize(v_i_2261_);
lean_dec(v_i_2261_);
v_stop_boxed_2265_ = lean_unbox_usize(v_stop_2262_);
lean_dec(v_stop_2262_);
v_res_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_2260_, v_i_boxed_2264_, v_stop_boxed_2265_, v_b_2263_);
lean_dec_ref(v_as_2260_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(lean_object* v_ands_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2269_ = lean_array_get_size(v_ands_2268_);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = lean_nat_dec_eq(v___x_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v___x_2272_ = lean_array_fget_borrowed(v_ands_2268_, v___x_2270_);
lean_inc(v___x_2272_);
v___x_2273_ = l_Lake_VerComparator_toString(v___x_2272_);
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = lean_nat_dec_lt(v___x_2274_, v___x_2269_);
if (v___x_2275_ == 0)
{
return v___x_2273_;
}
else
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_nat_dec_le(v___x_2269_, v___x_2269_);
if (v___x_2276_ == 0)
{
if (v___x_2275_ == 0)
{
return v___x_2273_;
}
else
{
size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_of_nat(v___x_2269_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2268_, v___x_2277_, v___x_2278_, v___x_2273_);
return v___x_2279_;
}
}
else
{
size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_of_nat(v___x_2269_);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_2268_, v___x_2280_, v___x_2281_, v___x_2273_);
return v___x_2282_;
}
}
}
else
{
lean_object* v___x_2283_; 
v___x_2283_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0));
return v___x_2283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(lean_object* v_ands_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v_ands_2284_);
lean_dec_ref(v_ands_2284_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(lean_object* v_as_2287_, size_t v_i_2288_, size_t v_stop_2289_, lean_object* v_b_2290_){
_start:
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_usize_dec_eq(v_i_2288_, v_stop_2289_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; size_t v___x_2297_; size_t v___x_2298_; 
v___x_2292_ = lean_array_uget_borrowed(v_as_2287_, v_i_2288_);
v___x_2293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0));
v___x_2294_ = lean_string_append(v_b_2290_, v___x_2293_);
v___x_2295_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2292_);
v___x_2296_ = lean_string_append(v___x_2294_, v___x_2295_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = ((size_t)1ULL);
v___x_2298_ = lean_usize_add(v_i_2288_, v___x_2297_);
v_i_2288_ = v___x_2298_;
v_b_2290_ = v___x_2296_;
goto _start;
}
else
{
return v_b_2290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(lean_object* v_as_2300_, lean_object* v_i_2301_, lean_object* v_stop_2302_, lean_object* v_b_2303_){
_start:
{
size_t v_i_boxed_2304_; size_t v_stop_boxed_2305_; lean_object* v_res_2306_; 
v_i_boxed_2304_ = lean_unbox_usize(v_i_2301_);
lean_dec(v_i_2301_);
v_stop_boxed_2305_ = lean_unbox_usize(v_stop_2302_);
lean_dec(v_stop_2302_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_2300_, v_i_boxed_2304_, v_stop_boxed_2305_, v_b_2303_);
lean_dec_ref(v_as_2300_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(lean_object* v_ors_2307_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = lean_array_get_size(v_ors_2307_);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_nat_dec_eq(v___x_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2311_ = lean_array_fget_borrowed(v_ors_2307_, v___x_2309_);
v___x_2312_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_2311_);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_nat_dec_lt(v___x_2313_, v___x_2308_);
if (v___x_2314_ == 0)
{
return v___x_2312_;
}
else
{
uint8_t v___x_2315_; 
v___x_2315_ = lean_nat_dec_le(v___x_2308_, v___x_2308_);
if (v___x_2315_ == 0)
{
if (v___x_2314_ == 0)
{
return v___x_2312_;
}
else
{
size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((size_t)1ULL);
v___x_2317_ = lean_usize_of_nat(v___x_2308_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2307_, v___x_2316_, v___x_2317_, v___x_2312_);
return v___x_2318_;
}
}
else
{
size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((size_t)1ULL);
v___x_2320_ = lean_usize_of_nat(v___x_2308_);
v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_2307_, v___x_2319_, v___x_2320_, v___x_2312_);
return v___x_2321_;
}
}
}
else
{
lean_object* v___x_2322_; 
v___x_2322_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
return v___x_2322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(lean_object* v_ors_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_ors_2323_);
lean_dec_ref(v_ors_2323_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_ofClauses(lean_object* v_clauses_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_clauses_2325_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v_clauses_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(lean_object* v_ands_2328_, lean_object* v_minVer_2329_, lean_object* v_maxVer_2330_, lean_object* v_specialDescr_2331_){
_start:
{
lean_object* v_minVer_2332_; lean_object* v___x_2333_; lean_object* v_maxVer_2334_; uint8_t v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_minVer_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2332_, 0, v_minVer_2329_);
lean_ctor_set(v_minVer_2332_, 1, v_specialDescr_2331_);
v___x_2333_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2334_, 0, v_maxVer_2330_);
lean_ctor_set(v_maxVer_2334_, 1, v___x_2333_);
v___x_2335_ = 3;
v___x_2336_ = 0;
v___x_2337_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2337_, 0, v_minVer_2332_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2335_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1 + 1, v___x_2336_);
v___x_2338_ = lean_array_push(v_ands_2328_, v___x_2337_);
v___x_2339_ = 0;
v___x_2340_ = 1;
v___x_2341_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2341_, 0, v_maxVer_2334_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*1, v___x_2339_);
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*1 + 1, v___x_2340_);
v___x_2342_ = lean_array_push(v___x_2338_, v___x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(lean_object* v_s_2345_, lean_object* v_ands_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_a_2351_; lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2523_; 
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2347_);
lean_inc_ref(v_s_2345_);
v___x_2350_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2345_, v___x_2349_, v_a_2347_, v_a_2347_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_a_2352_ = lean_ctor_get(v___x_2350_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2354_ = v___x_2350_;
v_isShared_2355_ = v_isSharedCheck_2523_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2523_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; 
v___x_2356_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2345_, v_a_2352_);
lean_dec_ref(v_s_2345_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2513_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_a_2358_ = lean_ctor_get(v___x_2356_, 1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2360_ = v___x_2356_;
v_isShared_2361_ = v_isSharedCheck_2513_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2513_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2362_ = lean_array_get_size(v_a_2351_);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_nat_dec_eq(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = lean_unsigned_to_nat(2u);
v___x_2366_ = lean_nat_dec_eq(v___x_2362_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = lean_unsigned_to_nat(3u);
v___x_2368_ = lean_nat_dec_eq(v___x_2362_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v___x_2369_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0));
v___x_2370_ = l_Nat_reprFast(v___x_2362_);
v___x_2371_ = lean_string_append(v___x_2369_, v___x_2370_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2373_ = lean_string_append(v___x_2371_, v___x_2372_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2373_);
v___x_2375_ = v___x_2360_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_a_2358_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
else
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_array_fget_borrowed(v_a_2351_, v___x_2348_);
v___x_2378_ = l_String_Slice_toNat_x3f(v___x_2377_);
if (lean_obj_tag(v___x_2378_) == 1)
{
lean_object* v_val_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_val_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_val_2379_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = lean_array_fget_borrowed(v_a_2351_, v___x_2363_);
v___x_2381_ = l_String_Slice_toNat_x3f(v___x_2380_);
if (lean_obj_tag(v___x_2381_) == 1)
{
lean_object* v_val_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_val_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_val_2382_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = lean_array_fget(v_a_2351_, v___x_2365_);
lean_dec(v_a_2351_);
v___x_2384_ = l_String_Slice_toNat_x3f(v___x_2383_);
if (lean_obj_tag(v___x_2384_) == 1)
{
lean_object* v_val_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_minVer_2390_; 
lean_dec(v___x_2383_);
v_val_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_val_2385_);
lean_dec_ref(v___x_2384_);
lean_inc(v_val_2382_);
lean_inc(v_val_2379_);
v___x_2386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2386_, 0, v_val_2379_);
lean_ctor_set(v___x_2386_, 1, v_val_2382_);
lean_ctor_set(v___x_2386_, 2, v_val_2385_);
v___x_2387_ = lean_nat_add(v_val_2382_, v___x_2363_);
lean_dec(v_val_2382_);
v___x_2388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2388_, 0, v_val_2379_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
lean_ctor_set(v___x_2388_, 2, v___x_2348_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v_a_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2386_);
v_minVer_2390_ = v___x_2354_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_a_2357_);
v_minVer_2390_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v_maxVer_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2391_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2392_, 0, v___x_2388_);
lean_ctor_set(v_maxVer_2392_, 1, v___x_2391_);
v___x_2393_ = 3;
v___x_2394_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2394_, 0, v_minVer_2390_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*1, v___x_2393_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*1 + 1, v___x_2366_);
v___x_2395_ = lean_array_push(v_ands_2346_, v___x_2394_);
v___x_2396_ = 0;
v___x_2397_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2397_, 0, v_maxVer_2392_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1, v___x_2396_);
lean_ctor_set_uint8(v___x_2397_, sizeof(void*)*1 + 1, v___x_2368_);
v___x_2398_ = lean_array_push(v___x_2395_, v___x_2397_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2398_);
v___x_2400_ = v___x_2360_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_a_2358_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
else
{
lean_object* v_str_2403_; lean_object* v_startInclusive_2404_; lean_object* v_endExclusive_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
lean_dec(v___x_2384_);
lean_dec(v_val_2382_);
lean_dec(v_val_2379_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_ands_2346_);
v_str_2403_ = lean_ctor_get(v___x_2383_, 0);
lean_inc_ref(v_str_2403_);
v_startInclusive_2404_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_startInclusive_2404_);
v_endExclusive_2405_ = lean_ctor_get(v___x_2383_, 2);
lean_inc(v_endExclusive_2405_);
lean_dec(v___x_2383_);
v___x_2406_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2407_ = lean_string_utf8_extract(v_str_2403_, v_startInclusive_2404_, v_endExclusive_2405_);
lean_dec(v_endExclusive_2405_);
lean_dec(v_startInclusive_2404_);
lean_dec_ref(v_str_2403_);
v___x_2408_ = lean_string_append(v___x_2406_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2410_ = lean_string_append(v___x_2408_, v___x_2409_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2410_);
v___x_2412_ = v___x_2360_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_a_2358_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
else
{
lean_object* v_str_2414_; lean_object* v_startInclusive_2415_; lean_object* v_endExclusive_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_inc(v___x_2380_);
lean_dec(v___x_2381_);
lean_dec(v_val_2379_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v_str_2414_ = lean_ctor_get(v___x_2380_, 0);
lean_inc_ref(v_str_2414_);
v_startInclusive_2415_ = lean_ctor_get(v___x_2380_, 1);
lean_inc(v_startInclusive_2415_);
v_endExclusive_2416_ = lean_ctor_get(v___x_2380_, 2);
lean_inc(v_endExclusive_2416_);
lean_dec(v___x_2380_);
v___x_2417_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2418_ = lean_string_utf8_extract(v_str_2414_, v_startInclusive_2415_, v_endExclusive_2416_);
lean_dec(v_endExclusive_2416_);
lean_dec(v_startInclusive_2415_);
lean_dec_ref(v_str_2414_);
v___x_2419_ = lean_string_append(v___x_2417_, v___x_2418_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2421_ = lean_string_append(v___x_2419_, v___x_2420_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2421_);
v___x_2423_ = v___x_2360_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_a_2358_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_str_2425_; lean_object* v_startInclusive_2426_; lean_object* v_endExclusive_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
lean_inc(v___x_2377_);
lean_dec(v___x_2378_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v_str_2425_ = lean_ctor_get(v___x_2377_, 0);
lean_inc_ref(v_str_2425_);
v_startInclusive_2426_ = lean_ctor_get(v___x_2377_, 1);
lean_inc(v_startInclusive_2426_);
v_endExclusive_2427_ = lean_ctor_get(v___x_2377_, 2);
lean_inc(v_endExclusive_2427_);
lean_dec(v___x_2377_);
v___x_2428_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2429_ = lean_string_utf8_extract(v_str_2425_, v_startInclusive_2426_, v_endExclusive_2427_);
lean_dec(v_endExclusive_2427_);
lean_dec(v_startInclusive_2426_);
lean_dec_ref(v_str_2425_);
v___x_2430_ = lean_string_append(v___x_2428_, v___x_2429_);
lean_dec_ref(v___x_2429_);
v___x_2431_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2432_ = lean_string_append(v___x_2430_, v___x_2431_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2432_);
v___x_2434_ = v___x_2360_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_a_2358_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_array_fget_borrowed(v_a_2351_, v___x_2348_);
v___x_2437_ = l_String_Slice_toNat_x3f(v___x_2436_);
if (lean_obj_tag(v___x_2437_) == 1)
{
lean_object* v_val_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_val_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_val_2438_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = lean_array_fget(v_a_2351_, v___x_2363_);
lean_dec(v_a_2351_);
v___x_2440_ = l_String_Slice_toNat_x3f(v___x_2439_);
if (lean_obj_tag(v___x_2440_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_minVer_2446_; 
lean_dec(v___x_2439_);
v_val_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc_n(v_val_2441_, 2);
lean_dec_ref(v___x_2440_);
lean_inc(v_val_2438_);
v___x_2442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2442_, 0, v_val_2438_);
lean_ctor_set(v___x_2442_, 1, v_val_2441_);
lean_ctor_set(v___x_2442_, 2, v___x_2348_);
v___x_2443_ = lean_nat_add(v_val_2441_, v___x_2363_);
lean_dec(v_val_2441_);
v___x_2444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2444_, 0, v_val_2438_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
lean_ctor_set(v___x_2444_, 2, v___x_2348_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v_a_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2442_);
v_minVer_2446_ = v___x_2354_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_a_2357_);
v_minVer_2446_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v_maxVer_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2447_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2448_, 0, v___x_2444_);
lean_ctor_set(v_maxVer_2448_, 1, v___x_2447_);
v___x_2449_ = 3;
v___x_2450_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2450_, 0, v_minVer_2446_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*1, v___x_2449_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*1 + 1, v___x_2364_);
v___x_2451_ = lean_array_push(v_ands_2346_, v___x_2450_);
v___x_2452_ = 0;
v___x_2453_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2453_, 0, v_maxVer_2448_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*1, v___x_2452_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*1 + 1, v___x_2366_);
v___x_2454_ = lean_array_push(v___x_2451_, v___x_2453_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2454_);
v___x_2456_ = v___x_2360_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_a_2358_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_str_2459_; lean_object* v_startInclusive_2460_; lean_object* v_endExclusive_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_dec(v___x_2440_);
lean_dec(v_val_2438_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_ands_2346_);
v_str_2459_ = lean_ctor_get(v___x_2439_, 0);
lean_inc_ref(v_str_2459_);
v_startInclusive_2460_ = lean_ctor_get(v___x_2439_, 1);
lean_inc(v_startInclusive_2460_);
v_endExclusive_2461_ = lean_ctor_get(v___x_2439_, 2);
lean_inc(v_endExclusive_2461_);
lean_dec(v___x_2439_);
v___x_2462_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2463_ = lean_string_utf8_extract(v_str_2459_, v_startInclusive_2460_, v_endExclusive_2461_);
lean_dec(v_endExclusive_2461_);
lean_dec(v_startInclusive_2460_);
lean_dec_ref(v_str_2459_);
v___x_2464_ = lean_string_append(v___x_2462_, v___x_2463_);
lean_dec_ref(v___x_2463_);
v___x_2465_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2466_);
v___x_2468_ = v___x_2360_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_a_2358_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
lean_object* v_str_2470_; lean_object* v_startInclusive_2471_; lean_object* v_endExclusive_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
lean_inc(v___x_2436_);
lean_dec(v___x_2437_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v_str_2470_ = lean_ctor_get(v___x_2436_, 0);
lean_inc_ref(v_str_2470_);
v_startInclusive_2471_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_startInclusive_2471_);
v_endExclusive_2472_ = lean_ctor_get(v___x_2436_, 2);
lean_inc(v_endExclusive_2472_);
lean_dec(v___x_2436_);
v___x_2473_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2474_ = lean_string_utf8_extract(v_str_2470_, v_startInclusive_2471_, v_endExclusive_2472_);
lean_dec(v_endExclusive_2472_);
lean_dec(v_startInclusive_2471_);
lean_dec_ref(v_str_2470_);
v___x_2475_ = lean_string_append(v___x_2473_, v___x_2474_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2477_ = lean_string_append(v___x_2475_, v___x_2476_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2477_);
v___x_2479_ = v___x_2360_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_a_2358_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_array_fget(v_a_2351_, v___x_2348_);
lean_dec(v_a_2351_);
v___x_2482_ = l_String_Slice_toNat_x3f(v___x_2481_);
if (lean_obj_tag(v___x_2482_) == 1)
{
lean_object* v_val_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_minVer_2488_; 
lean_dec(v___x_2481_);
v_val_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc_n(v_val_2483_, 2);
lean_dec_ref(v___x_2482_);
v___x_2484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2484_, 0, v_val_2483_);
lean_ctor_set(v___x_2484_, 1, v___x_2348_);
lean_ctor_set(v___x_2484_, 2, v___x_2348_);
v___x_2485_ = lean_nat_add(v_val_2483_, v___x_2363_);
lean_dec(v_val_2483_);
v___x_2486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2348_);
lean_ctor_set(v___x_2486_, 2, v___x_2348_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v_a_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2484_);
v_minVer_2488_ = v___x_2354_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_a_2357_);
v_minVer_2488_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v_maxVer_2490_; uint8_t v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2489_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2490_, 0, v___x_2486_);
lean_ctor_set(v_maxVer_2490_, 1, v___x_2489_);
v___x_2491_ = 3;
v___x_2492_ = 0;
v___x_2493_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2493_, 0, v_minVer_2488_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*1, v___x_2491_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*1 + 1, v___x_2492_);
v___x_2494_ = lean_array_push(v_ands_2346_, v___x_2493_);
v___x_2495_ = 0;
v___x_2496_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2496_, 0, v_maxVer_2490_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*1, v___x_2495_);
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*1 + 1, v___x_2364_);
v___x_2497_ = lean_array_push(v___x_2494_, v___x_2496_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2497_);
v___x_2499_ = v___x_2360_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_a_2358_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
lean_object* v_str_2502_; lean_object* v_startInclusive_2503_; lean_object* v_endExclusive_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
lean_dec(v___x_2482_);
lean_dec(v_a_2357_);
lean_del_object(v___x_2354_);
lean_dec_ref(v_ands_2346_);
v_str_2502_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_ref(v_str_2502_);
v_startInclusive_2503_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_startInclusive_2503_);
v_endExclusive_2504_ = lean_ctor_get(v___x_2481_, 2);
lean_inc(v_endExclusive_2504_);
lean_dec(v___x_2481_);
v___x_2505_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2506_ = lean_string_utf8_extract(v_str_2502_, v_startInclusive_2503_, v_endExclusive_2504_);
lean_dec(v_endExclusive_2504_);
lean_dec(v_startInclusive_2503_);
lean_dec_ref(v_str_2502_);
v___x_2507_ = lean_string_append(v___x_2505_, v___x_2506_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2509_ = lean_string_append(v___x_2507_, v___x_2508_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
lean_ctor_set(v___x_2360_, 0, v___x_2509_);
v___x_2511_ = v___x_2360_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_a_2358_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_del_object(v___x_2354_);
lean_dec(v_a_2351_);
lean_dec_ref(v_ands_2346_);
v_a_2514_ = lean_ctor_get(v___x_2356_, 0);
v_a_2515_ = lean_ctor_get(v___x_2356_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2356_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_inc(v_a_2514_);
lean_dec(v___x_2356_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2514_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(lean_object* v_s_2526_, lean_object* v_ands_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_a_2532_; lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2755_; 
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2528_);
lean_inc_ref(v_s_2526_);
v___x_2531_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2526_, v___x_2530_, v_a_2528_, v_a_2528_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_a_2533_ = lean_ctor_get(v___x_2531_, 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2535_ = v___x_2531_;
v_isShared_2536_ = v_isSharedCheck_2755_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2755_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; 
v___x_2537_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_2526_, v_a_2533_);
lean_dec_ref(v_s_2526_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2745_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_a_2539_ = lean_ctor_get(v___x_2537_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2541_ = v___x_2537_;
v_isShared_2542_ = v_isSharedCheck_2745_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2745_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2543_ = lean_array_get_size(v_a_2532_);
v___x_2544_ = lean_unsigned_to_nat(1u);
v___x_2545_ = lean_nat_dec_eq(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2546_ = lean_unsigned_to_nat(2u);
v___x_2547_ = lean_nat_dec_eq(v___x_2543_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = lean_unsigned_to_nat(3u);
v___x_2549_ = lean_nat_dec_eq(v___x_2543_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_dec(v_a_2538_);
lean_del_object(v___x_2535_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v___x_2550_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0));
v___x_2551_ = l_Nat_reprFast(v___x_2543_);
v___x_2552_ = lean_string_append(v___x_2550_, v___x_2551_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2554_ = lean_string_append(v___x_2552_, v___x_2553_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2554_);
v___x_2556_ = v___x_2541_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_a_2539_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_array_fget_borrowed(v_a_2532_, v___x_2529_);
v___x_2559_ = l_String_Slice_toNat_x3f(v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 1)
{
lean_object* v_val_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_val_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_val_2560_);
lean_dec_ref(v___x_2559_);
v___x_2561_ = lean_array_fget_borrowed(v_a_2532_, v___x_2544_);
v___x_2562_ = l_String_Slice_toNat_x3f(v___x_2561_);
if (lean_obj_tag(v___x_2562_) == 1)
{
lean_object* v_val_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_val_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_val_2563_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = lean_array_fget(v_a_2532_, v___x_2546_);
lean_dec(v_a_2532_);
v___x_2565_ = l_String_Slice_toNat_x3f(v___x_2564_);
if (lean_obj_tag(v___x_2565_) == 1)
{
lean_object* v_val_2566_; uint8_t v___y_2568_; uint8_t v___x_2588_; 
lean_dec(v___x_2564_);
v_val_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_val_2566_);
lean_dec_ref(v___x_2565_);
v___x_2588_ = lean_nat_dec_eq(v_val_2560_, v___x_2529_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v_minVer_2592_; lean_object* v___x_2593_; lean_object* v_maxVer_2594_; uint8_t v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_del_object(v___x_2541_);
lean_inc(v_val_2560_);
v___x_2589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2589_, 0, v_val_2560_);
lean_ctor_set(v___x_2589_, 1, v_val_2563_);
lean_ctor_set(v___x_2589_, 2, v_val_2566_);
v___x_2590_ = lean_nat_add(v_val_2560_, v___x_2544_);
lean_dec(v_val_2560_);
v___x_2591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___x_2529_);
lean_ctor_set(v___x_2591_, 2, v___x_2529_);
v_minVer_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2592_, 0, v___x_2589_);
lean_ctor_set(v_minVer_2592_, 1, v_a_2538_);
v___x_2593_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2594_, 0, v___x_2591_);
lean_ctor_set(v_maxVer_2594_, 1, v___x_2593_);
v___x_2595_ = 3;
v___x_2596_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2596_, 0, v_minVer_2592_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*1, v___x_2595_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*1 + 1, v___x_2588_);
v___x_2597_ = lean_array_push(v_ands_2527_, v___x_2596_);
v___x_2598_ = 0;
v___x_2599_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2599_, 0, v_maxVer_2594_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*1, v___x_2598_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*1 + 1, v___x_2549_);
v___x_2600_ = lean_array_push(v___x_2597_, v___x_2599_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v_a_2539_);
lean_ctor_set(v___x_2535_, 0, v___x_2600_);
v___x_2602_ = v___x_2535_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_a_2539_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
else
{
uint8_t v___x_2604_; 
v___x_2604_ = lean_nat_dec_eq(v_val_2563_, v___x_2529_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v_minVer_2608_; lean_object* v___x_2609_; lean_object* v_maxVer_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_del_object(v___x_2541_);
lean_inc(v_val_2563_);
lean_inc(v_val_2560_);
v___x_2605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2605_, 0, v_val_2560_);
lean_ctor_set(v___x_2605_, 1, v_val_2563_);
lean_ctor_set(v___x_2605_, 2, v_val_2566_);
v___x_2606_ = lean_nat_add(v_val_2563_, v___x_2544_);
lean_dec(v_val_2563_);
v___x_2607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2607_, 0, v_val_2560_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_ctor_set(v___x_2607_, 2, v___x_2529_);
v_minVer_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2608_, 0, v___x_2605_);
lean_ctor_set(v_minVer_2608_, 1, v_a_2538_);
v___x_2609_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2610_, 0, v___x_2607_);
lean_ctor_set(v_maxVer_2610_, 1, v___x_2609_);
v___x_2611_ = 3;
v___x_2612_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2612_, 0, v_minVer_2608_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*1, v___x_2611_);
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*1 + 1, v___x_2604_);
v___x_2613_ = lean_array_push(v_ands_2527_, v___x_2612_);
v___x_2614_ = 0;
v___x_2615_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2615_, 0, v_maxVer_2610_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*1, v___x_2614_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*1 + 1, v___x_2588_);
v___x_2616_ = lean_array_push(v___x_2613_, v___x_2615_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 1, v_a_2539_);
lean_ctor_set(v___x_2535_, 0, v___x_2616_);
v___x_2618_ = v___x_2535_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_a_2539_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
else
{
uint8_t v___x_2620_; 
lean_del_object(v___x_2535_);
v___x_2620_ = lean_nat_dec_eq(v_val_2566_, v___x_2529_);
if (v___x_2620_ == 0)
{
v___y_2568_ = v___x_2620_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = lean_string_utf8_byte_size(v_a_2538_);
v___x_2622_ = lean_nat_dec_eq(v___x_2621_, v___x_2529_);
v___y_2568_ = v___x_2622_;
goto v___jp_2567_;
}
}
}
v___jp_2567_:
{
if (v___y_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v_minVer_2572_; lean_object* v___x_2573_; lean_object* v_maxVer_2574_; uint8_t v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_inc(v_val_2566_);
lean_inc(v_val_2563_);
lean_inc(v_val_2560_);
v___x_2569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2569_, 0, v_val_2560_);
lean_ctor_set(v___x_2569_, 1, v_val_2563_);
lean_ctor_set(v___x_2569_, 2, v_val_2566_);
v___x_2570_ = lean_nat_add(v_val_2566_, v___x_2544_);
lean_dec(v_val_2566_);
v___x_2571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2571_, 0, v_val_2560_);
lean_ctor_set(v___x_2571_, 1, v_val_2563_);
lean_ctor_set(v___x_2571_, 2, v___x_2570_);
v_minVer_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2572_, 0, v___x_2569_);
lean_ctor_set(v_minVer_2572_, 1, v_a_2538_);
v___x_2573_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2574_, 0, v___x_2571_);
lean_ctor_set(v_maxVer_2574_, 1, v___x_2573_);
v___x_2575_ = 3;
v___x_2576_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2576_, 0, v_minVer_2572_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*1, v___x_2575_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*1 + 1, v___y_2568_);
v___x_2577_ = lean_array_push(v_ands_2527_, v___x_2576_);
v___x_2578_ = 0;
v___x_2579_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2579_, 0, v_maxVer_2574_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*1, v___x_2578_);
lean_ctor_set_uint8(v___x_2579_, sizeof(void*)*1 + 1, v___x_2549_);
v___x_2580_ = lean_array_push(v___x_2577_, v___x_2579_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2580_);
v___x_2582_ = v___x_2541_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_a_2539_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_dec(v_val_2566_);
lean_dec(v_val_2563_);
lean_dec(v_val_2560_);
lean_dec(v_a_2538_);
lean_dec_ref(v_ands_2527_);
v___x_2584_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1));
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2584_);
v___x_2586_ = v___x_2541_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_a_2539_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_str_2623_; lean_object* v_startInclusive_2624_; lean_object* v_endExclusive_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; 
lean_dec(v___x_2565_);
lean_dec(v_val_2563_);
lean_dec(v_val_2560_);
lean_dec(v_a_2538_);
lean_del_object(v___x_2535_);
lean_dec_ref(v_ands_2527_);
v_str_2623_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_ref(v_str_2623_);
v_startInclusive_2624_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_startInclusive_2624_);
v_endExclusive_2625_ = lean_ctor_get(v___x_2564_, 2);
lean_inc(v_endExclusive_2625_);
lean_dec(v___x_2564_);
v___x_2626_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3));
v___x_2627_ = lean_string_utf8_extract(v_str_2623_, v_startInclusive_2624_, v_endExclusive_2625_);
lean_dec(v_endExclusive_2625_);
lean_dec(v_startInclusive_2624_);
lean_dec_ref(v_str_2623_);
v___x_2628_ = lean_string_append(v___x_2626_, v___x_2627_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2630_ = lean_string_append(v___x_2628_, v___x_2629_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2630_);
v___x_2632_ = v___x_2541_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_a_2539_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
else
{
lean_object* v_str_2634_; lean_object* v_startInclusive_2635_; lean_object* v_endExclusive_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_inc(v___x_2561_);
lean_dec(v___x_2562_);
lean_dec(v_val_2560_);
lean_dec(v_a_2538_);
lean_del_object(v___x_2535_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v_str_2634_ = lean_ctor_get(v___x_2561_, 0);
lean_inc_ref(v_str_2634_);
v_startInclusive_2635_ = lean_ctor_get(v___x_2561_, 1);
lean_inc(v_startInclusive_2635_);
v_endExclusive_2636_ = lean_ctor_get(v___x_2561_, 2);
lean_inc(v_endExclusive_2636_);
lean_dec(v___x_2561_);
v___x_2637_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2638_ = lean_string_utf8_extract(v_str_2634_, v_startInclusive_2635_, v_endExclusive_2636_);
lean_dec(v_endExclusive_2636_);
lean_dec(v_startInclusive_2635_);
lean_dec_ref(v_str_2634_);
v___x_2639_ = lean_string_append(v___x_2637_, v___x_2638_);
lean_dec_ref(v___x_2638_);
v___x_2640_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2641_);
v___x_2643_ = v___x_2541_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_a_2539_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
lean_object* v_str_2645_; lean_object* v_startInclusive_2646_; lean_object* v_endExclusive_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_inc(v___x_2558_);
lean_dec(v___x_2559_);
lean_dec(v_a_2538_);
lean_del_object(v___x_2535_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v_str_2645_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_ref(v_str_2645_);
v_startInclusive_2646_ = lean_ctor_get(v___x_2558_, 1);
lean_inc(v_startInclusive_2646_);
v_endExclusive_2647_ = lean_ctor_get(v___x_2558_, 2);
lean_inc(v_endExclusive_2647_);
lean_dec(v___x_2558_);
v___x_2648_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2649_ = lean_string_utf8_extract(v_str_2645_, v_startInclusive_2646_, v_endExclusive_2647_);
lean_dec(v_endExclusive_2647_);
lean_dec(v_startInclusive_2646_);
lean_dec_ref(v_str_2645_);
v___x_2650_ = lean_string_append(v___x_2648_, v___x_2649_);
lean_dec_ref(v___x_2649_);
v___x_2651_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2652_ = lean_string_append(v___x_2650_, v___x_2651_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2652_);
v___x_2654_ = v___x_2541_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_a_2539_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_del_object(v___x_2535_);
v___x_2656_ = lean_array_fget_borrowed(v_a_2532_, v___x_2529_);
v___x_2657_ = l_String_Slice_toNat_x3f(v___x_2656_);
if (lean_obj_tag(v___x_2657_) == 1)
{
lean_object* v_val_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v_val_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_val_2658_);
lean_dec_ref(v___x_2657_);
v___x_2659_ = lean_array_fget(v_a_2532_, v___x_2544_);
lean_dec(v_a_2532_);
v___x_2660_ = l_String_Slice_toNat_x3f(v___x_2659_);
if (lean_obj_tag(v___x_2660_) == 1)
{
lean_object* v_val_2661_; uint8_t v___x_2662_; 
lean_dec(v___x_2659_);
v_val_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_val_2661_);
lean_dec_ref(v___x_2660_);
v___x_2662_ = lean_nat_dec_eq(v_val_2658_, v___x_2529_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v_minVer_2666_; lean_object* v___x_2667_; lean_object* v_maxVer_2668_; uint8_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_inc(v_val_2658_);
v___x_2663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2663_, 0, v_val_2658_);
lean_ctor_set(v___x_2663_, 1, v_val_2661_);
lean_ctor_set(v___x_2663_, 2, v___x_2529_);
v___x_2664_ = lean_nat_add(v_val_2658_, v___x_2544_);
lean_dec(v_val_2658_);
v___x_2665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v___x_2529_);
lean_ctor_set(v___x_2665_, 2, v___x_2529_);
v_minVer_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2666_, 0, v___x_2663_);
lean_ctor_set(v_minVer_2666_, 1, v_a_2538_);
v___x_2667_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2668_, 0, v___x_2665_);
lean_ctor_set(v_maxVer_2668_, 1, v___x_2667_);
v___x_2669_ = 3;
v___x_2670_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2670_, 0, v_minVer_2666_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*1, v___x_2669_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*1 + 1, v___x_2662_);
v___x_2671_ = lean_array_push(v_ands_2527_, v___x_2670_);
v___x_2672_ = 0;
v___x_2673_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2673_, 0, v_maxVer_2668_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*1, v___x_2672_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*1 + 1, v___x_2547_);
v___x_2674_ = lean_array_push(v___x_2671_, v___x_2673_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2674_);
v___x_2676_ = v___x_2541_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2539_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_minVer_2681_; lean_object* v___x_2682_; lean_object* v_maxVer_2683_; uint8_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
lean_inc(v_val_2661_);
lean_inc(v_val_2658_);
v___x_2678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2678_, 0, v_val_2658_);
lean_ctor_set(v___x_2678_, 1, v_val_2661_);
lean_ctor_set(v___x_2678_, 2, v___x_2529_);
v___x_2679_ = lean_nat_add(v_val_2661_, v___x_2544_);
lean_dec(v_val_2661_);
v___x_2680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2680_, 0, v_val_2658_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
lean_ctor_set(v___x_2680_, 2, v___x_2529_);
v_minVer_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2681_, 0, v___x_2678_);
lean_ctor_set(v_minVer_2681_, 1, v_a_2538_);
v___x_2682_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2683_, 0, v___x_2680_);
lean_ctor_set(v_maxVer_2683_, 1, v___x_2682_);
v___x_2684_ = 3;
v___x_2685_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2685_, 0, v_minVer_2681_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*1, v___x_2684_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*1 + 1, v___x_2545_);
v___x_2686_ = lean_array_push(v_ands_2527_, v___x_2685_);
v___x_2687_ = 0;
v___x_2688_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2688_, 0, v_maxVer_2683_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*1, v___x_2687_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*1 + 1, v___x_2662_);
v___x_2689_ = lean_array_push(v___x_2686_, v___x_2688_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2689_);
v___x_2691_ = v___x_2541_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_a_2539_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_str_2693_; lean_object* v_startInclusive_2694_; lean_object* v_endExclusive_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_dec(v___x_2660_);
lean_dec(v_val_2658_);
lean_dec(v_a_2538_);
lean_dec_ref(v_ands_2527_);
v_str_2693_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_ref(v_str_2693_);
v_startInclusive_2694_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_startInclusive_2694_);
v_endExclusive_2695_ = lean_ctor_get(v___x_2659_, 2);
lean_inc(v_endExclusive_2695_);
lean_dec(v___x_2659_);
v___x_2696_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4));
v___x_2697_ = lean_string_utf8_extract(v_str_2693_, v_startInclusive_2694_, v_endExclusive_2695_);
lean_dec(v_endExclusive_2695_);
lean_dec(v_startInclusive_2694_);
lean_dec_ref(v_str_2693_);
v___x_2698_ = lean_string_append(v___x_2696_, v___x_2697_);
lean_dec_ref(v___x_2697_);
v___x_2699_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2700_ = lean_string_append(v___x_2698_, v___x_2699_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2700_);
v___x_2702_ = v___x_2541_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_a_2539_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
else
{
lean_object* v_str_2704_; lean_object* v_startInclusive_2705_; lean_object* v_endExclusive_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_inc(v___x_2656_);
lean_dec(v___x_2657_);
lean_dec(v_a_2538_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v_str_2704_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_ref(v_str_2704_);
v_startInclusive_2705_ = lean_ctor_get(v___x_2656_, 1);
lean_inc(v_startInclusive_2705_);
v_endExclusive_2706_ = lean_ctor_get(v___x_2656_, 2);
lean_inc(v_endExclusive_2706_);
lean_dec(v___x_2656_);
v___x_2707_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2708_ = lean_string_utf8_extract(v_str_2704_, v_startInclusive_2705_, v_endExclusive_2706_);
lean_dec(v_endExclusive_2706_);
lean_dec(v_startInclusive_2705_);
lean_dec_ref(v_str_2704_);
v___x_2709_ = lean_string_append(v___x_2707_, v___x_2708_);
lean_dec_ref(v___x_2708_);
v___x_2710_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2711_ = lean_string_append(v___x_2709_, v___x_2710_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2711_);
v___x_2713_ = v___x_2541_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2711_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_a_2539_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_del_object(v___x_2535_);
v___x_2715_ = lean_array_fget(v_a_2532_, v___x_2529_);
lean_dec(v_a_2532_);
v___x_2716_ = l_String_Slice_toNat_x3f(v___x_2715_);
if (lean_obj_tag(v___x_2716_) == 1)
{
lean_object* v_val_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v_minVer_2721_; lean_object* v___x_2722_; lean_object* v_maxVer_2723_; uint8_t v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
lean_dec(v___x_2715_);
v_val_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc_n(v_val_2717_, 2);
lean_dec_ref(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2718_, 0, v_val_2717_);
lean_ctor_set(v___x_2718_, 1, v___x_2529_);
lean_ctor_set(v___x_2718_, 2, v___x_2529_);
v___x_2719_ = lean_nat_add(v_val_2717_, v___x_2544_);
lean_dec(v_val_2717_);
v___x_2720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v___x_2529_);
lean_ctor_set(v___x_2720_, 2, v___x_2529_);
v_minVer_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2721_, 0, v___x_2718_);
lean_ctor_set(v_minVer_2721_, 1, v_a_2538_);
v___x_2722_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_maxVer_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2723_, 0, v___x_2720_);
lean_ctor_set(v_maxVer_2723_, 1, v___x_2722_);
v___x_2724_ = 3;
v___x_2725_ = 0;
v___x_2726_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2726_, 0, v_minVer_2721_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*1, v___x_2724_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*1 + 1, v___x_2725_);
v___x_2727_ = lean_array_push(v_ands_2527_, v___x_2726_);
v___x_2728_ = 0;
v___x_2729_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2729_, 0, v_maxVer_2723_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1, v___x_2728_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1 + 1, v___x_2545_);
v___x_2730_ = lean_array_push(v___x_2727_, v___x_2729_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2730_);
v___x_2732_ = v___x_2541_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_a_2539_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
else
{
lean_object* v_str_2734_; lean_object* v_startInclusive_2735_; lean_object* v_endExclusive_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_dec(v___x_2716_);
lean_dec(v_a_2538_);
lean_dec_ref(v_ands_2527_);
v_str_2734_ = lean_ctor_get(v___x_2715_, 0);
lean_inc_ref(v_str_2734_);
v_startInclusive_2735_ = lean_ctor_get(v___x_2715_, 1);
lean_inc(v_startInclusive_2735_);
v_endExclusive_2736_ = lean_ctor_get(v___x_2715_, 2);
lean_inc(v_endExclusive_2736_);
lean_dec(v___x_2715_);
v___x_2737_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5));
v___x_2738_ = lean_string_utf8_extract(v_str_2734_, v_startInclusive_2735_, v_endExclusive_2736_);
lean_dec(v_endExclusive_2736_);
lean_dec(v_startInclusive_2735_);
lean_dec_ref(v_str_2734_);
v___x_2739_ = lean_string_append(v___x_2737_, v___x_2738_);
lean_dec_ref(v___x_2738_);
v___x_2740_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2));
v___x_2741_ = lean_string_append(v___x_2739_, v___x_2740_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2741_);
v___x_2743_ = v___x_2541_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_a_2539_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_del_object(v___x_2535_);
lean_dec(v_a_2532_);
lean_dec_ref(v_ands_2527_);
v_a_2746_ = lean_ctor_get(v___x_2537_, 0);
v_a_2747_ = lean_ctor_get(v___x_2537_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2537_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_inc(v_a_2746_);
lean_dec(v___x_2537_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2746_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(lean_object* v_s_2761_, lean_object* v_ands_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___y_2765_; lean_object* v___y_2769_; lean_object* v___y_2774_; lean_object* v___x_2777_; uint8_t v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v_a_2867_; lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2952_; 
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2865_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0));
lean_inc(v_a_2763_);
lean_inc_ref(v_s_2761_);
v___x_2866_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(v_s_2761_, v___x_2865_, v_a_2763_, v_a_2763_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_a_2868_ = lean_ctor_get(v___x_2866_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2870_ = v___x_2866_;
v_isShared_2871_ = v_isSharedCheck_2952_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2952_;
goto v_resetjp_2869_;
}
v___jp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0));
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___y_2765_);
return v___x_2767_;
}
v___jp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = ((lean_object*)(l_Lake_VerComparator_wild));
v___x_2771_ = lean_array_push(v_ands_2762_, v___x_2770_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v___y_2769_);
return v___x_2772_;
}
v___jp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1));
v___x_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
lean_ctor_set(v___x_2776_, 1, v___y_2774_);
return v___x_2776_;
}
v___jp_2778_:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2784_, v___y_2785_, v___y_2781_);
lean_dec(v___y_2785_);
if (lean_obj_tag(v___x_2786_) == 0)
{
switch(lean_obj_tag(v___y_2782_))
{
case 2:
{
switch(lean_obj_tag(v___y_2780_))
{
case 2:
{
lean_object* v_a_2787_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
if (lean_obj_tag(v_a_2787_) == 1)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2810_; 
v_a_2788_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; 
v_unused_2811_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2811_);
v___x_2790_ = v___x_2786_;
v_isShared_2791_ = v_isSharedCheck_2810_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2786_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2810_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v_n_2792_; lean_object* v_n_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v_minVer_2798_; lean_object* v_maxVer_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
v_n_2792_ = lean_ctor_get(v___y_2782_, 0);
lean_inc_n(v_n_2792_, 2);
lean_dec_ref(v___y_2782_);
v_n_2793_ = lean_ctor_get(v___y_2780_, 0);
lean_inc_n(v_n_2793_, 2);
lean_dec_ref(v___y_2780_);
v___x_2794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2794_, 0, v_n_2792_);
lean_ctor_set(v___x_2794_, 1, v_n_2793_);
lean_ctor_set(v___x_2794_, 2, v___x_2777_);
v___x_2795_ = lean_nat_add(v_n_2793_, v___y_2783_);
lean_dec(v_n_2793_);
v___x_2796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2796_, 0, v_n_2792_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
lean_ctor_set(v___x_2796_, 2, v___x_2777_);
v___x_2797_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2798_, 0, v___x_2794_);
lean_ctor_set(v_minVer_2798_, 1, v___x_2797_);
v_maxVer_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2799_, 0, v___x_2796_);
lean_ctor_set(v_maxVer_2799_, 1, v___x_2797_);
v___x_2800_ = 3;
v___x_2801_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2801_, 0, v_minVer_2798_);
lean_ctor_set_uint8(v___x_2801_, sizeof(void*)*1, v___x_2800_);
lean_ctor_set_uint8(v___x_2801_, sizeof(void*)*1 + 1, v___y_2779_);
v___x_2802_ = lean_array_push(v_ands_2762_, v___x_2801_);
v___x_2803_ = 0;
v___x_2804_ = 1;
v___x_2805_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2805_, 0, v_maxVer_2799_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1, v___x_2803_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*1 + 1, v___x_2804_);
v___x_2806_ = lean_array_push(v___x_2802_, v___x_2805_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2806_);
v___x_2808_ = v___x_2790_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_a_2788_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2812_; 
lean_dec(v_a_2787_);
lean_dec_ref(v___y_2780_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v_ands_2762_);
v_a_2812_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2812_);
lean_dec_ref(v___x_2786_);
v___y_2765_ = v_a_2812_;
goto v___jp_2764_;
}
}
case 1:
{
lean_object* v_a_2813_; 
v_a_2813_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2813_);
if (lean_obj_tag(v_a_2813_) == 2)
{
lean_object* v_a_2814_; 
lean_dec_ref(v_a_2813_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v_ands_2762_);
v_a_2814_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2814_);
lean_dec_ref(v___x_2786_);
v___y_2774_ = v_a_2814_;
goto v___jp_2773_;
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_a_2813_);
v_a_2815_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2837_);
v___x_2817_ = v___x_2786_;
v_isShared_2818_ = v_isSharedCheck_2836_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2786_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2836_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_n_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v_minVer_2824_; lean_object* v_maxVer_2825_; uint8_t v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; uint8_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v_n_2819_ = lean_ctor_get(v___y_2782_, 0);
lean_inc_n(v_n_2819_, 2);
lean_dec_ref(v___y_2782_);
v___x_2820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2820_, 0, v_n_2819_);
lean_ctor_set(v___x_2820_, 1, v___x_2777_);
lean_ctor_set(v___x_2820_, 2, v___x_2777_);
v___x_2821_ = lean_nat_add(v_n_2819_, v___y_2783_);
lean_dec(v_n_2819_);
v___x_2822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
lean_ctor_set(v___x_2822_, 1, v___x_2777_);
lean_ctor_set(v___x_2822_, 2, v___x_2777_);
v___x_2823_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1));
v_minVer_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_minVer_2824_, 0, v___x_2820_);
lean_ctor_set(v_minVer_2824_, 1, v___x_2823_);
v_maxVer_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_maxVer_2825_, 0, v___x_2822_);
lean_ctor_set(v_maxVer_2825_, 1, v___x_2823_);
v___x_2826_ = 3;
v___x_2827_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2827_, 0, v_minVer_2824_);
lean_ctor_set_uint8(v___x_2827_, sizeof(void*)*1, v___x_2826_);
lean_ctor_set_uint8(v___x_2827_, sizeof(void*)*1 + 1, v___y_2779_);
v___x_2828_ = lean_array_push(v_ands_2762_, v___x_2827_);
v___x_2829_ = 0;
v___x_2830_ = 1;
v___x_2831_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_2831_, 0, v_maxVer_2825_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*1, v___x_2829_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*1 + 1, v___x_2830_);
v___x_2832_ = lean_array_push(v___x_2828_, v___x_2831_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2832_);
v___x_2834_ = v___x_2817_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_a_2815_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
default: 
{
lean_object* v_a_2838_; 
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2780_);
lean_dec_ref(v_ands_2762_);
v_a_2838_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2838_);
lean_dec_ref(v___x_2786_);
v___y_2765_ = v_a_2838_;
goto v___jp_2764_;
}
}
}
case 1:
{
lean_object* v_a_2839_; 
v_a_2839_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2839_);
if (lean_obj_tag(v_a_2839_) == 2)
{
lean_object* v_a_2840_; 
lean_dec_ref(v_a_2839_);
lean_dec(v___y_2780_);
lean_dec_ref(v_ands_2762_);
v_a_2840_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2840_);
lean_dec_ref(v___x_2786_);
v___y_2774_ = v_a_2840_;
goto v___jp_2773_;
}
else
{
lean_dec(v_a_2839_);
if (lean_obj_tag(v___y_2780_) == 2)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v___y_2780_);
lean_dec_ref(v_ands_2762_);
v_a_2841_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2850_);
v___x_2843_ = v___x_2786_;
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2786_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2845_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2));
if (v_isShared_2844_ == 0)
{
lean_ctor_set_tag(v___x_2843_, 1);
lean_ctor_set(v___x_2843_, 0, v___x_2845_);
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_a_2841_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
else
{
lean_object* v_a_2851_; 
lean_dec(v___y_2780_);
v_a_2851_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2786_);
v___y_2769_ = v_a_2851_;
goto v___jp_2768_;
}
}
}
default: 
{
lean_dec(v___y_2782_);
if (lean_obj_tag(v___y_2780_) == 1)
{
lean_object* v_a_2852_; 
v_a_2852_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2852_);
if (lean_obj_tag(v_a_2852_) == 2)
{
lean_object* v_a_2853_; 
lean_dec_ref(v_a_2852_);
lean_dec_ref(v_ands_2762_);
v_a_2853_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2853_);
lean_dec_ref(v___x_2786_);
v___y_2774_ = v_a_2853_;
goto v___jp_2773_;
}
else
{
lean_object* v_a_2854_; 
lean_dec(v_a_2852_);
v_a_2854_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2854_);
lean_dec_ref(v___x_2786_);
v___y_2769_ = v_a_2854_;
goto v___jp_2768_;
}
}
else
{
lean_object* v_a_2855_; 
lean_dec(v___y_2780_);
v_a_2855_ = lean_ctor_get(v___x_2786_, 1);
lean_inc(v_a_2855_);
lean_dec_ref(v___x_2786_);
v___y_2769_ = v_a_2855_;
goto v___jp_2768_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v___y_2782_);
lean_dec(v___y_2780_);
lean_dec_ref(v_ands_2762_);
v_a_2856_ = lean_ctor_get(v___x_2786_, 0);
v_a_2857_ = lean_ctor_get(v___x_2786_, 1);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2786_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_inc(v_a_2856_);
lean_dec(v___x_2786_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2856_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
v_resetjp_2869_:
{
lean_object* v___y_2873_; uint8_t v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; uint8_t v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; uint8_t v___y_2932_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2942_ = lean_string_utf8_byte_size(v_s_2761_);
v___x_2943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2943_, 0, v_s_2761_);
lean_ctor_set(v___x_2943_, 1, v___x_2777_);
lean_ctor_set(v___x_2943_, 2, v___x_2942_);
v___x_2944_ = l_String_Slice_Pos_get_x3f(v___x_2943_, v_a_2868_);
lean_dec_ref(v___x_2943_);
if (lean_obj_tag(v___x_2944_) == 0)
{
uint8_t v___x_2945_; 
v___x_2945_ = 0;
v___y_2932_ = v___x_2945_;
goto v___jp_2931_;
}
else
{
lean_object* v_val_2946_; uint32_t v___x_2947_; uint32_t v___x_2948_; uint8_t v___x_2949_; 
v_val_2946_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_val_2946_);
lean_dec_ref(v___x_2944_);
v___x_2947_ = 45;
v___x_2948_ = lean_unbox_uint32(v_val_2946_);
lean_dec(v_val_2946_);
v___x_2949_ = lean_uint32_dec_eq(v___x_2948_, v___x_2947_);
if (v___x_2949_ == 0)
{
v___y_2932_ = v___x_2949_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
lean_del_object(v___x_2870_);
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v___x_2950_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4));
v___x_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_a_2868_);
return v___x_2951_;
}
}
v___jp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2874_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3));
v___x_2875_ = l_Nat_reprFast(v___y_2873_);
v___x_2876_ = lean_string_append(v___x_2874_, v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1));
v___x_2878_ = lean_string_append(v___x_2876_, v___x_2877_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 1);
lean_ctor_set(v___x_2870_, 0, v___x_2878_);
v___x_2880_ = v___x_2870_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_a_2868_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
v___jp_2882_:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2884_, v___y_2889_, v___y_2886_);
lean_dec(v___y_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
v_a_2892_ = lean_ctor_get(v___x_2890_, 1);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2890_);
v___x_2893_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__12));
v___x_2894_ = lean_unsigned_to_nat(2u);
v___x_2895_ = lean_nat_dec_lt(v___x_2894_, v___y_2888_);
lean_dec(v___y_2888_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_dec(v_a_2867_);
v___x_2896_ = lean_box(0);
v___y_2779_ = v___y_2883_;
v___y_2780_ = v_a_2891_;
v___y_2781_ = v_a_2892_;
v___y_2782_ = v___y_2885_;
v___y_2783_ = v___y_2887_;
v___y_2784_ = v___x_2893_;
v___y_2785_ = v___x_2896_;
goto v___jp_2778_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_array_fget(v_a_2867_, v___x_2894_);
lean_dec(v_a_2867_);
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
v___y_2779_ = v___y_2883_;
v___y_2780_ = v_a_2891_;
v___y_2781_ = v_a_2892_;
v___y_2782_ = v___y_2885_;
v___y_2783_ = v___y_2887_;
v___y_2784_ = v___x_2893_;
v___y_2785_ = v___x_2898_;
goto v___jp_2778_;
}
}
else
{
lean_object* v_a_2899_; lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v___y_2888_);
lean_dec(v___y_2885_);
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v_a_2899_ = lean_ctor_get(v___x_2890_, 0);
v_a_2900_ = lean_ctor_get(v___x_2890_, 1);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2890_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_inc(v_a_2899_);
lean_dec(v___x_2890_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2899_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
v___jp_2908_:
{
lean_object* v___x_2913_; 
v___x_2913_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(v___y_2911_, v___y_2912_, v_a_2868_);
lean_dec(v___y_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
v_a_2915_ = lean_ctor_get(v___x_2913_, 1);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2913_);
v___x_2916_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__10));
v___x_2917_ = lean_unsigned_to_nat(1u);
v___x_2918_ = lean_nat_dec_lt(v___x_2917_, v___y_2910_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_box(0);
v___y_2883_ = v___y_2909_;
v___y_2884_ = v___x_2916_;
v___y_2885_ = v_a_2914_;
v___y_2886_ = v_a_2915_;
v___y_2887_ = v___x_2917_;
v___y_2888_ = v___y_2910_;
v___y_2889_ = v___x_2919_;
goto v___jp_2882_;
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_array_fget_borrowed(v_a_2867_, v___x_2917_);
lean_inc(v___x_2920_);
v___x_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
v___y_2883_ = v___y_2909_;
v___y_2884_ = v___x_2916_;
v___y_2885_ = v_a_2914_;
v___y_2886_ = v_a_2915_;
v___y_2887_ = v___x_2917_;
v___y_2888_ = v___y_2910_;
v___y_2889_ = v___x_2921_;
goto v___jp_2882_;
}
}
else
{
lean_object* v_a_2922_; lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v___y_2910_);
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v_a_2922_ = lean_ctor_get(v___x_2913_, 0);
v_a_2923_ = lean_ctor_get(v___x_2913_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2913_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_inc(v_a_2922_);
lean_dec(v___x_2913_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2922_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
v___jp_2931_:
{
lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = lean_array_get_size(v_a_2867_);
v___x_2934_ = lean_nat_dec_eq(v___x_2933_, v___x_2777_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = lean_unsigned_to_nat(3u);
v___x_2936_ = lean_nat_dec_lt(v___x_2935_, v___x_2933_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; uint8_t v___x_2938_; 
lean_del_object(v___x_2870_);
v___x_2937_ = ((lean_object*)(l_Lake_instReprSemVerCore_repr___redArg___closed__1));
v___x_2938_ = lean_nat_dec_lt(v___x_2777_, v___x_2933_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_box(0);
v___y_2909_ = v___y_2932_;
v___y_2910_ = v___x_2933_;
v___y_2911_ = v___x_2937_;
v___y_2912_ = v___x_2939_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_array_fget_borrowed(v_a_2867_, v___x_2777_);
lean_inc(v___x_2940_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
v___y_2909_ = v___y_2932_;
v___y_2910_ = v___x_2933_;
v___y_2911_ = v___x_2937_;
v___y_2912_ = v___x_2941_;
goto v___jp_2908_;
}
}
else
{
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v___y_2873_ = v___x_2933_;
goto v___jp_2872_;
}
}
else
{
lean_dec(v_a_2867_);
lean_dec_ref(v_ands_2762_);
v___y_2873_ = v___x_2933_;
goto v___jp_2872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(lean_object* v_s_2957_, uint8_t v_needsRange_2958_, lean_object* v_ors_2959_, lean_object* v_ands_2960_, lean_object* v_p_2961_){
_start:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_string_utf8_byte_size(v_s_2957_);
v___x_2969_ = lean_nat_dec_eq(v_p_2961_, v___x_2968_);
if (v___x_2969_ == 0)
{
uint32_t v_c_2984_; uint8_t v___y_2986_; uint8_t v___y_2987_; uint8_t v___y_3028_; uint8_t v___y_3029_; uint8_t v___y_3035_; uint8_t v___y_3076_; uint32_t v___x_3086_; uint8_t v___x_3087_; 
v_c_2984_ = lean_string_utf8_get_fast(v_s_2957_, v_p_2961_);
v___x_3086_ = 65;
v___x_3087_ = lean_uint32_dec_le(v___x_3086_, v_c_2984_);
if (v___x_3087_ == 0)
{
goto v___jp_3081_;
}
else
{
uint32_t v___x_3088_; uint8_t v___x_3089_; 
v___x_3088_ = 90;
v___x_3089_ = lean_uint32_dec_le(v_c_2984_, v___x_3088_);
if (v___x_3089_ == 0)
{
goto v___jp_3081_;
}
else
{
goto v___jp_2970_;
}
}
v___jp_2985_:
{
if (v___y_2987_ == 0)
{
uint32_t v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = 44;
v___x_2989_ = lean_uint32_dec_eq(v_c_2984_, v___x_2988_);
if (v___x_2989_ == 0)
{
uint32_t v___x_2990_; uint8_t v___x_2991_; 
v___x_2990_ = 124;
v___x_2991_ = lean_uint32_dec_eq(v_c_2984_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; 
lean_inc_ref(v_s_2957_);
v___x_2992_ = l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_2957_, v_p_2961_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v_a_2994_; lean_object* v___x_2995_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
v_a_2994_ = lean_ctor_get(v___x_2992_, 1);
lean_inc(v_a_2994_);
lean_dec_ref(v___x_2992_);
v___x_2995_ = lean_array_push(v_ands_2960_, v_a_2993_);
v_needsRange_2958_ = v___x_2991_;
v_ands_2960_ = v___x_2995_;
v_p_2961_ = v_a_2994_;
goto _start;
}
else
{
lean_object* v_a_2997_; lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v_a_2997_ = lean_ctor_get(v___x_2992_, 0);
v_a_2998_ = lean_ctor_get(v___x_2992_, 1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2992_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_inc(v_a_2997_);
lean_dec(v___x_2992_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2997_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_p_3006_; uint8_t v___x_3007_; 
v_p_3006_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
v___x_3007_ = lean_nat_dec_eq(v_p_3006_, v___x_2968_);
if (v___x_3007_ == 0)
{
uint32_t v___x_3008_; uint8_t v___x_3009_; 
v___x_3008_ = lean_string_utf8_get_fast(v_s_2957_, v_p_3006_);
v___x_3009_ = lean_uint32_dec_eq(v___x_3008_, v___x_2990_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v___x_3010_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v_p_3006_);
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = lean_array_get_size(v_ands_2960_);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_nat_dec_eq(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_array_push(v_ors_2959_, v_ands_2960_);
v___x_3016_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2));
v___x_3017_ = lean_string_utf8_next_fast(v_s_2957_, v_p_3006_);
v_needsRange_2958_ = v___y_2986_;
v_ors_2959_ = v___x_3015_;
v_ands_2960_ = v___x_3016_;
v_p_2961_ = v___x_3017_;
goto _start;
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v___x_3019_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v_p_3006_);
return v___x_3020_;
}
}
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v___x_3021_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1));
v___x_3022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v_p_3006_);
return v___x_3022_;
}
}
}
else
{
if (v_needsRange_2958_ == 0)
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
v_needsRange_2958_ = v___y_2986_;
v_p_2961_ = v___x_3023_;
goto _start;
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v___x_3025_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v_p_2961_);
return v___x_3026_;
}
}
}
else
{
goto v___jp_2965_;
}
}
v___jp_3027_:
{
if (v___y_3029_ == 0)
{
uint32_t v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = 13;
v___x_3031_ = lean_uint32_dec_eq(v_c_2984_, v___x_3030_);
if (v___x_3031_ == 0)
{
uint32_t v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = 10;
v___x_3033_ = lean_uint32_dec_eq(v_c_2984_, v___x_3032_);
v___y_2986_ = v___y_3028_;
v___y_2987_ = v___x_3033_;
goto v___jp_2985_;
}
else
{
v___y_2986_ = v___y_3028_;
v___y_2987_ = v___x_3031_;
goto v___jp_2985_;
}
}
else
{
goto v___jp_2965_;
}
}
v___jp_3034_:
{
if (v___y_3035_ == 0)
{
uint32_t v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = 42;
v___x_3037_ = lean_uint32_dec_eq(v_c_2984_, v___x_3036_);
if (v___x_3037_ == 0)
{
uint32_t v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = 94;
v___x_3039_ = lean_uint32_dec_eq(v_c_2984_, v___x_3038_);
if (v___x_3039_ == 0)
{
uint32_t v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = 126;
v___x_3041_ = lean_uint32_dec_eq(v_c_2984_, v___x_3040_);
if (v___x_3041_ == 0)
{
uint8_t v___x_3042_; uint32_t v___x_3043_; uint8_t v___x_3044_; 
v___x_3042_ = 1;
v___x_3043_ = 32;
v___x_3044_ = lean_uint32_dec_eq(v_c_2984_, v___x_3043_);
if (v___x_3044_ == 0)
{
uint32_t v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = 9;
v___x_3046_ = lean_uint32_dec_eq(v_c_2984_, v___x_3045_);
v___y_3028_ = v___x_3042_;
v___y_3029_ = v___x_3046_;
goto v___jp_3027_;
}
else
{
v___y_3028_ = v___x_3042_;
v___y_3029_ = v___x_3044_;
goto v___jp_3027_;
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
lean_inc_ref(v_s_2957_);
v___x_3048_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(v_s_2957_, v_ands_2960_, v___x_3047_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v_a_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
v_a_3050_ = lean_ctor_get(v___x_3048_, 1);
lean_inc(v_a_3050_);
lean_dec_ref(v___x_3048_);
v_needsRange_2958_ = v___x_3039_;
v_ands_2960_ = v_a_3049_;
v_p_2961_ = v_a_3050_;
goto _start;
}
else
{
lean_object* v_a_3052_; lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v_a_3052_ = lean_ctor_get(v___x_3048_, 0);
v_a_3053_ = lean_ctor_get(v___x_3048_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3048_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_inc(v_a_3052_);
lean_dec(v___x_3048_);
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
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3052_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_a_3053_);
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
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
lean_inc_ref(v_s_2957_);
v___x_3062_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(v_s_2957_, v_ands_2960_, v___x_3061_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v_a_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
v_a_3064_ = lean_ctor_get(v___x_3062_, 1);
lean_inc(v_a_3064_);
lean_dec_ref(v___x_3062_);
v_needsRange_2958_ = v___x_3037_;
v_ands_2960_ = v_a_3063_;
v_p_2961_ = v_a_3064_;
goto _start;
}
else
{
lean_object* v_a_3066_; lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v_a_3066_ = lean_ctor_get(v___x_3062_, 0);
v_a_3067_ = lean_ctor_get(v___x_3062_, 1);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3062_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_inc(v_a_3066_);
lean_dec(v___x_3062_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3066_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
else
{
goto v___jp_2970_;
}
}
else
{
goto v___jp_2970_;
}
}
v___jp_3075_:
{
if (v___y_3076_ == 0)
{
uint32_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = 48;
v___x_3078_ = lean_uint32_dec_le(v___x_3077_, v_c_2984_);
if (v___x_3078_ == 0)
{
v___y_3035_ = v___x_3078_;
goto v___jp_3034_;
}
else
{
uint32_t v___x_3079_; uint8_t v___x_3080_; 
v___x_3079_ = 57;
v___x_3080_ = lean_uint32_dec_le(v_c_2984_, v___x_3079_);
v___y_3035_ = v___x_3080_;
goto v___jp_3034_;
}
}
else
{
goto v___jp_2970_;
}
}
v___jp_3081_:
{
uint32_t v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = 97;
v___x_3083_ = lean_uint32_dec_le(v___x_3082_, v_c_2984_);
if (v___x_3083_ == 0)
{
v___y_3076_ = v___x_3083_;
goto v___jp_3075_;
}
else
{
uint32_t v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = 122;
v___x_3085_ = lean_uint32_dec_le(v_c_2984_, v___x_3084_);
v___y_3076_ = v___x_3085_;
goto v___jp_3075_;
}
}
}
else
{
lean_dec_ref(v_s_2957_);
if (v_needsRange_2958_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3090_ = lean_array_get_size(v_ands_2960_);
v___x_3091_ = lean_unsigned_to_nat(0u);
v___x_3092_ = lean_nat_dec_eq(v___x_3090_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = lean_array_push(v_ors_2959_, v_ands_2960_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_p_2961_);
return v___x_3094_;
}
else
{
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
goto v___jp_2962_;
}
}
else
{
lean_dec_ref(v_ands_2960_);
lean_dec_ref(v_ors_2959_);
goto v___jp_2962_;
}
}
v___jp_2962_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0));
v___x_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v_p_2961_);
return v___x_2964_;
}
v___jp_2965_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_string_utf8_next_fast(v_s_2957_, v_p_2961_);
lean_dec(v_p_2961_);
v_p_2961_ = v___x_2966_;
goto _start;
}
v___jp_2970_:
{
lean_object* v___x_2971_; 
lean_inc_ref(v_s_2957_);
v___x_2971_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(v_s_2957_, v_ands_2960_, v_p_2961_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v_a_2973_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
v_a_2973_ = lean_ctor_get(v___x_2971_, 1);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2971_);
v_needsRange_2958_ = v___x_2969_;
v_ands_2960_ = v_a_2972_;
v_p_2961_ = v_a_2973_;
goto _start;
}
else
{
lean_object* v_a_2975_; lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec_ref(v_ors_2959_);
lean_dec_ref(v_s_2957_);
v_a_2975_ = lean_ctor_get(v___x_2971_, 0);
v_a_2976_ = lean_ctor_get(v___x_2971_, 1);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2971_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_inc(v_a_2975_);
lean_dec(v___x_2971_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2975_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(lean_object* v_s_3095_, lean_object* v_needsRange_3096_, lean_object* v_ors_3097_, lean_object* v_ands_3098_, lean_object* v_p_3099_){
_start:
{
uint8_t v_needsRange_boxed_3100_; lean_object* v_res_3101_; 
v_needsRange_boxed_3100_ = lean_unbox(v_needsRange_3096_);
v_res_3101_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3095_, v_needsRange_boxed_3100_, v_ors_3097_, v_ands_3098_, v_p_3099_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Version_0__Lake_VerRange_parseM(lean_object* v_s_3104_, lean_object* v_a_3105_){
_start:
{
uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = 1;
v___x_3107_ = ((lean_object*)(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0));
lean_inc_ref(v_s_3104_);
v___x_3108_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(v_s_3104_, v___x_3106_, v___x_3107_, v___x_3107_, v_a_3105_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3118_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_a_3110_ = lean_ctor_get(v___x_3108_, 1);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3112_ = v___x_3108_;
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_s_3104_);
lean_ctor_set(v___x_3114_, 1, v_a_3109_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3114_);
v___x_3116_ = v___x_3112_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_a_3110_);
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
lean_object* v_a_3119_; lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_s_3104_);
v_a_3119_ = lean_ctor_get(v___x_3108_, 0);
v_a_3120_ = lean_ctor_get(v___x_3108_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3108_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_inc(v_a_3119_);
lean_dec(v___x_3108_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3119_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_parse(lean_object* v_s_3129_){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3130_ = ((lean_object*)(l_Lake_VerRange_parse___closed__0));
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = lean_string_utf8_byte_size(v_s_3129_);
v___x_3133_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(v_s_3129_, v___x_3130_, v___x_3131_, v___x_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(lean_object* v_ver_3134_, lean_object* v_as_3135_, size_t v_i_3136_, size_t v_stop_3137_){
_start:
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_usize_dec_eq(v_i_3136_, v_stop_3137_);
if (v___x_3138_ == 0)
{
uint8_t v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3139_ = 1;
v___x_3140_ = lean_array_uget_borrowed(v_as_3135_, v_i_3136_);
v___x_3141_ = l_Lake_VerComparator_test(v___x_3140_, v_ver_3134_);
if (v___x_3141_ == 0)
{
return v___x_3139_;
}
else
{
if (v___x_3138_ == 0)
{
size_t v___x_3142_; size_t v___x_3143_; 
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_add(v_i_3136_, v___x_3142_);
v_i_3136_ = v___x_3143_;
goto _start;
}
else
{
return v___x_3139_;
}
}
}
else
{
uint8_t v___x_3145_; 
v___x_3145_ = 0;
return v___x_3145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(lean_object* v_ver_3146_, lean_object* v_as_3147_, lean_object* v_i_3148_, lean_object* v_stop_3149_){
_start:
{
size_t v_i_boxed_3150_; size_t v_stop_boxed_3151_; uint8_t v_res_3152_; lean_object* v_r_3153_; 
v_i_boxed_3150_ = lean_unbox_usize(v_i_3148_);
lean_dec(v_i_3148_);
v_stop_boxed_3151_ = lean_unbox_usize(v_stop_3149_);
lean_dec(v_stop_3149_);
v_res_3152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3146_, v_as_3147_, v_i_boxed_3150_, v_stop_boxed_3151_);
lean_dec_ref(v_as_3147_);
lean_dec_ref(v_ver_3146_);
v_r_3153_ = lean_box(v_res_3152_);
return v_r_3153_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(lean_object* v_ver_3154_, lean_object* v_as_3155_, size_t v_i_3156_, size_t v_stop_3157_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_usize_dec_eq(v_i_3156_, v_stop_3157_);
if (v___x_3158_ == 0)
{
uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3159_ = 1;
v___x_3160_ = lean_array_uget_borrowed(v_as_3155_, v_i_3156_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = lean_array_get_size(v___x_3160_);
v___x_3163_ = lean_nat_dec_lt(v___x_3161_, v___x_3162_);
if (v___x_3163_ == 0)
{
return v___x_3159_;
}
else
{
if (v___x_3163_ == 0)
{
return v___x_3159_;
}
else
{
size_t v___x_3164_; size_t v___x_3165_; uint8_t v___x_3166_; 
v___x_3164_ = ((size_t)0ULL);
v___x_3165_ = lean_usize_of_nat(v___x_3162_);
v___x_3166_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_3154_, v___x_3160_, v___x_3164_, v___x_3165_);
if (v___x_3166_ == 0)
{
return v___x_3159_;
}
else
{
if (v___x_3158_ == 0)
{
size_t v___x_3167_; size_t v___x_3168_; 
v___x_3167_ = ((size_t)1ULL);
v___x_3168_ = lean_usize_add(v_i_3156_, v___x_3167_);
v_i_3156_ = v___x_3168_;
goto _start;
}
else
{
return v___x_3159_;
}
}
}
}
}
else
{
uint8_t v___x_3170_; 
v___x_3170_ = 0;
return v___x_3170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(lean_object* v_ver_3171_, lean_object* v_as_3172_, lean_object* v_i_3173_, lean_object* v_stop_3174_){
_start:
{
size_t v_i_boxed_3175_; size_t v_stop_boxed_3176_; uint8_t v_res_3177_; lean_object* v_r_3178_; 
v_i_boxed_3175_ = lean_unbox_usize(v_i_3173_);
lean_dec(v_i_3173_);
v_stop_boxed_3176_ = lean_unbox_usize(v_stop_3174_);
lean_dec(v_stop_3174_);
v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3171_, v_as_3172_, v_i_boxed_3175_, v_stop_boxed_3176_);
lean_dec_ref(v_as_3172_);
lean_dec_ref(v_ver_3171_);
v_r_3178_ = lean_box(v_res_3177_);
return v_r_3178_;
}
}
LEAN_EXPORT uint8_t l_Lake_VerRange_test(lean_object* v_self_3179_, lean_object* v_ver_3180_){
_start:
{
lean_object* v_clauses_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v_clauses_3181_ = lean_ctor_get(v_self_3179_, 1);
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_array_get_size(v_clauses_3181_);
v___x_3184_ = lean_nat_dec_lt(v___x_3182_, v___x_3183_);
if (v___x_3184_ == 0)
{
return v___x_3184_;
}
else
{
if (v___x_3184_ == 0)
{
return v___x_3184_;
}
else
{
size_t v___x_3185_; size_t v___x_3186_; uint8_t v___x_3187_; 
v___x_3185_ = ((size_t)0ULL);
v___x_3186_ = lean_usize_of_nat(v___x_3183_);
v___x_3187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_3180_, v_clauses_3181_, v___x_3185_, v___x_3186_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_VerRange_test___boxed(lean_object* v_self_3188_, lean_object* v_ver_3189_){
_start:
{
uint8_t v_res_3190_; lean_object* v_r_3191_; 
v_res_3190_ = l_Lake_VerRange_test(v_self_3188_, v_ver_3189_);
lean_dec_ref(v_ver_3189_);
lean_dec_ref(v_self_3188_);
v_r_3191_ = lean_box(v_res_3190_);
return v_r_3191_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Date(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Trie(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Trie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_SemVerCore_instLT = _init_l_Lake_SemVerCore_instLT();
lean_mark_persistent(l_Lake_SemVerCore_instLT);
l_Lake_SemVerCore_instLE = _init_l_Lake_SemVerCore_instLE();
lean_mark_persistent(l_Lake_SemVerCore_instLE);
l_Lake_StdVer_instLT = _init_l_Lake_StdVer_instLT();
lean_mark_persistent(l_Lake_StdVer_instLT);
l_Lake_StdVer_instLE = _init_l_Lake_StdVer_instLE();
lean_mark_persistent(l_Lake_StdVer_instLE);
l_Lake_ToolchainVer_instLT = _init_l_Lake_ToolchainVer_instLT();
lean_mark_persistent(l_Lake_ToolchainVer_instLT);
l_Lake_ToolchainVer_instLE = _init_l_Lake_ToolchainVer_instLE();
lean_mark_persistent(l_Lake_ToolchainVer_instLE);
l_Lake_instInhabitedComparatorOp_default = _init_l_Lake_instInhabitedComparatorOp_default();
l_Lake_instInhabitedComparatorOp = _init_l_Lake_instInhabitedComparatorOp();
l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie = _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie();
lean_mark_persistent(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Version(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Lake_Util_Date(uint8_t builtin);
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Lean_Data_Trie(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Version(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Trie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Version(builtin);
}
#ifdef __cplusplus
}
#endif
