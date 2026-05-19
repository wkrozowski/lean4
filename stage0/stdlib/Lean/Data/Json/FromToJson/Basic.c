// Lean compiler output
// Module: Lean.Data.Json.FromToJson.Basic
// Imports: public import Lean.Data.Json.Printer public import Init.Data.ToString.Macro import Init.Data.Array.GetLit
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
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSlice(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getArr_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
lean_object* l_Lean_JsonNumber_fromFloat_x3f(double);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_div(double, double);
double lean_float_negate(double);
double l_Lean_JsonNumber_toFloat(lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Json_getNum_x3f(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonJson = (const lean_object*)&l_Lean_instFromJsonJson___closed__0_value;
static const lean_closure_object l_Lean_instToJsonJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_instToJsonJson___closed__0 = (const lean_object*)&l_Lean_instToJsonJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonJson = (const lean_object*)&l_Lean_instToJsonJson___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonJsonNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getNum_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonJsonNumber___closed__0 = (const lean_object*)&l_Lean_instFromJsonJsonNumber___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonJsonNumber = (const lean_object*)&l_Lean_instFromJsonJsonNumber___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonJsonNumber___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonJsonNumber___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonJsonNumber___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonJsonNumber___closed__0 = (const lean_object*)&l_Lean_instToJsonJsonNumber___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonJsonNumber = (const lean_object*)&l_Lean_instToJsonJsonNumber___closed__0_value;
static const lean_string_object l_Lean_instFromJsonUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "expected {} to decode Unit, got "};
static const lean_object* l_Lean_instFromJsonUnit___lam__0___closed__0 = (const lean_object*)&l_Lean_instFromJsonUnit___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instFromJsonUnit___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instFromJsonUnit___lam__0___closed__1 = (const lean_object*)&l_Lean_instFromJsonUnit___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instFromJsonUnit___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUnit___closed__0 = (const lean_object*)&l_Lean_instFromJsonUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUnit = (const lean_object*)&l_Lean_instFromJsonUnit___closed__0_value;
static const lean_ctor_object l_Lean_instToJsonUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instToJsonUnit___lam__0___closed__0 = (const lean_object*)&l_Lean_instToJsonUnit___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonUnit___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUnit___closed__0 = (const lean_object*)&l_Lean_instToJsonUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUnit = (const lean_object*)&l_Lean_instToJsonUnit___closed__0_value;
static const lean_string_object l_Lean_instFromJsonEmpty___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "type Empty has no constructor to match JSON value '"};
static const lean_object* l_Lean_instFromJsonEmpty___lam__0___closed__0 = (const lean_object*)&l_Lean_instFromJsonEmpty___lam__0___closed__0_value;
static const lean_string_object l_Lean_instFromJsonEmpty___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 122, .m_capacity = 122, .m_length = 121, .m_data = "'. This occurs when deserializing a value for type Empty, e.g. at type Option Empty with code for the 'some' constructor."};
static const lean_object* l_Lean_instFromJsonEmpty___lam__0___closed__1 = (const lean_object*)&l_Lean_instFromJsonEmpty___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instFromJsonEmpty___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonEmpty___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonEmpty___closed__0 = (const lean_object*)&l_Lean_instFromJsonEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonEmpty = (const lean_object*)&l_Lean_instFromJsonEmpty___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonEmpty___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonEmpty___closed__0 = (const lean_object*)&l_Lean_instToJsonEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonEmpty = (const lean_object*)&l_Lean_instToJsonEmpty___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getBool_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonBool___closed__0 = (const lean_object*)&l_Lean_instFromJsonBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonBool = (const lean_object*)&l_Lean_instFromJsonBool___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonBool___closed__0 = (const lean_object*)&l_Lean_instToJsonBool___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonBool = (const lean_object*)&l_Lean_instToJsonBool___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getNat_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonNat___closed__0 = (const lean_object*)&l_Lean_instFromJsonNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonNat = (const lean_object*)&l_Lean_instFromJsonNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonNat___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonNat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonNat___closed__0 = (const lean_object*)&l_Lean_instToJsonNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonNat = (const lean_object*)&l_Lean_instToJsonNat___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getInt_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonInt___closed__0 = (const lean_object*)&l_Lean_instFromJsonInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonInt = (const lean_object*)&l_Lean_instFromJsonInt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonInt___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonInt___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonInt___closed__0 = (const lean_object*)&l_Lean_instToJsonInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonInt = (const lean_object*)&l_Lean_instToJsonInt___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonString___closed__0 = (const lean_object*)&l_Lean_instFromJsonString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonString = (const lean_object*)&l_Lean_instFromJsonString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonString___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonString___closed__0 = (const lean_object*)&l_Lean_instToJsonString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonString = (const lean_object*)&l_Lean_instToJsonString___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_toSlice, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonSlice___closed__0 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__0_value;
static const lean_closure_object l_Lean_instFromJsonSlice___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonSlice___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonSlice___closed__1 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__1_value;
static const lean_closure_object l_Lean_instFromJsonSlice___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonSlice___closed__1_value),((lean_object*)&l_Lean_instFromJsonString___closed__0_value)} };
static const lean_object* l_Lean_instFromJsonSlice___closed__2 = (const lean_object*)&l_Lean_instFromJsonSlice___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonSlice = (const lean_object*)&l_Lean_instFromJsonSlice___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonSlice___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonSlice___closed__0 = (const lean_object*)&l_Lean_instToJsonSlice___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonSlice = (const lean_object*)&l_Lean_instToJsonSlice___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object*);
static const lean_closure_object l_Lean_instFromJsonFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonFilePath___closed__0 = (const lean_object*)&l_Lean_instFromJsonFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonFilePath = (const lean_object*)&l_Lean_instFromJsonFilePath___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonFilePath___closed__0 = (const lean_object*)&l_Lean_instToJsonFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonFilePath = (const lean_object*)&l_Lean_instToJsonFilePath___closed__0_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__0_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__1_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__2 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__2_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__3 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__3_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__4 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__4_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__4_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__0_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__5 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__5_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__6 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__6_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__5_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__6_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__1_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__2_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__3_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__7 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__7_value;
static const lean_closure_object l_Array_fromJson_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Array_fromJson_x3f___redArg___closed__8 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__8_value;
static const lean_ctor_object l_Array_fromJson_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_fromJson_x3f___redArg___closed__7_value),((lean_object*)&l_Array_fromJson_x3f___redArg___closed__8_value)}};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__9 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__9_value;
static const lean_string_object l_Array_fromJson_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__10 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__10_value;
static const lean_string_object l_Array_fromJson_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___redArg___closed__11 = (const lean_object*)&l_Array_fromJson_x3f___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Array_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__0 = (const lean_object*)&l_Array_toJson___redArg___closed__0_value;
static const lean_closure_object l_Array_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__1 = (const lean_object*)&l_Array_toJson___redArg___closed__1_value;
static const lean_closure_object l_Array_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__2 = (const lean_object*)&l_Array_toJson___redArg___closed__2_value;
static const lean_closure_object l_Array_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__3 = (const lean_object*)&l_Array_toJson___redArg___closed__3_value;
static const lean_closure_object l_Array_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__4 = (const lean_object*)&l_Array_toJson___redArg___closed__4_value;
static const lean_closure_object l_Array_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__5 = (const lean_object*)&l_Array_toJson___redArg___closed__5_value;
static const lean_closure_object l_Array_toJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_toJson___redArg___closed__6 = (const lean_object*)&l_Array_toJson___redArg___closed__6_value;
static const lean_ctor_object l_Array_toJson___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toJson___redArg___closed__0_value),((lean_object*)&l_Array_toJson___redArg___closed__1_value)}};
static const lean_object* l_Array_toJson___redArg___closed__7 = (const lean_object*)&l_Array_toJson___redArg___closed__7_value;
static const lean_ctor_object l_Array_toJson___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toJson___redArg___closed__7_value),((lean_object*)&l_Array_toJson___redArg___closed__2_value),((lean_object*)&l_Array_toJson___redArg___closed__3_value),((lean_object*)&l_Array_toJson___redArg___closed__4_value),((lean_object*)&l_Array_toJson___redArg___closed__5_value)}};
static const lean_object* l_Array_toJson___redArg___closed__8 = (const lean_object*)&l_Array_toJson___redArg___closed__8_value;
static const lean_ctor_object l_Array_toJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_toJson___redArg___closed__8_value),((lean_object*)&l_Array_toJson___redArg___closed__6_value)}};
static const lean_object* l_Array_toJson___redArg___closed__9 = (const lean_object*)&l_Array_toJson___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonList(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonOption(lean_object*, lean_object*);
static const lean_string_object l_Prod_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected pair, got '"};
static const lean_object* l_Prod_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Prod_fromJson_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_toJson(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Name_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Lean_Name_fromJson_x3f___closed__0 = (const lean_object*)&l_Lean_Name_fromJson_x3f___closed__0_value;
static const lean_string_object l_Lean_Name_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "expected a `Name`, got '"};
static const lean_object* l_Lean_Name_fromJson_x3f___closed__1 = (const lean_object*)&l_Lean_Name_fromJson_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Name_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Name_fromJson_x3f___closed__2 = (const lean_object*)&l_Lean_Name_fromJson_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonName___closed__0 = (const lean_object*)&l_Lean_instFromJsonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonName = (const lean_object*)&l_Lean_instFromJsonName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonName___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToJsonName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonName___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonName___closed__0 = (const lean_object*)&l_Lean_instToJsonName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonName = (const lean_object*)&l_Lean_instToJsonName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "expected a `NameMap`, got '"};
static const lean_object* l_Lean_NameMap_fromJson_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_NameMap_toJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_NameMap_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameMap_toJson___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_NameMap_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_NameMap_toJson___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap(lean_object*, lean_object*);
static const lean_string_object l_Lean_bignumFromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "expected a string-encoded number, got '"};
static const lean_object* l_Lean_bignumFromJson_x3f___closed__0 = (const lean_object*)&l_Lean_bignumFromJson_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_bignumToJson(lean_object*);
static lean_once_cell_t l_USize_fromJson_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_fromJson_x3f___closed__0;
static const lean_string_object l_USize_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "value '"};
static const lean_object* l_USize_fromJson_x3f___closed__1 = (const lean_object*)&l_USize_fromJson_x3f___closed__1_value;
static const lean_string_object l_USize_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is too large for `USize`"};
static const lean_object* l_USize_fromJson_x3f___closed__2 = (const lean_object*)&l_USize_fromJson_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_USize_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUSize___closed__0 = (const lean_object*)&l_Lean_instFromJsonUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUSize = (const lean_object*)&l_Lean_instFromJsonUSize___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUSize___closed__0 = (const lean_object*)&l_Lean_instToJsonUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUSize = (const lean_object*)&l_Lean_instToJsonUSize___closed__0_value;
static lean_once_cell_t l_UInt64_fromJson_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_fromJson_x3f___closed__0;
static const lean_string_object l_UInt64_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "' is too large for `UInt64`"};
static const lean_object* l_UInt64_fromJson_x3f___closed__1 = (const lean_object*)&l_UInt64_fromJson_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_UInt64_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonUInt64___closed__0 = (const lean_object*)&l_Lean_instFromJsonUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonUInt64 = (const lean_object*)&l_Lean_instFromJsonUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonUInt64___closed__0 = (const lean_object*)&l_Lean_instToJsonUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonUInt64 = (const lean_object*)&l_Lean_instToJsonUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_Float_toJson(double);
LEAN_EXPORT lean_object* l_Float_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_instToJsonFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonFloat___closed__0 = (const lean_object*)&l_Lean_instToJsonFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonFloat = (const lean_object*)&l_Lean_instToJsonFloat___closed__0_value;
static const lean_string_object l_Float_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Expected a number or a string 'Infinity', '-Infinity', 'NaN'."};
static const lean_object* l_Float_fromJson_x3f___closed__0 = (const lean_object*)&l_Float_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Float_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Float_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Float_fromJson_x3f___closed__1 = (const lean_object*)&l_Float_fromJson_x3f___closed__1_value;
static const lean_string_object l_Float_fromJson_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Infinity"};
static const lean_object* l_Float_fromJson_x3f___closed__2 = (const lean_object*)&l_Float_fromJson_x3f___closed__2_value;
static const lean_string_object l_Float_fromJson_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-Infinity"};
static const lean_object* l_Float_fromJson_x3f___closed__3 = (const lean_object*)&l_Float_fromJson_x3f___closed__3_value;
static const lean_string_object l_Float_fromJson_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "NaN"};
static const lean_object* l_Float_fromJson_x3f___closed__4 = (const lean_object*)&l_Float_fromJson_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Float_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_instFromJsonFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonFloat___closed__0 = (const lean_object*)&l_Lean_instFromJsonFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonFloat = (const lean_object*)&l_Lean_instFromJsonFloat___closed__0_value;
static const lean_string_object l_Lean_Json_Structured_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expected structured object, got '"};
static const lean_object* l_Lean_Json_Structured_fromJson_x3f___closed__0 = (const lean_object*)&l_Lean_Json_Structured_fromJson_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lean_Json_instFromJsonStructured___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_Structured_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instFromJsonStructured___closed__0 = (const lean_object*)&l_Lean_Json_instFromJsonStructured___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instFromJsonStructured = (const lean_object*)&l_Lean_Json_instFromJsonStructured___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_Structured_toJson(lean_object*);
static const lean_closure_object l_Lean_Json_instToJsonStructured___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_Structured_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Json_instToJsonStructured___closed__0 = (const lean_object*)&l_Lean_Json_instToJsonStructured___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Json_instToJsonStructured = (const lean_object*)&l_Lean_Json_instToJsonStructured___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getTag_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Json_parseTagged___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "incorrect number of fields: "};
static const lean_object* l_Lean_Json_parseTagged___closed__0 = (const lean_object*)&l_Lean_Json_parseTagged___closed__0_value;
static const lean_string_object l_Lean_Json_parseTagged___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≟ "};
static const lean_object* l_Lean_Json_parseTagged___closed__1 = (const lean_object*)&l_Lean_Json_parseTagged___closed__1_value;
static const lean_array_object l_Lean_Json_parseTagged___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Json_parseTagged___closed__2 = (const lean_object*)&l_Lean_Json_parseTagged___closed__2_value;
static const lean_string_object l_Lean_Json_parseTagged___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "incorrect tag: "};
static const lean_object* l_Lean_Json_parseTagged___closed__3 = (const lean_object*)&l_Lean_Json_parseTagged___closed__3_value;
static const lean_ctor_object l_Lean_Json_parseTagged___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Json_parseTagged___closed__2_value)}};
static const lean_object* l_Lean_Json_parseTagged___closed__4 = (const lean_object*)&l_Lean_Json_parseTagged___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonJson___lam__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2_, 0, v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonJsonNumber___lam__0(lean_object* v_n_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_10_, 0, v_n_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonUnit___lam__0(lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 5)
{
lean_object* v_kvPairs_23_; 
v_kvPairs_23_ = lean_ctor_get(v_x_16_, 0);
if (lean_obj_tag(v_kvPairs_23_) == 1)
{
lean_object* v___x_24_; 
lean_dec_ref(v_x_16_);
v___x_24_ = ((lean_object*)(l_Lean_instFromJsonUnit___lam__0___closed__1));
return v___x_24_;
}
else
{
goto v___jp_17_;
}
}
else
{
goto v___jp_17_;
}
v___jp_17_:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_18_ = ((lean_object*)(l_Lean_instFromJsonUnit___lam__0___closed__0));
v___x_19_ = lean_unsigned_to_nat(80u);
v___x_20_ = l_Lean_Json_pretty(v_x_16_, v___x_19_);
v___x_21_ = lean_string_append(v___x_18_, v___x_20_);
lean_dec_ref(v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUnit___lam__0(lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l_Lean_instToJsonUnit___lam__0___closed__0));
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonEmpty___lam__0(lean_object* v_j_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_36_ = ((lean_object*)(l_Lean_instFromJsonEmpty___lam__0___closed__0));
v___x_37_ = lean_unsigned_to_nat(80u);
v___x_38_ = l_Lean_Json_pretty(v_j_35_, v___x_37_);
v___x_39_ = lean_string_append(v___x_36_, v___x_38_);
lean_dec_ref(v___x_38_);
v___x_40_ = ((lean_object*)(l_Lean_instFromJsonEmpty___lam__0___closed__1));
v___x_41_ = lean_string_append(v___x_39_, v___x_40_);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0(uint8_t v_a_45_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonEmpty___lam__0___boxed(lean_object* v_a_46_){
_start:
{
uint8_t v_a_6__boxed_47_; lean_object* v_res_48_; 
v_a_6__boxed_47_ = lean_unbox(v_a_46_);
v_res_48_ = l_Lean_instToJsonEmpty___lam__0(v_a_6__boxed_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0(uint8_t v_b_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_54_, 0, v_b_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object* v_b_55_){
_start:
{
uint8_t v_b_boxed_56_; lean_object* v_res_57_; 
v_b_boxed_56_ = lean_unbox(v_b_55_);
v_res_57_ = l_Lean_instToJsonBool___lam__0(v_b_boxed_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNat___lam__0(lean_object* v_n_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = l_Lean_JsonNumber_fromNat(v_n_62_);
v___x_64_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonInt___lam__0(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = l_Lean_JsonNumber_fromInt(v_n_69_);
v___x_71_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonString___lam__0(lean_object* v_s_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v_s_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0(lean_object* v_s_87_){
_start:
{
lean_object* v_str_88_; lean_object* v_startInclusive_89_; lean_object* v_endExclusive_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_str_88_ = lean_ctor_get(v_s_87_, 0);
v_startInclusive_89_ = lean_ctor_get(v_s_87_, 1);
v_endExclusive_90_ = lean_ctor_get(v_s_87_, 2);
v___x_91_ = lean_string_utf8_extract(v_str_88_, v_startInclusive_89_, v_endExclusive_90_);
v___x_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSlice___lam__0___boxed(lean_object* v_s_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_instToJsonSlice___lam__0(v_s_93_);
lean_dec_ref(v_s_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonFilePath___lam__0(lean_object* v_j_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Json_getStr_x3f(v_j_97_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_98_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_98_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonFilePath___lam__0(lean_object* v_p_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_118_, 0, v_p_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___redArg(lean_object* v_inst_142_, lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(v_x_143_) == 4)
{
lean_object* v_elems_145_; size_t v_sz_146_; size_t v___x_147_; lean_object* v___x_148_; 
v_elems_145_ = lean_ctor_get(v_x_143_, 0);
lean_inc_ref(v_elems_145_);
lean_dec_ref(v_x_143_);
v_sz_146_ = lean_array_size(v_elems_145_);
v___x_147_ = ((size_t)0ULL);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_144_, v_inst_142_, v_sz_146_, v___x_147_, v_elems_145_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec_ref(v_inst_142_);
v___x_149_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__10));
v___x_150_ = lean_unsigned_to_nat(80u);
v___x_151_ = l_Lean_Json_pretty(v_x_143_, v___x_150_);
v___x_152_ = lean_string_append(v___x_149_, v___x_151_);
lean_dec_ref(v___x_151_);
v___x_153_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_154_ = lean_string_append(v___x_152_, v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f(lean_object* v_00_u03b1_156_, lean_object* v_inst_157_, lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Array_fromJson_x3f___redArg(v_inst_157_, v_x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray___redArg(lean_object* v_inst_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_closure((void*)(l_Array_fromJson_x3f), 3, 2);
lean_closure_set(v___x_161_, 0, lean_box(0));
lean_closure_set(v___x_161_, 1, v_inst_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonArray(lean_object* v_00_u03b1_162_, lean_object* v_inst_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_alloc_closure((void*)(l_Array_fromJson_x3f), 3, 2);
lean_closure_set(v___x_164_, 0, lean_box(0));
lean_closure_set(v___x_164_, 1, v_inst_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___redArg___lam__0(lean_object* v_inst_165_, lean_object* v_x_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_apply_1(v_inst_165_, v_x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___redArg(lean_object* v_inst_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___x_190_; size_t v_sz_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___f_189_ = lean_alloc_closure((void*)(l_Array_toJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_189_, 0, v_inst_187_);
v___x_190_ = ((lean_object*)(l_Array_toJson___redArg___closed__9));
v_sz_191_ = lean_array_size(v_a_188_);
v___x_192_ = ((size_t)0ULL);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_190_, v___f_189_, v_sz_191_, v___x_192_, v_a_188_);
v___x_194_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson(lean_object* v_00_u03b1_195_, lean_object* v_inst_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Array_toJson___redArg(v_inst_196_, v_a_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray___redArg(lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_closure((void*)(l_Array_toJson), 3, 2);
lean_closure_set(v___x_200_, 0, lean_box(0));
lean_closure_set(v___x_200_, 1, v_inst_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonArray(lean_object* v_00_u03b1_201_, lean_object* v_inst_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_closure((void*)(l_Array_toJson), 3, 2);
lean_closure_set(v___x_203_, 0, lean_box(0));
lean_closure_set(v___x_203_, 1, v_inst_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_List_fromJson_x3f___redArg(lean_object* v_inst_204_, lean_object* v_j_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Array_fromJson_x3f___redArg(v_inst_204_, v_j_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_a_215_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v___x_206_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_206_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_array_to_list(v_a_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_fromJson_x3f(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_, lean_object* v_j_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_List_fromJson_x3f___redArg(v_inst_225_, v_j_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList___redArg(lean_object* v_inst_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_closure((void*)(l_List_fromJson_x3f), 3, 2);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, v_inst_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonList(lean_object* v_00_u03b1_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_closure((void*)(l_List_fromJson_x3f), 3, 2);
lean_closure_set(v___x_232_, 0, lean_box(0));
lean_closure_set(v___x_232_, 1, v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_List_toJson___redArg(lean_object* v_inst_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_array_mk(v_a_234_);
v___x_236_ = l_Array_toJson___redArg(v_inst_233_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_List_toJson(lean_object* v_00_u03b1_237_, lean_object* v_inst_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_List_toJson___redArg(v_inst_238_, v_a_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList___redArg(lean_object* v_inst_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_closure((void*)(l_List_toJson), 3, 2);
lean_closure_set(v___x_242_, 0, lean_box(0));
lean_closure_set(v___x_242_, 1, v_inst_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonList(lean_object* v_00_u03b1_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_closure((void*)(l_List_toJson), 3, 2);
lean_closure_set(v___x_245_, 0, lean_box(0));
lean_closure_set(v___x_245_, 1, v_inst_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___redArg(lean_object* v_inst_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_inst_248_);
v___x_250_ = ((lean_object*)(l_Option_fromJson_x3f___redArg___closed__0));
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
v___x_251_ = lean_apply_1(v_inst_248_, v_x_249_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_a_260_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_268_ == 0)
{
v___x_262_ = v___x_251_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_251_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_a_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Option_fromJson_x3f___redArg(v_inst_270_, v_x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption___redArg(lean_object* v_inst_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_closure((void*)(l_Option_fromJson_x3f), 3, 2);
lean_closure_set(v___x_274_, 0, lean_box(0));
lean_closure_set(v___x_274_, 1, v_inst_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonOption(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_closure((void*)(l_Option_fromJson_x3f), 3, 2);
lean_closure_set(v___x_277_, 0, lean_box(0));
lean_closure_set(v___x_277_, 1, v_inst_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___redArg(lean_object* v_inst_278_, lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_inst_278_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_282_; 
v_val_281_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_val_281_);
lean_dec_ref(v_x_279_);
v___x_282_ = lean_apply_1(v_inst_278_, v_val_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson(lean_object* v_00_u03b1_283_, lean_object* v_inst_284_, lean_object* v_x_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Option_toJson___redArg(v_inst_284_, v_x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption___redArg(lean_object* v_inst_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_alloc_closure((void*)(l_Option_toJson), 3, 2);
lean_closure_set(v___x_288_, 0, lean_box(0));
lean_closure_set(v___x_288_, 1, v_inst_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonOption(lean_object* v_00_u03b1_289_, lean_object* v_inst_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_closure((void*)(l_Option_toJson), 3, 2);
lean_closure_set(v___x_291_, 0, lean_box(0));
lean_closure_set(v___x_291_, 1, v_inst_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f___redArg(lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_j_297_; 
if (lean_obj_tag(v_x_295_) == 4)
{
lean_object* v_elems_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_elems_305_ = lean_ctor_get(v_x_295_, 0);
v___x_306_ = lean_array_get_size(v_elems_305_);
v___x_307_ = lean_unsigned_to_nat(2u);
v___x_308_ = lean_nat_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec_ref(v_inst_294_);
lean_dec_ref(v_inst_293_);
v_j_297_ = v_x_295_;
goto v___jp_296_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_inc_ref(v_elems_305_);
lean_dec_ref(v_x_295_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_array_fget_borrowed(v_elems_305_, v___x_309_);
lean_inc(v___x_310_);
v___x_311_ = lean_apply_1(v_inst_293_, v___x_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v_elems_305_);
lean_dec_ref(v_inst_294_);
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_a_320_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_320_);
lean_dec_ref(v___x_311_);
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_array_fget(v_elems_305_, v___x_321_);
lean_dec_ref(v_elems_305_);
v___x_323_ = lean_apply_1(v_inst_294_, v___x_322_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_a_320_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_340_; 
v_a_332_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_340_ == 0)
{
v___x_334_ = v___x_323_;
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_323_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_340_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_a_320_);
lean_ctor_set(v___x_336_, 1, v_a_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_inst_294_);
lean_dec_ref(v_inst_293_);
v_j_297_ = v_x_295_;
goto v___jp_296_;
}
v___jp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_298_ = ((lean_object*)(l_Prod_fromJson_x3f___redArg___closed__0));
v___x_299_ = lean_unsigned_to_nat(80u);
v___x_300_ = l_Lean_Json_pretty(v_j_297_, v___x_299_);
v___x_301_ = lean_string_append(v___x_298_, v___x_300_);
lean_dec_ref(v___x_300_);
v___x_302_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_fromJson_x3f(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Prod_fromJson_x3f___redArg(v_inst_343_, v_inst_344_, v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd___redArg(lean_object* v_inst_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_closure((void*)(l_Prod_fromJson_x3f), 5, 4);
lean_closure_set(v___x_349_, 0, lean_box(0));
lean_closure_set(v___x_349_, 1, lean_box(0));
lean_closure_set(v___x_349_, 2, v_inst_347_);
lean_closure_set(v___x_349_, 3, v_inst_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonProd(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_inst_352_, lean_object* v_inst_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_alloc_closure((void*)(l_Prod_fromJson_x3f), 5, 4);
lean_closure_set(v___x_354_, 0, lean_box(0));
lean_closure_set(v___x_354_, 1, lean_box(0));
lean_closure_set(v___x_354_, 2, v_inst_352_);
lean_closure_set(v___x_354_, 3, v_inst_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson___redArg(lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_fst_358_ = lean_ctor_get(v_x_357_, 0);
lean_inc(v_fst_358_);
v_snd_359_ = lean_ctor_get(v_x_357_, 1);
lean_inc(v_snd_359_);
lean_dec_ref(v_x_357_);
v___x_360_ = lean_apply_1(v_inst_355_, v_fst_358_);
v___x_361_ = lean_apply_1(v_inst_356_, v_snd_359_);
v___x_362_ = lean_unsigned_to_nat(2u);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_362_);
v___x_364_ = lean_array_push(v___x_363_, v___x_360_);
v___x_365_ = lean_array_push(v___x_364_, v___x_361_);
v___x_366_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Prod_toJson(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Prod_toJson___redArg(v_inst_369_, v_inst_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd___redArg(lean_object* v_inst_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_closure((void*)(l_Prod_toJson), 5, 4);
lean_closure_set(v___x_375_, 0, lean_box(0));
lean_closure_set(v___x_375_, 1, lean_box(0));
lean_closure_set(v___x_375_, 2, v_inst_373_);
lean_closure_set(v___x_375_, 3, v_inst_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonProd(lean_object* v_00_u03b1_376_, lean_object* v_00_u03b2_377_, lean_object* v_inst_378_, lean_object* v_inst_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_closure((void*)(l_Prod_toJson), 5, 4);
lean_closure_set(v___x_380_, 0, lean_box(0));
lean_closure_set(v___x_380_, 1, lean_box(0));
lean_closure_set(v___x_380_, 2, v_inst_378_);
lean_closure_set(v___x_380_, 3, v_inst_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_fromJson_x3f(lean_object* v_j_385_){
_start:
{
lean_object* v___x_386_; 
lean_inc(v_j_385_);
v___x_386_ = l_Lean_Json_getStr_x3f(v_j_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_j_385_);
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_416_; 
v_a_395_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_416_ == 0)
{
v___x_397_ = v___x_386_;
v_isShared_398_ = v_isSharedCheck_416_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_386_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_416_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
v___x_400_ = lean_string_dec_eq(v_a_395_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = l_String_toName(v_a_395_);
v___x_402_ = l_Lean_Name_isAnonymous(v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_404_; 
lean_dec(v_j_385_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_401_);
v___x_404_ = v___x_397_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_401_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
lean_dec(v___x_401_);
v___x_406_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
v___x_407_ = lean_unsigned_to_nat(80u);
v___x_408_ = l_Lean_Json_pretty(v_j_385_, v___x_407_);
v___x_409_ = lean_string_append(v___x_406_, v___x_408_);
lean_dec_ref(v___x_408_);
v___x_410_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_411_ = lean_string_append(v___x_409_, v___x_410_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 0);
lean_ctor_set(v___x_397_, 0, v___x_411_);
v___x_413_ = v___x_397_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
lean_object* v___x_415_; 
lean_del_object(v___x_397_);
lean_dec(v_a_395_);
lean_dec(v_j_385_);
v___x_415_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__2));
return v___x_415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonName___lam__0(lean_object* v_n_419_){
_start:
{
uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = 1;
v___x_421_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_419_, v___x_420_);
v___x_422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg___lam__0(lean_object* v_inst_425_, lean_object* v_m_426_, lean_object* v_k_427_, lean_object* v_v_428_){
_start:
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__0));
v___x_430_ = lean_string_dec_eq(v_k_427_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v_n_431_; uint8_t v___x_432_; 
lean_inc_ref(v_k_427_);
v_n_431_ = l_String_toName(v_k_427_);
v___x_432_ = l_Lean_Name_isAnonymous(v_n_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v_k_427_);
v___x_433_ = lean_apply_1(v_inst_425_, v_v_428_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec(v_n_431_);
lean_dec(v_m_426_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_a_442_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_431_, v_a_442_, v_m_426_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_n_431_);
lean_dec(v_v_428_);
lean_dec(v_m_426_);
lean_dec_ref(v_inst_425_);
v___x_451_ = ((lean_object*)(l_Lean_Name_fromJson_x3f___closed__1));
v___x_452_ = lean_string_append(v___x_451_, v_k_427_);
lean_dec_ref(v_k_427_);
v___x_453_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_454_ = lean_string_append(v___x_452_, v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec_ref(v_k_427_);
v___x_456_ = lean_apply_1(v_inst_425_, v_v_428_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_m_426_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v_a_465_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_474_ == 0)
{
v___x_467_ = v___x_456_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_456_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_box(0);
v___x_470_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_469_, v_a_465_, v_m_426_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_470_);
v___x_472_ = v___x_467_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f___redArg(lean_object* v_inst_476_, lean_object* v_x_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__9));
if (lean_obj_tag(v_x_477_) == 5)
{
lean_object* v_kvPairs_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_kvPairs_479_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_kvPairs_479_);
lean_dec_ref(v_x_477_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_480_, 0, v_inst_476_);
v___x_481_ = lean_box(1);
v___x_482_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_478_, v___f_480_, v___x_481_, v_kvPairs_479_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref(v_inst_476_);
v___x_483_ = ((lean_object*)(l_Lean_NameMap_fromJson_x3f___redArg___closed__0));
v___x_484_ = lean_unsigned_to_nat(80u);
v___x_485_ = l_Lean_Json_pretty(v_x_477_, v___x_484_);
v___x_486_ = lean_string_append(v___x_483_, v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_fromJson_x3f(lean_object* v_00_u03b1_490_, lean_object* v_inst_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_NameMap_fromJson_x3f___redArg(v_inst_491_, v_x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap___redArg(lean_object* v_inst_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(v___x_495_, 0, lean_box(0));
lean_closure_set(v___x_495_, 1, v_inst_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonNameMap(lean_object* v_00_u03b1_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_closure((void*)(l_Lean_NameMap_fromJson_x3f), 3, 2);
lean_closure_set(v___x_498_, 0, lean_box(0));
lean_closure_set(v___x_498_, 1, v_inst_497_);
return v___x_498_;
}
}
LEAN_EXPORT uint8_t l_Lean_NameMap_toJson___redArg___lam__0(lean_object* v_x_499_, lean_object* v_y_500_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = lean_string_dec_lt(v_x_499_, v_y_500_);
if (v___x_501_ == 0)
{
uint8_t v___x_502_; 
v___x_502_ = lean_string_dec_eq(v_x_499_, v_y_500_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; 
v___x_503_ = 2;
return v___x_503_;
}
else
{
uint8_t v___x_504_; 
v___x_504_ = 1;
return v___x_504_;
}
}
else
{
uint8_t v___x_505_; 
v___x_505_ = 0;
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__0___boxed(lean_object* v_x_506_, lean_object* v_y_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Lean_NameMap_toJson___redArg___lam__0(v_x_506_, v_y_507_);
lean_dec_ref(v_y_507_);
lean_dec_ref(v_x_506_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg___lam__1(lean_object* v_inst_510_, lean_object* v___f_511_, lean_object* v_n_512_, lean_object* v_k_513_, lean_object* v_v_514_){
_start:
{
uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = 1;
v___x_516_ = l_Lean_Name_toString(v_k_513_, v___x_515_);
v___x_517_ = lean_apply_1(v_inst_510_, v_v_514_);
v___x_518_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(v___f_511_, v___x_516_, v___x_517_, v_n_512_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___redArg(lean_object* v_inst_520_, lean_object* v_m_521_){
_start:
{
lean_object* v___f_522_; lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___f_522_ = ((lean_object*)(l_Lean_NameMap_toJson___redArg___closed__0));
v___f_523_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson___redArg___lam__1), 5, 2);
lean_closure_set(v___f_523_, 0, v_inst_520_);
lean_closure_set(v___f_523_, 1, v___f_522_);
v___x_524_ = lean_box(1);
v___x_525_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_523_, v___x_524_, v_m_521_);
v___x_526_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson(lean_object* v_00_u03b1_527_, lean_object* v_inst_528_, lean_object* v_m_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_NameMap_toJson___redArg(v_inst_528_, v_m_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap___redArg(lean_object* v_inst_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(v___x_532_, 0, lean_box(0));
lean_closure_set(v___x_532_, 1, v_inst_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonNameMap(lean_object* v_00_u03b1_533_, lean_object* v_inst_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_closure((void*)(l_Lean_NameMap_toJson), 3, 2);
lean_closure_set(v___x_535_, 0, lean_box(0));
lean_closure_set(v___x_535_, 1, v_inst_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_bignumFromJson_x3f(lean_object* v_j_537_){
_start:
{
lean_object* v___x_538_; 
lean_inc(v_j_537_);
v___x_538_ = l_Lean_Json_getStr_x3f(v_j_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_j_537_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_565_; 
v_a_547_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_565_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_565_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_565_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_a_547_);
lean_dec(v_a_547_);
if (lean_obj_tag(v___x_551_) == 1)
{
lean_object* v_val_552_; lean_object* v___x_554_; 
lean_dec(v_j_537_);
v_val_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref(v___x_551_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v_val_552_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_val_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
lean_dec(v___x_551_);
v___x_556_ = ((lean_object*)(l_Lean_bignumFromJson_x3f___closed__0));
v___x_557_ = lean_unsigned_to_nat(80u);
v___x_558_ = l_Lean_Json_pretty(v_j_537_, v___x_557_);
v___x_559_ = lean_string_append(v___x_556_, v___x_558_);
lean_dec_ref(v___x_558_);
v___x_560_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_561_ = lean_string_append(v___x_559_, v___x_560_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
lean_ctor_set(v___x_549_, 0, v___x_561_);
v___x_563_ = v___x_549_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_bignumToJson(lean_object* v_n_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = l_Nat_reprFast(v_n_566_);
v___x_568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_USize_fromJson_x3f___closed__0(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = l_System_Platform_numBits;
v___x_570_ = lean_unsigned_to_nat(2u);
v___x_571_ = lean_nat_pow(v___x_570_, v___x_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_USize_fromJson_x3f(lean_object* v_j_574_){
_start:
{
lean_object* v___x_575_; 
lean_inc(v_j_574_);
v___x_575_ = l_Lean_bignumFromJson_x3f(v_j_574_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_j_574_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_604_; 
v_a_584_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_604_ == 0)
{
v___x_586_ = v___x_575_;
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_575_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_obj_once(&l_USize_fromJson_x3f___closed__0, &l_USize_fromJson_x3f___closed__0_once, _init_l_USize_fromJson_x3f___closed__0);
v___x_589_ = lean_nat_dec_le(v___x_588_, v_a_584_);
if (v___x_589_ == 0)
{
size_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
lean_dec(v_j_574_);
v___x_590_ = lean_usize_of_nat(v_a_584_);
lean_dec(v_a_584_);
v___x_591_ = lean_box_usize(v___x_590_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_591_);
v___x_593_ = v___x_586_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
lean_dec(v_a_584_);
v___x_595_ = ((lean_object*)(l_USize_fromJson_x3f___closed__1));
v___x_596_ = lean_unsigned_to_nat(80u);
v___x_597_ = l_Lean_Json_pretty(v_j_574_, v___x_596_);
v___x_598_ = lean_string_append(v___x_595_, v___x_597_);
lean_dec_ref(v___x_597_);
v___x_599_ = ((lean_object*)(l_USize_fromJson_x3f___closed__2));
v___x_600_ = lean_string_append(v___x_598_, v___x_599_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 0);
lean_ctor_set(v___x_586_, 0, v___x_600_);
v___x_602_ = v___x_586_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0(size_t v_v_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_usize_to_nat(v_v_607_);
v___x_609_ = l_Lean_bignumToJson(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUSize___lam__0___boxed(lean_object* v_v_610_){
_start:
{
size_t v_v_boxed_611_; lean_object* v_res_612_; 
v_v_boxed_611_ = lean_unbox_usize(v_v_610_);
lean_dec(v_v_610_);
v_res_612_ = l_Lean_instToJsonUSize___lam__0(v_v_boxed_611_);
return v_res_612_;
}
}
static lean_object* _init_l_UInt64_fromJson_x3f___closed__0(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_cstr_to_nat("18446744073709551616");
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_UInt64_fromJson_x3f(lean_object* v_j_617_){
_start:
{
lean_object* v___x_618_; 
lean_inc(v_j_617_);
v___x_618_ = l_Lean_bignumFromJson_x3f(v_j_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_j_617_);
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_647_; 
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_647_ == 0)
{
v___x_629_ = v___x_618_;
v_isShared_630_ = v_isSharedCheck_647_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_647_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_obj_once(&l_UInt64_fromJson_x3f___closed__0, &l_UInt64_fromJson_x3f___closed__0_once, _init_l_UInt64_fromJson_x3f___closed__0);
v___x_632_ = lean_nat_dec_le(v___x_631_, v_a_627_);
if (v___x_632_ == 0)
{
uint64_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_j_617_);
v___x_633_ = lean_uint64_of_nat(v_a_627_);
lean_dec(v_a_627_);
v___x_634_ = lean_box_uint64(v___x_633_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_634_);
v___x_636_ = v___x_629_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
lean_dec(v_a_627_);
v___x_638_ = ((lean_object*)(l_USize_fromJson_x3f___closed__1));
v___x_639_ = lean_unsigned_to_nat(80u);
v___x_640_ = l_Lean_Json_pretty(v_j_617_, v___x_639_);
v___x_641_ = lean_string_append(v___x_638_, v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = ((lean_object*)(l_UInt64_fromJson_x3f___closed__1));
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 0);
lean_ctor_set(v___x_629_, 0, v___x_643_);
v___x_645_ = v___x_629_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0(uint64_t v_v_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_uint64_to_nat(v_v_650_);
v___x_652_ = l_Lean_bignumToJson(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonUInt64___lam__0___boxed(lean_object* v_v_653_){
_start:
{
uint64_t v_v_boxed_654_; lean_object* v_res_655_; 
v_v_boxed_654_ = lean_unbox_uint64(v_v_653_);
lean_dec_ref(v_v_653_);
v_res_655_ = l_Lean_instToJsonUInt64___lam__0(v_v_boxed_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Float_toJson(double v_x_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_val_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_val_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_val_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 3);
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_val_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
else
{
lean_object* v_val_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_val_668_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_659_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_val_668_);
lean_dec(v___x_659_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 2);
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_val_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Float_toJson___boxed(lean_object* v_x_676_){
_start:
{
double v_x_boxed_677_; lean_object* v_res_678_; 
v_x_boxed_677_ = lean_unbox_float(v_x_676_);
lean_dec_ref(v_x_676_);
v_res_678_ = l_Float_toJson(v_x_boxed_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Float_fromJson_x3f(lean_object* v_x_687_){
_start:
{
switch(lean_obj_tag(v_x_687_))
{
case 3:
{
lean_object* v_s_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_729_; 
v_s_690_ = lean_ctor_get(v_x_687_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_x_687_);
if (v_isSharedCheck_729_ == 0)
{
v___x_692_ = v_x_687_;
v_isShared_693_ = v_isSharedCheck_729_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_s_690_);
lean_dec(v_x_687_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_729_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = ((lean_object*)(l_Float_fromJson_x3f___closed__2));
v___x_695_ = lean_string_dec_eq(v_s_690_, v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = ((lean_object*)(l_Float_fromJson_x3f___closed__3));
v___x_697_ = lean_string_dec_eq(v_s_690_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = ((lean_object*)(l_Float_fromJson_x3f___closed__4));
v___x_699_ = lean_string_dec_eq(v_s_690_, v___x_698_);
lean_dec_ref(v_s_690_);
if (v___x_699_ == 0)
{
lean_del_object(v___x_692_);
goto v___jp_688_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; double v___x_702_; double v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = l_Float_ofScientific(v___x_700_, v___x_699_, v___x_701_);
v___x_703_ = lean_float_div(v___x_702_, v___x_702_);
v___x_704_ = lean_box_float(v___x_703_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 0, v___x_704_);
v___x_706_ = v___x_692_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; double v___x_710_; double v___x_711_; lean_object* v___x_712_; double v___x_713_; double v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec_ref(v_s_690_);
v___x_708_ = lean_unsigned_to_nat(10u);
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = l_Float_ofScientific(v___x_708_, v___x_697_, v___x_709_);
v___x_711_ = lean_float_negate(v___x_710_);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = l_Float_ofScientific(v___x_712_, v___x_697_, v___x_709_);
v___x_714_ = lean_float_div(v___x_711_, v___x_713_);
v___x_715_ = lean_box_float(v___x_714_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 0, v___x_715_);
v___x_717_ = v___x_692_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; double v___x_721_; lean_object* v___x_722_; double v___x_723_; double v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
lean_dec_ref(v_s_690_);
v___x_719_ = lean_unsigned_to_nat(10u);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = l_Float_ofScientific(v___x_719_, v___x_695_, v___x_720_);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = l_Float_ofScientific(v___x_722_, v___x_695_, v___x_720_);
v___x_724_ = lean_float_div(v___x_721_, v___x_723_);
v___x_725_ = lean_box_float(v___x_724_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 1);
lean_ctor_set(v___x_692_, 0, v___x_725_);
v___x_727_ = v___x_692_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
case 2:
{
lean_object* v_n_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_739_; 
v_n_730_ = lean_ctor_get(v_x_687_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_x_687_);
if (v_isSharedCheck_739_ == 0)
{
v___x_732_ = v_x_687_;
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_n_730_);
lean_dec(v_x_687_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_739_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
double v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_734_ = l_Lean_JsonNumber_toFloat(v_n_730_);
v___x_735_ = lean_box_float(v___x_734_);
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 1);
lean_ctor_set(v___x_732_, 0, v___x_735_);
v___x_737_ = v___x_732_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
default: 
{
lean_dec(v_x_687_);
goto v___jp_688_;
}
}
v___jp_688_:
{
lean_object* v___x_689_; 
v___x_689_ = ((lean_object*)(l_Float_fromJson_x3f___closed__1));
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object* v_x_743_){
_start:
{
switch(lean_obj_tag(v_x_743_))
{
case 4:
{
lean_object* v_elems_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_elems_744_ = lean_ctor_get(v_x_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v_x_743_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_elems_744_);
lean_dec(v_x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 0);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_elems_744_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
case 5:
{
lean_object* v_kvPairs_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_kvPairs_753_ = lean_ctor_get(v_x_743_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_761_ == 0)
{
v___x_755_ = v_x_743_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_kvPairs_753_);
lean_dec(v_x_743_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 1);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_kvPairs_753_);
v___x_758_ = v_reuseFailAlloc_760_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; 
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
default: 
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_762_ = ((lean_object*)(l_Lean_Json_Structured_fromJson_x3f___closed__0));
v___x_763_ = lean_unsigned_to_nat(80u);
v___x_764_ = l_Lean_Json_pretty(v_x_743_, v___x_763_);
v___x_765_ = lean_string_append(v___x_762_, v___x_764_);
lean_dec_ref(v___x_764_);
v___x_766_ = ((lean_object*)(l_Array_fromJson_x3f___redArg___closed__11));
v___x_767_ = lean_string_append(v___x_765_, v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Structured_toJson(lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 0)
{
lean_object* v_elems_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
v_elems_772_ = lean_ctor_get(v_x_771_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v_x_771_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_elems_772_);
lean_dec(v_x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 4);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_elems_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v_kvPairs_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
v_kvPairs_780_ = lean_ctor_get(v_x_771_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_771_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v_x_771_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_kvPairs_780_);
lean_dec(v_x_771_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set_tag(v___x_782_, 5);
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_kvPairs_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object* v_inst_790_, lean_object* v_v_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_apply_1(v_inst_790_, v_v_791_);
v___x_793_ = l_Lean_Json_Structured_fromJson_x3f(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f(lean_object* v_00_u03b1_794_, lean_object* v_inst_795_, lean_object* v_v_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_795_, v_v_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object* v_j_798_, lean_object* v_inst_799_, lean_object* v_k_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l_Lean_Json_getObjValD(v_j_798_, v_k_800_);
v___x_802_ = lean_apply_1(v_inst_799_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___redArg___boxed(lean_object* v_j_803_, lean_object* v_inst_804_, lean_object* v_k_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_803_, v_inst_804_, v_k_805_);
lean_dec_ref(v_k_805_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f(lean_object* v_j_807_, lean_object* v_00_u03b1_808_, lean_object* v_inst_809_, lean_object* v_k_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_807_, v_inst_809_, v_k_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___boxed(lean_object* v_j_812_, lean_object* v_00_u03b1_813_, lean_object* v_inst_814_, lean_object* v_k_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Json_getObjValAs_x3f(v_j_812_, v_00_u03b1_813_, v_inst_814_, v_k_815_);
lean_dec_ref(v_k_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21___redArg(lean_object* v_j_817_, lean_object* v_inst_818_, lean_object* v_k_819_, lean_object* v_v_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_apply_1(v_inst_818_, v_v_820_);
v___x_822_ = l_Lean_Json_setObjVal_x21(v_j_817_, v_k_819_, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_setObjValAs_x21(lean_object* v_j_823_, lean_object* v_00_u03b1_824_, lean_object* v_inst_825_, lean_object* v_k_826_, lean_object* v_v_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Json_setObjValAs_x21___redArg(v_j_823_, v_inst_825_, v_k_826_, v_v_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___redArg(lean_object* v_inst_829_, lean_object* v_k_830_, lean_object* v_x_831_){
_start:
{
if (lean_obj_tag(v_x_831_) == 0)
{
lean_object* v___x_832_; 
lean_dec_ref(v_k_830_);
lean_dec_ref(v_inst_829_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v_val_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_val_833_ = lean_ctor_get(v_x_831_, 0);
lean_inc(v_val_833_);
lean_dec_ref(v_x_831_);
v___x_834_ = lean_apply_1(v_inst_829_, v_val_833_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v_k_830_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt(lean_object* v_00_u03b1_838_, lean_object* v_inst_839_, lean_object* v_k_840_, lean_object* v_x_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Json_opt___redArg(v_inst_839_, v_k_840_, v_x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getTag_x3f(lean_object* v_x_843_){
_start:
{
switch(lean_obj_tag(v_x_843_))
{
case 3:
{
lean_object* v_s_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_s_844_ = lean_ctor_get(v_x_843_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_x_843_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v_x_843_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_s_844_);
lean_dec(v_x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 1);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_s_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
case 5:
{
lean_object* v_kvPairs_852_; lean_object* v___y_854_; 
v_kvPairs_852_ = lean_ctor_get(v_x_843_, 0);
lean_inc(v_kvPairs_852_);
lean_dec_ref(v_x_843_);
if (lean_obj_tag(v_kvPairs_852_) == 0)
{
lean_object* v_size_859_; 
v_size_859_ = lean_ctor_get(v_kvPairs_852_, 0);
lean_inc(v_size_859_);
v___y_854_ = v_size_859_;
goto v___jp_853_;
}
else
{
lean_object* v___x_860_; 
v___x_860_ = lean_unsigned_to_nat(0u);
v___y_854_ = v___x_860_;
goto v___jp_853_;
}
v___jp_853_:
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = lean_nat_dec_eq(v___y_854_, v___x_855_);
lean_dec(v___y_854_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec(v_kvPairs_852_);
v___x_857_ = lean_box(0);
return v___x_857_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_kvPairs_852_);
lean_dec(v_kvPairs_852_);
return v___x_858_;
}
}
}
default: 
{
lean_object* v___x_861_; 
lean_dec(v_x_843_);
v___x_861_ = lean_box(0);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(lean_object* v_a_862_, lean_object* v_as_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_b_866_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_lt(v_i_865_, v_sz_864_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_a_862_);
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v_b_866_);
return v___x_868_;
}
else
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_a_869_ = lean_array_uget_borrowed(v_as_863_, v_i_865_);
v___x_870_ = l_Lean_Name_getString_x21(v_a_869_);
lean_inc(v_a_862_);
v___x_871_ = l_Lean_Json_getObjVal_x3f(v_a_862_, v___x_870_);
lean_dec_ref(v___x_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_b_866_);
lean_dec(v_a_862_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_881_; size_t v___x_882_; size_t v___x_883_; 
v_a_880_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_880_);
lean_dec_ref(v___x_871_);
v___x_881_ = lean_array_push(v_b_866_, v_a_880_);
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_add(v_i_865_, v___x_882_);
v_i_865_ = v___x_883_;
v_b_866_ = v___x_881_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(lean_object* v_a_885_, lean_object* v_as_886_, lean_object* v_sz_887_, lean_object* v_i_888_, lean_object* v_b_889_){
_start:
{
size_t v_sz_boxed_890_; size_t v_i_boxed_891_; lean_object* v_res_892_; 
v_sz_boxed_890_ = lean_unbox_usize(v_sz_887_);
lean_dec(v_sz_887_);
v_i_boxed_891_ = lean_unbox_usize(v_i_888_);
lean_dec(v_i_888_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_885_, v_as_886_, v_sz_boxed_890_, v_i_boxed_891_, v_b_889_);
lean_dec_ref(v_as_886_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged(lean_object* v_json_900_, lean_object* v_tag_901_, lean_object* v_nFields_902_, lean_object* v_fieldNames_x3f_903_){
_start:
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_nat_dec_eq(v_nFields_902_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Json_getObjVal_x3f(v_json_900_, v_tag_901_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_nFields_902_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
if (lean_obj_tag(v_fieldNames_x3f_903_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_945_; 
v_a_915_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_945_ == 0)
{
v___x_917_ = v___x_906_;
v_isShared_918_ = v_isSharedCheck_945_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_906_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_945_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_dec_eq(v_nFields_902_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
lean_del_object(v___x_917_);
v___x_921_ = l_Lean_Json_getArr_x3f(v_a_915_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec(v_nFields_902_);
return v___x_921_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
v___x_923_ = lean_array_get_size(v_a_922_);
lean_dec(v_a_922_);
v___x_924_ = lean_nat_dec_eq(v___x_923_, v_nFields_902_);
if (v___x_924_ == 0)
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_938_; 
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_921_, 0);
lean_dec(v_unused_939_);
v___x_926_ = v___x_921_;
v_isShared_927_ = v_isSharedCheck_938_;
goto v_resetjp_925_;
}
else
{
lean_dec(v___x_921_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_938_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_928_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
v___x_929_ = l_Nat_reprFast(v___x_923_);
v___x_930_ = lean_string_append(v___x_928_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = l_Nat_reprFast(v_nFields_902_);
v___x_934_ = lean_string_append(v___x_932_, v___x_933_);
lean_dec_ref(v___x_933_);
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 0);
lean_ctor_set(v___x_926_, 0, v___x_934_);
v___x_936_ = v___x_926_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_dec(v_nFields_902_);
return v___x_921_;
}
}
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec(v_nFields_902_);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_919_);
v___x_941_ = lean_array_push(v___x_940_, v_a_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_941_);
v___x_943_ = v___x_917_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v_val_947_; lean_object* v_fields_948_; size_t v_sz_949_; size_t v___x_950_; lean_object* v___x_951_; 
lean_dec(v_nFields_902_);
v_a_946_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_946_);
lean_dec_ref(v___x_906_);
v_val_947_ = lean_ctor_get(v_fieldNames_x3f_903_, 0);
v_fields_948_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__2));
v_sz_949_ = lean_array_size(v_val_947_);
v___x_950_ = ((size_t)0ULL);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_946_, v_val_947_, v_sz_949_, v___x_950_, v_fields_948_);
return v___x_951_;
}
}
}
else
{
lean_object* v___x_952_; 
lean_dec(v_nFields_902_);
v___x_952_ = l_Lean_Json_getStr_x3f(v_json_900_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_975_; 
v_a_961_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_975_ == 0)
{
v___x_963_ = v___x_952_;
v_isShared_964_ = v_isSharedCheck_975_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_952_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_975_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v___x_965_; 
v___x_965_ = lean_string_dec_eq(v_a_961_, v_tag_901_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_966_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__3));
v___x_967_ = lean_string_append(v___x_966_, v_a_961_);
lean_dec(v_a_961_);
v___x_968_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
v___x_970_ = lean_string_append(v___x_969_, v_tag_901_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 0);
lean_ctor_set(v___x_963_, 0, v___x_970_);
v___x_972_ = v___x_963_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
else
{
lean_object* v___x_974_; 
lean_del_object(v___x_963_);
lean_dec(v_a_961_);
v___x_974_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__4));
return v___x_974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseTagged___boxed(lean_object* v_json_976_, lean_object* v_tag_977_, lean_object* v_nFields_978_, lean_object* v_fieldNames_x3f_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Json_parseTagged(v_json_976_, v_tag_977_, v_nFields_978_, v_fieldNames_x3f_979_);
lean_dec(v_fieldNames_x3f_979_);
lean_dec_ref(v_tag_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(lean_object* v_a_981_, size_t v_sz_982_, size_t v_i_983_, lean_object* v_bs_984_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = lean_usize_dec_lt(v_i_983_, v_sz_982_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec(v_a_981_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_bs_984_);
return v___x_986_;
}
else
{
lean_object* v_v_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_v_987_ = lean_array_uget_borrowed(v_bs_984_, v_i_983_);
v___x_988_ = l_Lean_Name_getString_x21(v_v_987_);
lean_inc(v_a_981_);
v___x_989_ = l_Lean_Json_getObjVal_x3f(v_a_981_, v___x_988_);
lean_dec_ref(v___x_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_bs_984_);
lean_dec(v_a_981_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v_bs_x27_1000_; size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
v_a_998_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_989_);
v___x_999_ = lean_unsigned_to_nat(0u);
v_bs_x27_1000_ = lean_array_uset(v_bs_984_, v_i_983_, v___x_999_);
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_add(v_i_983_, v___x_1001_);
v___x_1003_ = lean_array_uset(v_bs_x27_1000_, v_i_983_, v_a_998_);
v_i_983_ = v___x_1002_;
v_bs_984_ = v___x_1003_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(lean_object* v_a_1005_, lean_object* v_sz_1006_, lean_object* v_i_1007_, lean_object* v_bs_1008_){
_start:
{
size_t v_sz_boxed_1009_; size_t v_i_boxed_1010_; lean_object* v_res_1011_; 
v_sz_boxed_1009_ = lean_unbox_usize(v_sz_1006_);
lean_dec(v_sz_1006_);
v_i_boxed_1010_ = lean_unbox_usize(v_i_1007_);
lean_dec(v_i_1007_);
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_1005_, v_sz_boxed_1009_, v_i_boxed_1010_, v_bs_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields(lean_object* v_json_1012_, lean_object* v_tag_1013_, lean_object* v_nFields_1014_, lean_object* v_fieldNames_x3f_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Json_getObjVal_x3f(v_json_1012_, v_tag_1013_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v_fieldNames_x3f_1015_);
lean_dec(v_nFields_1014_);
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
else
{
if (lean_obj_tag(v_fieldNames_x3f_1015_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1055_; 
v_a_1025_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1027_ = v___x_1016_;
v_isShared_1028_ = v_isSharedCheck_1055_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1016_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1055_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_dec_eq(v_nFields_1014_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; 
lean_del_object(v___x_1027_);
v___x_1031_ = l_Lean_Json_getArr_x3f(v_a_1025_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_dec(v_nFields_1014_);
return v___x_1031_;
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
v___x_1033_ = lean_array_get_size(v_a_1032_);
lean_dec(v_a_1032_);
v___x_1034_ = lean_nat_dec_eq(v___x_1033_, v_nFields_1014_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1048_; 
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___x_1031_, 0);
lean_dec(v_unused_1049_);
v___x_1036_ = v___x_1031_;
v_isShared_1037_ = v_isSharedCheck_1048_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v___x_1031_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1048_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1038_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__0));
v___x_1039_ = l_Nat_reprFast(v___x_1033_);
v___x_1040_ = lean_string_append(v___x_1038_, v___x_1039_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = ((lean_object*)(l_Lean_Json_parseTagged___closed__1));
v___x_1042_ = lean_string_append(v___x_1040_, v___x_1041_);
v___x_1043_ = l_Nat_reprFast(v_nFields_1014_);
v___x_1044_ = lean_string_append(v___x_1042_, v___x_1043_);
lean_dec_ref(v___x_1043_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1044_);
v___x_1046_ = v___x_1036_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
lean_dec(v_nFields_1014_);
return v___x_1031_;
}
}
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_dec(v_nFields_1014_);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_1029_);
v___x_1051_ = lean_array_push(v___x_1050_, v_a_1025_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1051_);
v___x_1053_ = v___x_1027_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v_val_1057_; size_t v_sz_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_nFields_1014_);
v_a_1056_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1016_);
v_val_1057_ = lean_ctor_get(v_fieldNames_x3f_1015_, 0);
lean_inc(v_val_1057_);
lean_dec_ref(v_fieldNames_x3f_1015_);
v_sz_1058_ = lean_array_size(v_val_1057_);
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_1056_, v_sz_1058_, v___x_1059_, v_val_1057_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parseCtorFields___boxed(lean_object* v_json_1061_, lean_object* v_tag_1062_, lean_object* v_nFields_1063_, lean_object* v_fieldNames_x3f_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Json_parseCtorFields(v_json_1061_, v_tag_1062_, v_nFields_1063_, v_fieldNames_x3f_1064_);
lean_dec_ref(v_tag_1062_);
return v_res_1065_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Printer(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Json_FromToJson_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
