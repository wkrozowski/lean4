// Lean compiler output
// Module: Lean.Structure
// Imports: public import Lean.ProjFns public import Lean.Exception public import Init.While import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseReps___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Array_erase___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_instReprBinderInfo_repr(uint8_t, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedConstructorVal_default;
static const lean_ctor_object l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedStructureFieldInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureFieldInfo_default = (const lean_object*)&l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureFieldInfo = (const lean_object*)&l_Lean_instInhabitedStructureFieldInfo_default___closed__0_value;
static const lean_string_object l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprStructureFieldInfo_repr_spec__2(lean_object*);
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fieldName"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "projFn"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "subobject\?"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binderInfo"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "autoParam\?"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19_value;
static const lean_string_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21;
static lean_once_cell_t l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__20_value)}};
static const lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24 = (const lean_object*)&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24_value;
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprStructureFieldInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprStructureFieldInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprStructureFieldInfo___closed__0 = (const lean_object*)&l_Lean_instReprStructureFieldInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprStructureFieldInfo = (const lean_object*)&l_Lean_instReprStructureFieldInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_StructureFieldInfo_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureFieldInfo_lt___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedStructureParentInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedStructureParentInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureParentInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureParentInfo_default = (const lean_object*)&l_Lean_instInhabitedStructureParentInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureParentInfo = (const lean_object*)&l_Lean_instInhabitedStructureParentInfo_default___closed__0_value;
static const lean_array_object l_Lean_instInhabitedStructureInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureInfo_default___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedStructureInfo_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureInfo_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureInfo_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureInfo;
LEAN_EXPORT uint8_t l_Lean_StructureInfo_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_instInhabitedStructureState;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_StructureInfo_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Structure"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 99, 41, 156, 128, 75, 220, 191)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__6_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(95, 65, 245, 208, 160, 42, 187, 12)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__9_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 218, 80, 170, 109, 89, 69, 212)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "structureExt"};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__10_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__11_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 77, 126, 118, 66, 118, 83, 124)}};
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_structureExt;
static const lean_array_object l_Lean_instInhabitedStructureDescr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureDescr_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedStructureDescr_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedStructureDescr_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureDescr_default = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureDescr = (const lean_object*)&l_Lean_instInhabitedStructureDescr_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_StructureFieldInfo_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_registerStructure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_registerStructure___closed__0 = (const lean_object*)&l_Lean_registerStructure___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_setStructureParents___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "cannot set structure parents for `"};
static const lean_object* l_Lean_setStructureParents___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_setStructureParents___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_setStructureParents___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setStructureParents___redArg___lam__1___closed__1;
static const lean_string_object l_Lean_setStructureParents___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "`, structure not defined in current module"};
static const lean_object* l_Lean_setStructureParents___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_setStructureParents___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_setStructureParents___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setStructureParents___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_setStructureParents___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_setStructureParents___redArg___closed__0 = (const lean_object*)&l_Lean_setStructureParents___redArg___closed__0_value;
static const lean_closure_object l_Lean_setStructureParents___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_setStructureParents___redArg___closed__1 = (const lean_object*)&l_Lean_setStructureParents___redArg___closed__1_value;
static lean_once_cell_t l_Lean_setStructureParents___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setStructureParents___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_getStructureInfo_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getStructureInfo_x3f___closed__0 = (const lean_object*)&l_Lean_getStructureInfo_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object*);
static const lean_string_object l_Lean_getStructureInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.Structure"};
static const lean_object* l_Lean_getStructureInfo___closed__0 = (const lean_object*)&l_Lean_getStructureInfo___closed__0_value;
static const lean_string_object l_Lean_getStructureInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.getStructureInfo"};
static const lean_object* l_Lean_getStructureInfo___closed__1 = (const lean_object*)&l_Lean_getStructureInfo___closed__1_value;
static const lean_string_object l_Lean_getStructureInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structure expected"};
static const lean_object* l_Lean_getStructureInfo___closed__2 = (const lean_object*)&l_Lean_getStructureInfo___closed__2_value;
static lean_once_cell_t l_Lean_getStructureInfo___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getStructureInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object*);
static const lean_string_object l_Lean_getStructureCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.getStructureCtor"};
static const lean_object* l_Lean_getStructureCtor___closed__0 = (const lean_object*)&l_Lean_getStructureCtor___closed__0_value;
static lean_once_cell_t l_Lean_getStructureCtor___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getStructureCtor___closed__1;
static const lean_string_object l_Lean_getStructureCtor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed environment"};
static const lean_object* l_Lean_getStructureCtor___closed__2 = (const lean_object*)&l_Lean_getStructureCtor___closed__2_value;
static lean_once_cell_t l_Lean_getStructureCtor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getStructureCtor___closed__3;
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkFlatCtorOfStructCtorName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_flat_ctor"};
static const lean_object* l_Lean_mkFlatCtorOfStructCtorName___closed__0 = (const lean_object*)&l_Lean_mkFlatCtorOfStructCtorName___closed__0_value;
static const lean_ctor_object l_Lean_mkFlatCtorOfStructCtorName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkFlatCtorOfStructCtorName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 244, 96, 108, 193, 103, 182, 1)}};
static const lean_object* l_Lean_mkFlatCtorOfStructCtorName___closed__1 = (const lean_object*)&l_Lean_mkFlatCtorOfStructCtorName___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkDefaultFnOfProjFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_default"};
static const lean_object* l_Lean_mkDefaultFnOfProjFn___closed__0 = (const lean_object*)&l_Lean_mkDefaultFnOfProjFn___closed__0_value;
static const lean_ctor_object l_Lean_mkDefaultFnOfProjFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkDefaultFnOfProjFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(150, 118, 55, 225, 252, 34, 96, 112)}};
static const lean_object* l_Lean_mkDefaultFnOfProjFn___closed__1 = (const lean_object*)&l_Lean_mkDefaultFnOfProjFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object*);
static const lean_string_object l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "_inherited_default"};
static const lean_object* l_Lean_mkInheritedDefaultFnOfProjFn___closed__0 = (const lean_object*)&l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value;
static const lean_ctor_object l_Lean_mkInheritedDefaultFnOfProjFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkInheritedDefaultFnOfProjFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 137, 199, 23, 68, 254, 123, 5)}};
static const lean_object* l_Lean_mkInheritedDefaultFnOfProjFn___closed__1 = (const lean_object*)&l_Lean_mkInheritedDefaultFnOfProjFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_getDefaultFnForField_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkDefaultFnOfProjFn, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getDefaultFnForField_x3f___closed__0 = (const lean_object*)&l_Lean_getDefaultFnForField_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_getEffectiveDefaultFnForField_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkInheritedDefaultFnOfProjFn, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getEffectiveDefaultFnForField_x3f___closed__0 = (const lean_object*)&l_Lean_getEffectiveDefaultFnForField_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAutoParamFnOfProjFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_autoParam"};
static const lean_object* l_Lean_mkAutoParamFnOfProjFn___closed__0 = (const lean_object*)&l_Lean_mkAutoParamFnOfProjFn___closed__0_value;
static const lean_ctor_object l_Lean_mkAutoParamFnOfProjFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkAutoParamFnOfProjFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 175, 123, 123, 31, 136, 163, 222)}};
static const lean_object* l_Lean_mkAutoParamFnOfProjFn___closed__1 = (const lean_object*)&l_Lean_mkAutoParamFnOfProjFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object*);
static const lean_closure_object l_Lean_getAutoParamFnForField_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkAutoParamFnOfProjFn, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getAutoParamFnForField_x3f___closed__0 = (const lean_object*)&l_Lean_getAutoParamFnForField_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object*);
static const lean_string_object l_Lean_getNonRecStructureCtor_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.getNonRecStructureCtor\?"};
static const lean_object* l_Lean_getNonRecStructureCtor_x3f___closed__0 = (const lean_object*)&l_Lean_getNonRecStructureCtor_x3f___closed__0_value;
static lean_once_cell_t l_Lean_getNonRecStructureCtor_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getNonRecStructureCtor_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedStructureResolutionState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureResolutionState_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedStructureResolutionState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureResolutionState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionState;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_structureResolutionExt;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureResolutionOrderConflict_default = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedStructureResolutionOrderConflict = (const lean_object*)&l_Lean_instInhabitedStructureResolutionOrderConflict_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionOrderResult_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedStructureResolutionOrderResult;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value;
static const lean_closure_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__0_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__1_value)}};
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__7_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__2_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__3_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__4_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__5_value)}};
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__8_value),((lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__6_value)}};
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9_value;
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0;
static const lean_ctor_object l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1 = (const lean_object*)&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0_value;
static const lean_array_object l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1_value;
static const lean_array_object l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__2 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object*, lean_object*);
static const lean_closure_object l_Lean_computeStructureResolutionOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_computeStructureResolutionOrder___redArg___closed__0 = (const lean_object*)&l_Lean_computeStructureResolutionOrder___redArg___closed__0_value;
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___closed__0 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value;
static const lean_closure_object l_Lean_mergeStructureResolutionOrders___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mergeStructureResolutionOrders___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___closed__0_value)} };
static const lean_object* l_Lean_mergeStructureResolutionOrders___redArg___closed__1 = (const lean_object*)&l_Lean_mergeStructureResolutionOrders___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_getStructureResolutionOrder___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getStructureResolutionOrder___redArg___closed__0 = (const lean_object*)&l_Lean_getStructureResolutionOrder___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1));
return v___x_15_;
}
else
{
lean_object* v_val_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_val_16_ = lean_ctor_get(v_x_13_, 0);
lean_inc(v_val_16_);
lean_dec_ref(v_x_13_);
v___x_17_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3));
v___x_18_ = lean_unsigned_to_nat(1024u);
v___x_19_ = l_Lean_Name_reprPrec(v_val_16_, v___x_18_);
v___x_20_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_17_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
v___x_21_ = l_Repr_addAppParen(v___x_20_, v_x_14_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___boxed(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(v_x_22_, v_x_23_);
lean_dec(v_x_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_27_; 
v___x_27_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__1));
return v___x_27_;
}
else
{
lean_object* v_val_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_val_28_ = lean_ctor_get(v_x_25_, 0);
lean_inc(v_val_28_);
lean_dec_ref(v_x_25_);
v___x_29_ = ((lean_object*)(l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0___closed__3));
v___x_30_ = lean_unsigned_to_nat(1024u);
v___x_31_ = l_Lean_instReprExpr_repr(v_val_28_, v___x_30_);
v___x_32_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_29_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = l_Repr_addAppParen(v___x_32_, v_x_26_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1___boxed(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(v_x_34_, v_x_35_);
lean_dec(v_x_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprStructureFieldInfo_repr_spec__2(lean_object* v_a_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_nat_to_int(v_a_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(13u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(10u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(14u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__0));
v___x_75_ = lean_string_length(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__21);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr___redArg(lean_object* v_x_82_){
_start:
{
lean_object* v_fieldName_83_; lean_object* v_projFn_84_; lean_object* v_subobject_x3f_85_; uint8_t v_binderInfo_86_; lean_object* v_autoParam_x3f_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_fieldName_83_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_fieldName_83_);
v_projFn_84_ = lean_ctor_get(v_x_82_, 1);
lean_inc(v_projFn_84_);
v_subobject_x3f_85_ = lean_ctor_get(v_x_82_, 2);
lean_inc(v_subobject_x3f_85_);
v_binderInfo_86_ = lean_ctor_get_uint8(v_x_82_, sizeof(void*)*4);
v_autoParam_x3f_87_ = lean_ctor_get(v_x_82_, 3);
lean_inc(v_autoParam_x3f_87_);
lean_dec_ref(v_x_82_);
v___x_88_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__5));
v___x_89_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__6));
v___x_90_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__7);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = l_Lean_Name_reprPrec(v_fieldName_83_, v___x_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_90_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = 0;
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_89_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__9));
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_box(1);
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__11));
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_88_);
v___x_104_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__12);
v___x_105_ = l_Lean_Name_reprPrec(v_projFn_84_, v___x_91_);
v___x_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*1, v___x_94_);
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_103_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_97_);
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_99_);
v___x_111_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__14));
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_88_);
v___x_114_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__15);
v___x_115_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__0(v_subobject_x3f_85_, v___x_91_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_94_);
v___x_118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_113_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_97_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_99_);
v___x_121_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__17));
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_88_);
v___x_124_ = l_Lean_instReprBinderInfo_repr(v_binderInfo_86_, v___x_91_);
v___x_125_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_114_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_94_);
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_123_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_97_);
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_99_);
v___x_130_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__19));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_88_);
v___x_133_ = l_Option_repr___at___00Lean_instReprStructureFieldInfo_repr_spec__1(v_autoParam_x3f_87_, v___x_91_);
v___x_134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_114_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_94_);
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_132_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_obj_once(&l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22, &l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22_once, _init_l_Lean_instReprStructureFieldInfo_repr___redArg___closed__22);
v___x_138_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__23));
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_136_);
v___x_140_ = ((lean_object*)(l_Lean_instReprStructureFieldInfo_repr___redArg___closed__24));
v___x_141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_137_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*1, v___x_94_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr(lean_object* v_x_144_, lean_object* v_prec_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_instReprStructureFieldInfo_repr___redArg(v_x_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprStructureFieldInfo_repr___boxed(lean_object* v_x_147_, lean_object* v_prec_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_instReprStructureFieldInfo_repr(v_x_147_, v_prec_148_);
lean_dec(v_prec_148_);
return v_res_149_;
}
}
LEAN_EXPORT uint8_t l_Lean_StructureFieldInfo_lt(lean_object* v_i_u2081_152_, lean_object* v_i_u2082_153_){
_start:
{
lean_object* v_fieldName_154_; lean_object* v_fieldName_155_; uint8_t v___x_156_; 
v_fieldName_154_ = lean_ctor_get(v_i_u2081_152_, 0);
v_fieldName_155_ = lean_ctor_get(v_i_u2082_153_, 0);
v___x_156_ = l_Lean_Name_quickLt(v_fieldName_154_, v_fieldName_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_StructureFieldInfo_lt___boxed(lean_object* v_i_u2081_157_, lean_object* v_i_u2082_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lean_StructureFieldInfo_lt(v_i_u2081_157_, v_i_u2082_158_);
lean_dec_ref(v_i_u2082_158_);
lean_dec_ref(v_i_u2081_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureInfo_default___closed__1(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_169_ = lean_box(0);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_168_);
lean_ctor_set(v___x_170_, 3, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureInfo_default(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_instInhabitedStructureInfo_default___closed__1, &l_Lean_instInhabitedStructureInfo_default___closed__1_once, _init_l_Lean_instInhabitedStructureInfo_default___closed__1);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureInfo(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_instInhabitedStructureInfo_default;
return v___x_172_;
}
}
LEAN_EXPORT uint8_t l_Lean_StructureInfo_lt(lean_object* v_i_u2081_173_, lean_object* v_i_u2082_174_){
_start:
{
lean_object* v_structName_175_; lean_object* v_structName_176_; uint8_t v___x_177_; 
v_structName_175_ = lean_ctor_get(v_i_u2081_173_, 0);
v_structName_176_ = lean_ctor_get(v_i_u2082_174_, 0);
v___x_177_ = l_Lean_Name_quickLt(v_structName_175_, v_structName_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_lt___boxed(lean_object* v_i_u2081_178_, lean_object* v_i_u2082_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lean_StructureInfo_lt(v_i_u2081_178_, v_i_u2082_179_);
lean_dec_ref(v_i_u2082_179_);
lean_dec_ref(v_i_u2081_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(lean_object* v_as_182_, lean_object* v_k_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v_m_188_; lean_object* v_a_189_; uint8_t v___x_190_; 
v___x_186_ = lean_nat_add(v_x_184_, v_x_185_);
v___x_187_ = lean_unsigned_to_nat(1u);
v_m_188_ = lean_nat_shiftr(v___x_186_, v___x_187_);
lean_dec(v___x_186_);
v_a_189_ = lean_array_fget_borrowed(v_as_182_, v_m_188_);
v___x_190_ = l_Lean_StructureFieldInfo_lt(v_a_189_, v_k_183_);
if (v___x_190_ == 0)
{
uint8_t v___x_191_; 
lean_dec(v_x_185_);
v___x_191_ = l_Lean_StructureFieldInfo_lt(v_k_183_, v_a_189_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; 
lean_dec(v_m_188_);
lean_dec(v_x_184_);
lean_inc(v_a_189_);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_a_189_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_nat_dec_eq(v_m_188_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_nat_sub(v_m_188_, v___x_187_);
lean_dec(v_m_188_);
v___x_196_ = lean_nat_dec_lt(v___x_195_, v_x_184_);
if (v___x_196_ == 0)
{
v_x_185_ = v___x_195_;
goto _start;
}
else
{
lean_object* v___x_198_; 
lean_dec(v___x_195_);
lean_dec(v_x_184_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec(v_m_188_);
lean_dec(v_x_184_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
}
else
{
lean_object* v___x_200_; uint8_t v___x_201_; 
lean_dec(v_x_184_);
v___x_200_ = lean_nat_add(v_m_188_, v___x_187_);
lean_dec(v_m_188_);
v___x_201_ = lean_nat_dec_le(v___x_200_, v_x_185_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_dec(v___x_200_);
lean_dec(v_x_185_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
v_x_184_ = v___x_200_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg___boxed(lean_object* v_as_204_, lean_object* v_k_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_as_204_, v_k_205_, v_x_206_, v_x_207_);
lean_dec_ref(v_k_205_);
lean_dec_ref(v_as_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f(lean_object* v_info_209_, lean_object* v_i_210_){
_start:
{
lean_object* v_fieldNames_211_; lean_object* v_fieldInfo_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_fieldNames_211_ = lean_ctor_get(v_info_209_, 1);
v_fieldInfo_212_ = lean_ctor_get(v_info_209_, 2);
v___x_213_ = lean_array_get_size(v_fieldNames_211_);
v___x_214_ = lean_nat_dec_lt(v_i_210_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_array_get_size(v_fieldInfo_212_);
v___x_218_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_220_ = lean_box(0);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_sub(v___x_217_, v___x_221_);
v___x_223_ = lean_nat_dec_le(v___x_216_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec(v___x_222_);
return v___x_220_;
}
else
{
lean_object* v_fieldName_224_; lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_fieldName_224_ = lean_array_fget_borrowed(v_fieldNames_211_, v_i_210_);
v___x_225_ = lean_box(0);
v___x_226_ = 0;
lean_inc(v_fieldName_224_);
v___x_227_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_227_, 0, v_fieldName_224_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_220_);
lean_ctor_set(v___x_227_, 3, v___x_220_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*4, v___x_226_);
v___x_228_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_212_, v___x_227_, v___x_216_, v___x_222_);
lean_dec_ref(v___x_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
return v___x_220_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_val_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_val_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_projFn_233_; lean_object* v___x_235_; 
v_projFn_233_ = lean_ctor_get(v_val_229_, 1);
lean_inc(v_projFn_233_);
lean_dec(v_val_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v_projFn_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_projFn_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_StructureInfo_getProjFn_x3f___boxed(lean_object* v_info_238_, lean_object* v_i_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_StructureInfo_getProjFn_x3f(v_info_238_, v_i_239_);
lean_dec(v_i_239_);
lean_dec_ref(v_info_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(lean_object* v_as_241_, lean_object* v_k_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_as_241_, v_k_242_, v_x_243_, v_x_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___boxed(lean_object* v_as_247_, lean_object* v_k_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0(v_as_247_, v_k_248_, v_x_249_, v_x_250_, v_x_251_);
lean_dec_ref(v_k_248_);
lean_dec_ref(v_as_247_);
return v_res_252_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_253_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0, &l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0_once, _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__0);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1, &l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1_once, _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default;
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v_x_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_box(0);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Lean_Structure_0__Lean_initFn___lam__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v_x_260_);
lean_dec_ref(v_x_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(size_t v_sz_262_, size_t v_i_263_, lean_object* v_bs_264_){
_start:
{
uint8_t v___x_265_; 
v___x_265_ = lean_usize_dec_lt(v_i_263_, v_sz_262_);
if (v___x_265_ == 0)
{
return v_bs_264_;
}
else
{
lean_object* v_v_266_; lean_object* v_snd_267_; lean_object* v___x_268_; lean_object* v_bs_x27_269_; size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v_v_266_ = lean_array_uget_borrowed(v_bs_264_, v_i_263_);
v_snd_267_ = lean_ctor_get(v_v_266_, 1);
lean_inc(v_snd_267_);
v___x_268_ = lean_unsigned_to_nat(0u);
v_bs_x27_269_ = lean_array_uset(v_bs_264_, v_i_263_, v___x_268_);
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_add(v_i_263_, v___x_270_);
v___x_272_ = lean_array_uset(v_bs_x27_269_, v_i_263_, v_snd_267_);
v_i_263_ = v___x_271_;
v_bs_264_ = v___x_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_274_, lean_object* v_i_275_, lean_object* v_bs_276_){
_start:
{
size_t v_sz_boxed_277_; size_t v_i_boxed_278_; lean_object* v_res_279_; 
v_sz_boxed_277_ = lean_unbox_usize(v_sz_274_);
lean_dec(v_sz_274_);
v_i_boxed_278_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_res_279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_boxed_277_, v_i_boxed_278_, v_bs_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___lam__0(lean_object* v_ps_280_, lean_object* v_k_281_, lean_object* v_v_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_k_281_);
lean_ctor_set(v___x_283_, 1, v_v_282_);
v___x_284_ = lean_array_push(v_ps_280_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_f_285_, lean_object* v_keys_286_, lean_object* v_vals_287_, lean_object* v_i_288_, lean_object* v_acc_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_array_get_size(v_keys_286_);
v___x_291_ = lean_nat_dec_lt(v_i_288_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_i_288_);
lean_dec(v_f_285_);
return v_acc_289_;
}
else
{
lean_object* v_k_292_; lean_object* v_v_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_k_292_ = lean_array_fget_borrowed(v_keys_286_, v_i_288_);
v_v_293_ = lean_array_fget_borrowed(v_vals_287_, v_i_288_);
lean_inc(v_f_285_);
lean_inc(v_v_293_);
lean_inc(v_k_292_);
v___x_294_ = lean_apply_3(v_f_285_, v_acc_289_, v_k_292_, v_v_293_);
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_add(v_i_288_, v___x_295_);
lean_dec(v_i_288_);
v_i_288_ = v___x_296_;
v_acc_289_ = v___x_294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_f_298_, lean_object* v_keys_299_, lean_object* v_vals_300_, lean_object* v_i_301_, lean_object* v_acc_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_298_, v_keys_299_, v_vals_300_, v_i_301_, v_acc_302_);
lean_dec_ref(v_vals_300_);
lean_dec_ref(v_keys_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_f_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v_es_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_es_307_ = lean_ctor_get(v_x_305_, 0);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_array_get_size(v_es_307_);
v___x_310_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_dec(v_f_304_);
return v_x_306_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_le(v___x_309_, v___x_309_);
if (v___x_311_ == 0)
{
if (v___x_310_ == 0)
{
lean_dec(v_f_304_);
return v_x_306_;
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_309_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_304_, v_es_307_, v___x_312_, v___x_313_, v_x_306_);
return v___x_314_;
}
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_309_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_304_, v_es_307_, v___x_315_, v___x_316_, v_x_306_);
return v___x_317_;
}
}
}
else
{
lean_object* v_ks_318_; lean_object* v_vs_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_ks_318_ = lean_ctor_get(v_x_305_, 0);
v_vs_319_ = lean_ctor_get(v_x_305_, 1);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_304_, v_ks_318_, v_vs_319_, v___x_320_, v_x_306_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object* v_f_322_, lean_object* v_as_323_, size_t v_i_324_, size_t v_stop_325_, lean_object* v_b_326_){
_start:
{
lean_object* v___y_328_; uint8_t v___x_332_; 
v___x_332_ = lean_usize_dec_eq(v_i_324_, v_stop_325_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_array_uget_borrowed(v_as_323_, v_i_324_);
switch(lean_obj_tag(v___x_333_))
{
case 0:
{
lean_object* v_key_334_; lean_object* v_val_335_; lean_object* v___x_336_; 
v_key_334_ = lean_ctor_get(v___x_333_, 0);
v_val_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_f_322_);
lean_inc(v_val_335_);
lean_inc(v_key_334_);
v___x_336_ = lean_apply_3(v_f_322_, v_b_326_, v_key_334_, v_val_335_);
v___y_328_ = v___x_336_;
goto v___jp_327_;
}
case 1:
{
lean_object* v_node_337_; lean_object* v___x_338_; 
v_node_337_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_f_322_);
v___x_338_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_322_, v_node_337_, v_b_326_);
v___y_328_ = v___x_338_;
goto v___jp_327_;
}
default: 
{
v___y_328_ = v_b_326_;
goto v___jp_327_;
}
}
}
else
{
lean_dec(v_f_322_);
return v_b_326_;
}
v___jp_327_:
{
size_t v___x_329_; size_t v___x_330_; 
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_324_, v___x_329_);
v_i_324_ = v___x_330_;
v_b_326_ = v___y_328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_f_339_, lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_stop_342_, lean_object* v_b_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_342_);
lean_dec(v_stop_342_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_339_, v_as_340_, v_i_boxed_344_, v_stop_boxed_345_, v_b_343_);
lean_dec_ref(v_as_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_f_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_347_, v_x_348_, v_x_349_);
lean_dec_ref(v_x_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(lean_object* v_f_351_, lean_object* v_x1_352_, lean_object* v_x2_353_, lean_object* v_x3_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_apply_3(v_f_351_, v_x1_352_, v_x2_353_, v_x3_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_map_356_, lean_object* v_f_357_, lean_object* v_init_358_){
_start:
{
lean_object* v___f_359_; lean_object* v___x_360_; 
v___f_359_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_359_, 0, v_f_357_);
v___x_360_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v___f_359_, v_map_356_, v_init_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_map_361_, lean_object* v_f_362_, lean_object* v_init_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_361_, v_f_362_, v_init_363_);
lean_dec_ref(v_map_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_368_){
_start:
{
lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___f_369_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_370_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___closed__1));
v___x_371_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_368_, v___f_369_, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_m_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_372_);
lean_dec_ref(v_m_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_375_, lean_object* v_lo_376_, lean_object* v_hi_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_nat_dec_lt(v_lo_376_, v_hi_377_);
if (v___x_378_ == 0)
{
lean_dec(v_lo_376_);
return v_as_375_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_fst_381_; lean_object* v_snd_382_; uint8_t v___x_383_; 
v___x_379_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_376_);
v___x_380_ = l_Array_qpartition___redArg(v_as_375_, v___x_379_, v_lo_376_, v_hi_377_);
v_fst_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_fst_381_);
v_snd_382_ = lean_ctor_get(v___x_380_, 1);
lean_inc(v_snd_382_);
lean_dec_ref(v___x_380_);
v___x_383_ = lean_nat_dec_le(v_hi_377_, v_fst_381_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_snd_382_, v_lo_376_, v_fst_381_);
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_add(v_fst_381_, v___x_385_);
lean_dec(v_fst_381_);
v_as_375_ = v___x_384_;
v_lo_376_ = v___x_386_;
goto _start;
}
else
{
lean_dec(v_fst_381_);
lean_dec(v_lo_376_);
return v_snd_382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_388_, lean_object* v_lo_389_, lean_object* v_hi_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_as_388_, v_lo_389_, v_hi_390_);
lean_dec(v_hi_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_392_, lean_object* v_x_393_, lean_object* v_s_394_, uint8_t v_x_395_){
_start:
{
lean_object* v_snd_396_; lean_object* v___x_397_; size_t v_sz_398_; size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_snd_396_ = lean_ctor_get(v_s_394_, 1);
v___x_397_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_396_);
v_sz_398_ = lean_array_size(v___x_397_);
v___x_399_ = ((size_t)0ULL);
v___x_400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_398_, v___x_399_, v___x_397_);
v___x_401_ = lean_array_get_size(v___x_400_);
v___x_402_ = lean_nat_dec_eq(v___x_401_, v___x_392_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___y_406_; uint8_t v___x_410_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_sub(v___x_401_, v___x_403_);
v___x_410_ = lean_nat_dec_le(v___x_392_, v___x_404_);
if (v___x_410_ == 0)
{
lean_dec(v___x_392_);
lean_inc(v___x_404_);
v___y_406_ = v___x_404_;
goto v___jp_405_;
}
else
{
v___y_406_ = v___x_392_;
goto v___jp_405_;
}
v___jp_405_:
{
uint8_t v___x_407_; 
v___x_407_ = lean_nat_dec_le(v___y_406_, v___x_404_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec(v___x_404_);
lean_inc(v___y_406_);
v___x_408_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_400_, v___y_406_, v___y_406_);
lean_dec(v___y_406_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_400_, v___y_406_, v___x_404_);
lean_dec(v___x_404_);
return v___x_409_;
}
}
}
else
{
lean_dec(v___x_392_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_411_, lean_object* v_x_412_, lean_object* v_s_413_, lean_object* v_x_414_){
_start:
{
uint8_t v_x_1506__boxed_415_; lean_object* v_res_416_; 
v_x_1506__boxed_415_ = lean_unbox(v_x_414_);
v_res_416_ = l___private_Lean_Structure_0__Lean_initFn___lam__1_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_411_, v_x_412_, v_s_413_, v_x_1506__boxed_415_);
lean_dec_ref(v_s_413_);
lean_dec_ref(v_x_412_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_snd_419_; lean_object* v___x_420_; size_t v_sz_421_; size_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_snd_419_ = lean_ctor_get(v_x_418_, 1);
v___x_420_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_snd_419_);
v_sz_421_ = lean_array_size(v___x_420_);
v___x_422_ = ((size_t)0ULL);
v___x_423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__1(v_sz_421_, v___x_422_, v___x_420_);
v___x_424_ = lean_array_get_size(v___x_423_);
v___x_425_ = lean_nat_dec_eq(v___x_424_, v___x_417_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___y_429_; uint8_t v___x_433_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_sub(v___x_424_, v___x_426_);
v___x_433_ = lean_nat_dec_le(v___x_417_, v___x_427_);
if (v___x_433_ == 0)
{
lean_dec(v___x_417_);
lean_inc(v___x_427_);
v___y_429_ = v___x_427_;
goto v___jp_428_;
}
else
{
v___y_429_ = v___x_417_;
goto v___jp_428_;
}
v___jp_428_:
{
uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_le(v___y_429_, v___x_427_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v___x_427_);
lean_inc(v___y_429_);
v___x_431_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_423_, v___y_429_, v___y_429_);
lean_dec(v___y_429_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v___x_423_, v___y_429_, v___x_427_);
lean_dec(v___x_427_);
return v___x_432_;
}
}
}
else
{
lean_dec(v___x_417_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Structure_0__Lean_initFn___lam__2_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_434_, v_x_435_);
lean_dec_ref(v_x_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_ks_441_; lean_object* v_vs_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_466_; 
v_ks_441_ = lean_ctor_get(v_x_437_, 0);
v_vs_442_ = lean_ctor_get(v_x_437_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_x_437_);
if (v_isSharedCheck_466_ == 0)
{
v___x_444_ = v_x_437_;
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_vs_442_);
lean_inc(v_ks_441_);
lean_dec(v_x_437_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_array_get_size(v_ks_441_);
v___x_447_ = lean_nat_dec_lt(v_x_438_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
lean_dec(v_x_438_);
v___x_448_ = lean_array_push(v_ks_441_, v_x_439_);
v___x_449_ = lean_array_push(v_vs_442_, v_x_440_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_449_);
lean_ctor_set(v___x_444_, 0, v___x_448_);
v___x_451_ = v___x_444_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
else
{
lean_object* v_k_x27_453_; uint8_t v___x_454_; 
v_k_x27_453_ = lean_array_fget_borrowed(v_ks_441_, v_x_438_);
v___x_454_ = lean_name_eq(v_x_439_, v_k_x27_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_456_; 
if (v_isShared_445_ == 0)
{
v___x_456_ = v___x_444_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_ks_441_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_vs_442_);
v___x_456_ = v_reuseFailAlloc_460_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_x_438_, v___x_457_);
lean_dec(v_x_438_);
v_x_437_ = v___x_456_;
v_x_438_ = v___x_458_;
goto _start;
}
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = lean_array_fset(v_ks_441_, v_x_438_, v_x_439_);
v___x_462_ = lean_array_fset(v_vs_442_, v_x_438_, v_x_440_);
lean_dec(v_x_438_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_462_);
lean_ctor_set(v___x_444_, 0, v___x_461_);
v___x_464_ = v___x_444_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(lean_object* v_n_467_, lean_object* v_k_468_, lean_object* v_v_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(v_n_467_, v___x_470_, v_k_468_, v_v_469_);
return v___x_471_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_472_; uint64_t v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1723u);
v___x_473_ = lean_uint64_of_nat(v___x_472_);
return v___x_473_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; 
v___x_474_ = ((size_t)5ULL);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_shift_left(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; 
v___x_477_ = ((size_t)1ULL);
v___x_478_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__0);
v___x_479_ = lean_usize_sub(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(lean_object* v_x_481_, size_t v_x_482_, size_t v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v_es_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v_j_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_es_486_ = lean_ctor_get(v_x_481_, 0);
v___x_487_ = ((size_t)5ULL);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_490_ = lean_usize_land(v_x_482_, v___x_489_);
v_j_491_ = lean_usize_to_nat(v___x_490_);
v___x_492_ = lean_array_get_size(v_es_486_);
v___x_493_ = lean_nat_dec_lt(v_j_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec(v_j_491_);
lean_dec(v_x_485_);
lean_dec(v_x_484_);
return v_x_481_;
}
else
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_530_; 
lean_inc_ref(v_es_486_);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_x_481_, 0);
lean_dec(v_unused_531_);
v___x_495_ = v_x_481_;
v_isShared_496_ = v_isSharedCheck_530_;
goto v_resetjp_494_;
}
else
{
lean_dec(v_x_481_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_530_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_v_497_; lean_object* v___x_498_; lean_object* v_xs_x27_499_; lean_object* v___y_501_; 
v_v_497_ = lean_array_fget(v_es_486_, v_j_491_);
v___x_498_ = lean_box(0);
v_xs_x27_499_ = lean_array_fset(v_es_486_, v_j_491_, v___x_498_);
switch(lean_obj_tag(v_v_497_))
{
case 0:
{
lean_object* v_key_506_; lean_object* v_val_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_517_; 
v_key_506_ = lean_ctor_get(v_v_497_, 0);
v_val_507_ = lean_ctor_get(v_v_497_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_v_497_);
if (v_isSharedCheck_517_ == 0)
{
v___x_509_ = v_v_497_;
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_val_507_);
lean_inc(v_key_506_);
lean_dec(v_v_497_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = lean_name_eq(v_x_484_, v_key_506_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_del_object(v___x_509_);
v___x_512_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_506_, v_val_507_, v_x_484_, v_x_485_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___y_501_ = v___x_513_;
goto v___jp_500_;
}
else
{
lean_object* v___x_515_; 
lean_dec(v_val_507_);
lean_dec(v_key_506_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_x_485_);
lean_ctor_set(v___x_509_, 0, v_x_484_);
v___x_515_ = v___x_509_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_x_484_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_x_485_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v___y_501_ = v___x_515_;
goto v___jp_500_;
}
}
}
}
case 1:
{
lean_object* v_node_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_528_; 
v_node_518_ = lean_ctor_get(v_v_497_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_v_497_);
if (v_isSharedCheck_528_ == 0)
{
v___x_520_ = v_v_497_;
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_node_518_);
lean_dec(v_v_497_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = lean_usize_shift_right(v_x_482_, v___x_487_);
v___x_523_ = lean_usize_add(v_x_483_, v___x_488_);
v___x_524_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_node_518_, v___x_522_, v___x_523_, v_x_484_, v_x_485_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v___y_501_ = v___x_526_;
goto v___jp_500_;
}
}
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_x_484_);
lean_ctor_set(v___x_529_, 1, v_x_485_);
v___y_501_ = v___x_529_;
goto v___jp_500_;
}
}
v___jp_500_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_array_fset(v_xs_x27_499_, v_j_491_, v___y_501_);
lean_dec(v_j_491_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_502_);
v___x_504_ = v___x_495_;
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
else
{
lean_object* v_ks_532_; lean_object* v_vs_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_553_; 
v_ks_532_ = lean_ctor_get(v_x_481_, 0);
v_vs_533_ = lean_ctor_get(v_x_481_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_553_ == 0)
{
v___x_535_ = v_x_481_;
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_vs_533_);
lean_inc(v_ks_532_);
lean_dec(v_x_481_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_ks_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_vs_533_);
v___x_538_ = v_reuseFailAlloc_552_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v_newNode_539_; uint8_t v___y_541_; size_t v___x_547_; uint8_t v___x_548_; 
v_newNode_539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(v___x_538_, v_x_484_, v_x_485_);
v___x_547_ = ((size_t)7ULL);
v___x_548_ = lean_usize_dec_le(v___x_547_, v_x_483_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_539_);
v___x_550_ = lean_unsigned_to_nat(4u);
v___x_551_ = lean_nat_dec_lt(v___x_549_, v___x_550_);
lean_dec(v___x_549_);
v___y_541_ = v___x_551_;
goto v___jp_540_;
}
else
{
v___y_541_ = v___x_548_;
goto v___jp_540_;
}
v___jp_540_:
{
if (v___y_541_ == 0)
{
lean_object* v_ks_542_; lean_object* v_vs_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_ks_542_ = lean_ctor_get(v_newNode_539_, 0);
lean_inc_ref(v_ks_542_);
v_vs_543_ = lean_ctor_get(v_newNode_539_, 1);
lean_inc_ref(v_vs_543_);
lean_dec_ref(v_newNode_539_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__2);
v___x_546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_x_483_, v_ks_542_, v_vs_543_, v___x_544_, v___x_545_);
lean_dec_ref(v_vs_543_);
lean_dec_ref(v_ks_542_);
return v___x_546_;
}
else
{
return v_newNode_539_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(size_t v_depth_554_, lean_object* v_keys_555_, lean_object* v_vals_556_, lean_object* v_i_557_, lean_object* v_entries_558_){
_start:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_keys_555_);
v___x_560_ = lean_nat_dec_lt(v_i_557_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec(v_i_557_);
return v_entries_558_;
}
else
{
lean_object* v_k_561_; lean_object* v_v_562_; uint64_t v___y_564_; 
v_k_561_ = lean_array_fget_borrowed(v_keys_555_, v_i_557_);
v_v_562_ = lean_array_fget_borrowed(v_vals_556_, v_i_557_);
if (lean_obj_tag(v_k_561_) == 0)
{
uint64_t v___x_575_; 
v___x_575_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_564_ = v___x_575_;
goto v___jp_563_;
}
else
{
uint64_t v_hash_576_; 
v_hash_576_ = lean_ctor_get_uint64(v_k_561_, sizeof(void*)*2);
v___y_564_ = v_hash_576_;
goto v___jp_563_;
}
v___jp_563_:
{
size_t v_h_565_; size_t v___x_566_; lean_object* v___x_567_; size_t v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v_h_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_h_565_ = lean_uint64_to_usize(v___y_564_);
v___x_566_ = ((size_t)5ULL);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_sub(v_depth_554_, v___x_568_);
v___x_570_ = lean_usize_mul(v___x_566_, v___x_569_);
v_h_571_ = lean_usize_shift_right(v_h_565_, v___x_570_);
v___x_572_ = lean_nat_add(v_i_557_, v___x_567_);
lean_dec(v_i_557_);
lean_inc(v_v_562_);
lean_inc(v_k_561_);
v___x_573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_entries_558_, v_h_571_, v_depth_554_, v_k_561_, v_v_562_);
v_i_557_ = v___x_572_;
v_entries_558_ = v___x_573_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_depth_577_, lean_object* v_keys_578_, lean_object* v_vals_579_, lean_object* v_i_580_, lean_object* v_entries_581_){
_start:
{
size_t v_depth_boxed_582_; lean_object* v_res_583_; 
v_depth_boxed_582_ = lean_unbox_usize(v_depth_577_);
lean_dec(v_depth_577_);
v_res_583_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_depth_boxed_582_, v_keys_578_, v_vals_579_, v_i_580_, v_entries_581_);
lean_dec_ref(v_vals_579_);
lean_dec_ref(v_keys_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___boxed(lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
size_t v_x_1672__boxed_589_; size_t v_x_1673__boxed_590_; lean_object* v_res_591_; 
v_x_1672__boxed_589_ = lean_unbox_usize(v_x_585_);
lean_dec(v_x_585_);
v_x_1673__boxed_590_ = lean_unbox_usize(v_x_586_);
lean_dec(v_x_586_);
v_res_591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_584_, v_x_1672__boxed_589_, v_x_1673__boxed_590_, v_x_587_, v_x_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
uint64_t v___y_596_; 
if (lean_obj_tag(v_x_593_) == 0)
{
uint64_t v___x_600_; 
v___x_600_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_596_ = v___x_600_;
goto v___jp_595_;
}
else
{
uint64_t v_hash_601_; 
v_hash_601_ = lean_ctor_get_uint64(v_x_593_, sizeof(void*)*2);
v___y_596_ = v_hash_601_;
goto v___jp_595_;
}
v___jp_595_:
{
size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_uint64_to_usize(v___y_596_);
v___x_598_ = ((size_t)1ULL);
v___x_599_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_592_, v___x_597_, v___x_598_, v_x_593_, v_x_594_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__3_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_602_, lean_object* v_x_603_, lean_object* v_e_604_){
_start:
{
lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_614_; 
v_snd_605_ = lean_ctor_get(v_x_603_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_x_603_, 0);
lean_dec(v_unused_615_);
v___x_607_ = v_x_603_;
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_dec(v_x_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_structName_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v_structName_609_ = lean_ctor_get(v_e_604_, 0);
lean_inc(v_structName_609_);
v___x_610_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_snd_605_, v_structName_609_, v_e_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_610_);
lean_ctor_set(v___x_607_, 0, v___x_602_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(lean_object* v___x_622_, lean_object* v_x_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_622_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v___x_627_, lean_object* v_x_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(v___x_627_, v_x_628_, v___y_629_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_x_628_);
return v_res_631_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1, &l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1_once, _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default___closed__1);
v___x_662_ = lean_box(0);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
return v___x_663_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_664_; lean_object* v___f_665_; 
v___x_664_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_665_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__4_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_665_, 0, v___x_664_);
return v___f_665_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_666_; lean_object* v___f_667_; 
v___x_666_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__14_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_667_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_initFn___lam__5_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_667_, 0, v___x_666_);
return v___f_667_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___f_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_668_ = lean_box(0);
v___x_669_ = lean_box(2);
v___f_670_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__0_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_671_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__7_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_672_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__13_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___f_673_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__16_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___f_674_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__15_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_675_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__12_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_676_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___f_674_);
lean_ctor_set(v___x_676_, 2, v___f_673_);
lean_ctor_set(v___x_676_, 3, v___f_672_);
lean_ctor_set(v___x_676_, 4, v___f_671_);
lean_ctor_set(v___x_676_, 5, v___f_670_);
lean_ctor_set(v___x_676_, 6, v___x_669_);
lean_ctor_set(v___x_676_, 7, v___x_668_);
return v___x_676_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___f_677_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_initFn___closed__8_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_));
v___x_678_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__17_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___f_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_, &l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__once, _init_l___private_Lean_Structure_0__Lean_initFn___closed__18_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_);
v___x_682_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2____boxed(lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_685_, lean_object* v_m_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___redArg(v_m_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_688_, lean_object* v_m_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0(v_00_u03b2_688_, v_m_689_);
lean_dec_ref(v_m_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(lean_object* v_n_691_, lean_object* v_as_692_, lean_object* v_lo_693_, lean_object* v_hi_694_, lean_object* v_w_695_, lean_object* v_hlo_696_, lean_object* v_hhi_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___redArg(v_as_692_, v_lo_693_, v_hi_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_699_, lean_object* v_as_700_, lean_object* v_lo_701_, lean_object* v_hi_702_, lean_object* v_w_703_, lean_object* v_hlo_704_, lean_object* v_hhi_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__2(v_n_699_, v_as_700_, v_lo_701_, v_hi_702_, v_w_703_, v_hlo_704_, v_hhi_705_);
lean_dec(v_hi_702_);
lean_dec(v_n_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3___redArg(v_x_708_, v_x_709_, v_x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03c3_712_, lean_object* v_00_u03b2_713_, lean_object* v_map_714_, lean_object* v_f_715_, lean_object* v_init_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_714_, v_f_715_, v_init_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03c3_718_, lean_object* v_00_u03b2_719_, lean_object* v_map_720_, lean_object* v_f_721_, lean_object* v_init_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_718_, v_00_u03b2_719_, v_map_720_, v_f_721_, v_init_722_);
lean_dec_ref(v_map_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(lean_object* v_00_u03b2_724_, lean_object* v_x_725_, size_t v_x_726_, size_t v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg(v_x_725_, v_x_726_, v_x_727_, v_x_728_, v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___boxed(lean_object* v_00_u03b2_731_, lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
size_t v_x_2073__boxed_737_; size_t v_x_2074__boxed_738_; lean_object* v_res_739_; 
v_x_2073__boxed_737_ = lean_unbox_usize(v_x_733_);
lean_dec(v_x_733_);
v_x_2074__boxed_738_ = lean_unbox_usize(v_x_734_);
lean_dec(v_x_734_);
v_res_739_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4(v_00_u03b2_731_, v_x_732_, v_x_2073__boxed_737_, v_x_2074__boxed_738_, v_x_735_, v_x_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_map_740_, lean_object* v_f_741_, lean_object* v_init_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_741_, v_map_740_, v_init_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_744_, lean_object* v_f_745_, lean_object* v_init_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_map_744_, v_f_745_, v_init_746_);
lean_dec_ref(v_map_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03c3_748_, lean_object* v_00_u03b2_749_, lean_object* v_map_750_, lean_object* v_f_751_, lean_object* v_init_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_751_, v_map_750_, v_init_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_754_, lean_object* v_00_u03b2_755_, lean_object* v_map_756_, lean_object* v_f_757_, lean_object* v_init_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_754_, v_00_u03b2_755_, v_map_756_, v_f_757_, v_init_758_);
lean_dec_ref(v_map_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6(lean_object* v_00_u03b2_760_, lean_object* v_n_761_, lean_object* v_k_762_, lean_object* v_v_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6___redArg(v_n_761_, v_k_762_, v_v_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7(lean_object* v_00_u03b2_765_, size_t v_depth_766_, lean_object* v_keys_767_, lean_object* v_vals_768_, lean_object* v_heq_769_, lean_object* v_i_770_, lean_object* v_entries_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg(v_depth_766_, v_keys_767_, v_vals_768_, v_i_770_, v_entries_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_773_, lean_object* v_depth_774_, lean_object* v_keys_775_, lean_object* v_vals_776_, lean_object* v_heq_777_, lean_object* v_i_778_, lean_object* v_entries_779_){
_start:
{
size_t v_depth_boxed_780_; lean_object* v_res_781_; 
v_depth_boxed_780_ = lean_unbox_usize(v_depth_774_);
lean_dec(v_depth_774_);
v_res_781_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7(v_00_u03b2_773_, v_depth_boxed_780_, v_keys_775_, v_vals_776_, v_heq_777_, v_i_778_, v_entries_779_);
lean_dec_ref(v_vals_776_);
lean_dec_ref(v_keys_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03c3_782_, lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_f_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_785_, v_x_786_, v_x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03c3_789_, lean_object* v_00_u03b1_790_, lean_object* v_00_u03b2_791_, lean_object* v_f_792_, lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_789_, v_00_u03b1_790_, v_00_u03b2_791_, v_f_792_, v_x_793_, v_x_794_);
lean_dec_ref(v_x_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__6_spec__8___redArg(v_x_797_, v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_802_, lean_object* v_00_u03b2_803_, lean_object* v_00_u03c3_804_, lean_object* v_f_805_, lean_object* v_as_806_, size_t v_i_807_, size_t v_stop_808_, lean_object* v_b_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_f_805_, v_as_806_, v_i_807_, v_stop_808_, v_b_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_00_u03c3_813_, lean_object* v_f_814_, lean_object* v_as_815_, lean_object* v_i_816_, lean_object* v_stop_817_, lean_object* v_b_818_){
_start:
{
size_t v_i_boxed_819_; size_t v_stop_boxed_820_; lean_object* v_res_821_; 
v_i_boxed_819_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_stop_boxed_820_ = lean_unbox_usize(v_stop_817_);
lean_dec(v_stop_817_);
v_res_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_811_, v_00_u03b2_812_, v_00_u03c3_813_, v_f_814_, v_as_815_, v_i_boxed_819_, v_stop_boxed_820_, v_b_818_);
lean_dec_ref(v_as_815_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03c3_822_, lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_f_825_, lean_object* v_keys_826_, lean_object* v_vals_827_, lean_object* v_heq_828_, lean_object* v_i_829_, lean_object* v_acc_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_f_825_, v_keys_826_, v_vals_827_, v_i_829_, v_acc_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03c3_832_, lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_f_835_, lean_object* v_keys_836_, lean_object* v_vals_837_, lean_object* v_heq_838_, lean_object* v_i_839_, lean_object* v_acc_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03c3_832_, v_00_u03b1_833_, v_00_u03b2_834_, v_f_835_, v_keys_836_, v_vals_837_, v_heq_838_, v_i_839_, v_acc_840_);
lean_dec_ref(v_vals_837_);
lean_dec_ref(v_keys_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(size_t v_sz_849_, size_t v_i_850_, lean_object* v_bs_851_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_850_, v_sz_849_);
if (v___x_852_ == 0)
{
return v_bs_851_;
}
else
{
lean_object* v_v_853_; lean_object* v_fieldName_854_; lean_object* v___x_855_; lean_object* v_bs_x27_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v_v_853_ = lean_array_uget_borrowed(v_bs_851_, v_i_850_);
v_fieldName_854_ = lean_ctor_get(v_v_853_, 0);
lean_inc(v_fieldName_854_);
v___x_855_ = lean_unsigned_to_nat(0u);
v_bs_x27_856_ = lean_array_uset(v_bs_851_, v_i_850_, v___x_855_);
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_850_, v___x_857_);
v___x_859_ = lean_array_uset(v_bs_x27_856_, v_i_850_, v_fieldName_854_);
v_i_850_ = v___x_858_;
v_bs_851_ = v___x_859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0___boxed(lean_object* v_sz_861_, lean_object* v_i_862_, lean_object* v_bs_863_){
_start:
{
size_t v_sz_boxed_864_; size_t v_i_boxed_865_; lean_object* v_res_866_; 
v_sz_boxed_864_ = lean_unbox_usize(v_sz_861_);
lean_dec(v_sz_861_);
v_i_boxed_865_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_boxed_864_, v_i_boxed_865_, v_bs_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(lean_object* v_as_868_, lean_object* v_lo_869_, lean_object* v_hi_870_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = lean_nat_dec_lt(v_lo_869_, v_hi_870_);
if (v___x_871_ == 0)
{
lean_dec(v_lo_869_);
return v_as_868_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; uint8_t v___x_876_; 
v___x_872_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___closed__0));
lean_inc(v_lo_869_);
v___x_873_ = l_Array_qpartition___redArg(v_as_868_, v___x_872_, v_lo_869_, v_hi_870_);
v_fst_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_fst_874_);
v_snd_875_ = lean_ctor_get(v___x_873_, 1);
lean_inc(v_snd_875_);
lean_dec_ref(v___x_873_);
v___x_876_ = lean_nat_dec_le(v_hi_870_, v_fst_874_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_snd_875_, v_lo_869_, v_fst_874_);
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_nat_add(v_fst_874_, v___x_878_);
lean_dec(v_fst_874_);
v_as_868_ = v___x_877_;
v_lo_869_ = v___x_879_;
goto _start;
}
else
{
lean_dec(v_fst_874_);
lean_dec(v_lo_869_);
return v_snd_875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg___boxed(lean_object* v_as_881_, lean_object* v_lo_882_, lean_object* v_hi_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_as_881_, v_lo_882_, v_hi_883_);
lean_dec(v_hi_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerStructure(lean_object* v_env_887_, lean_object* v_e_888_){
_start:
{
lean_object* v_structName_889_; lean_object* v_fields_890_; lean_object* v___x_891_; size_t v_sz_892_; size_t v___x_893_; lean_object* v___x_894_; lean_object* v___y_896_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_structName_889_ = lean_ctor_get(v_e_888_, 0);
lean_inc(v_structName_889_);
v_fields_890_ = lean_ctor_get(v_e_888_, 1);
lean_inc_ref(v_fields_890_);
lean_dec_ref(v_e_888_);
v___x_891_ = l___private_Lean_Structure_0__Lean_structureExt;
v_sz_892_ = lean_array_size(v_fields_890_);
v___x_893_ = ((size_t)0ULL);
lean_inc_ref(v_fields_890_);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_registerStructure_spec__0(v_sz_892_, v___x_893_, v_fields_890_);
v___x_907_ = lean_array_get_size(v_fields_890_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_nat_dec_eq(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___y_913_; uint8_t v___x_915_; 
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_sub(v___x_907_, v___x_910_);
v___x_915_ = lean_nat_dec_le(v___x_908_, v___x_911_);
if (v___x_915_ == 0)
{
lean_inc(v___x_911_);
v___y_913_ = v___x_911_;
goto v___jp_912_;
}
else
{
v___y_913_ = v___x_908_;
goto v___jp_912_;
}
v___jp_912_:
{
uint8_t v___x_914_; 
v___x_914_ = lean_nat_dec_le(v___y_913_, v___x_911_);
if (v___x_914_ == 0)
{
lean_dec(v___x_911_);
lean_inc(v___y_913_);
v___y_904_ = v___y_913_;
v___y_905_ = v___y_913_;
goto v___jp_903_;
}
else
{
v___y_904_ = v___y_913_;
v___y_905_ = v___x_911_;
goto v___jp_903_;
}
}
}
else
{
v___y_896_ = v_fields_890_;
goto v___jp_895_;
}
v___jp_895_:
{
lean_object* v_toEnvExtension_897_; lean_object* v_asyncMode_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_toEnvExtension_897_ = lean_ctor_get(v___x_891_, 0);
lean_inc_ref(v_toEnvExtension_897_);
v_asyncMode_898_ = lean_ctor_get(v_toEnvExtension_897_, 2);
lean_inc(v_asyncMode_898_);
lean_dec_ref(v_toEnvExtension_897_);
v___x_899_ = ((lean_object*)(l_Lean_registerStructure___closed__0));
v___x_900_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_900_, 0, v_structName_889_);
lean_ctor_set(v___x_900_, 1, v___x_894_);
lean_ctor_set(v___x_900_, 2, v___y_896_);
lean_ctor_set(v___x_900_, 3, v___x_899_);
v___x_901_ = lean_box(0);
v___x_902_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_891_, v_env_887_, v___x_900_, v_asyncMode_898_, v___x_901_);
lean_dec(v_asyncMode_898_);
return v___x_902_;
}
v___jp_903_:
{
lean_object* v___x_906_; 
v___x_906_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_fields_890_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
v___y_896_ = v___x_906_;
goto v___jp_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(lean_object* v_n_916_, lean_object* v_as_917_, lean_object* v_lo_918_, lean_object* v_hi_919_, lean_object* v_w_920_, lean_object* v_hlo_921_, lean_object* v_hhi_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___redArg(v_as_917_, v_lo_918_, v_hi_919_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1___boxed(lean_object* v_n_924_, lean_object* v_as_925_, lean_object* v_lo_926_, lean_object* v_hi_927_, lean_object* v_w_928_, lean_object* v_hlo_929_, lean_object* v_hhi_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerStructure_spec__1(v_n_924_, v_as_925_, v_lo_926_, v_hi_927_, v_w_928_, v_hlo_929_, v_hhi_930_);
lean_dec(v_hi_927_);
lean_dec(v_n_924_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0(lean_object* v_val_932_, lean_object* v_parentInfo_933_, lean_object* v___x_934_, lean_object* v_asyncMode_935_, lean_object* v___x_936_, lean_object* v_env_937_){
_start:
{
lean_object* v_structName_938_; lean_object* v_fieldNames_939_; lean_object* v_fieldInfo_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_structName_938_ = lean_ctor_get(v_val_932_, 0);
v_fieldNames_939_ = lean_ctor_get(v_val_932_, 1);
v_fieldInfo_940_ = lean_ctor_get(v_val_932_, 2);
v_isSharedCheck_948_ = !lean_is_exclusive(v_val_932_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_val_932_, 3);
lean_dec(v_unused_949_);
v___x_942_ = v_val_932_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_fieldInfo_940_);
lean_inc(v_fieldNames_939_);
lean_inc(v_structName_938_);
lean_dec(v_val_932_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 3, v_parentInfo_933_);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_structName_938_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_fieldNames_939_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_fieldInfo_940_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_parentInfo_933_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_934_, v_env_937_, v___x_945_, v_asyncMode_935_, v___x_936_);
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__0___boxed(lean_object* v_val_950_, lean_object* v_parentInfo_951_, lean_object* v___x_952_, lean_object* v_asyncMode_953_, lean_object* v___x_954_, lean_object* v_env_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_setStructureParents___redArg___lam__0(v_val_950_, v_parentInfo_951_, v___x_952_, v_asyncMode_953_, v___x_954_, v_env_955_);
lean_dec(v_asyncMode_953_);
return v_res_956_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_setStructureParents___redArg___lam__1___closed__2));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg___lam__1(lean_object* v___x_963_, lean_object* v___x_964_, lean_object* v___x_965_, lean_object* v_structName_966_, lean_object* v_parentInfo_967_, lean_object* v_modifyEnv_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_____do__lift_971_){
_start:
{
lean_object* v___x_972_; lean_object* v_toEnvExtension_973_; lean_object* v_asyncMode_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_993_; 
v___x_972_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc_ref(v_toEnvExtension_973_);
v_asyncMode_974_ = lean_ctor_get(v_toEnvExtension_973_, 2);
lean_inc(v_asyncMode_974_);
lean_dec_ref(v_toEnvExtension_973_);
v___x_975_ = lean_box(0);
v___x_976_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_963_, v___x_972_, v_____do__lift_971_, v_asyncMode_974_, v___x_975_);
v_snd_977_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v___x_976_, 0);
lean_dec(v_unused_994_);
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_993_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_993_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; 
lean_inc(v_structName_966_);
v___x_981_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_964_, v___x_965_, v_snd_977_, v_structName_966_);
if (lean_obj_tag(v___x_981_) == 1)
{
lean_object* v_val_982_; lean_object* v___f_983_; lean_object* v___x_984_; 
lean_del_object(v___x_979_);
lean_dec_ref(v_inst_970_);
lean_dec_ref(v_inst_969_);
lean_dec(v_structName_966_);
v_val_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_val_982_);
lean_dec_ref(v___x_981_);
v___f_983_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_983_, 0, v_val_982_);
lean_closure_set(v___f_983_, 1, v_parentInfo_967_);
lean_closure_set(v___f_983_, 2, v___x_972_);
lean_closure_set(v___f_983_, 3, v_asyncMode_974_);
lean_closure_set(v___f_983_, 4, v___x_975_);
v___x_984_ = lean_apply_1(v_modifyEnv_968_, v___f_983_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
lean_dec(v___x_981_);
lean_dec(v_asyncMode_974_);
lean_dec(v_modifyEnv_968_);
lean_dec_ref(v_parentInfo_967_);
v___x_985_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__1, &l_Lean_setStructureParents___redArg___lam__1___closed__1_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__1);
v___x_986_ = l_Lean_MessageData_ofName(v_structName_966_);
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 7);
lean_ctor_set(v___x_979_, 1, v___x_986_);
lean_ctor_set(v___x_979_, 0, v___x_985_);
v___x_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v___x_986_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_obj_once(&l_Lean_setStructureParents___redArg___lam__1___closed__3, &l_Lean_setStructureParents___redArg___lam__1___closed__3_once, _init_l_Lean_setStructureParents___redArg___lam__1___closed__3);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_throwError___redArg(v_inst_969_, v_inst_970_, v___x_990_);
return v___x_991_;
}
}
}
}
}
static lean_object* _init_l_Lean_setStructureParents___redArg___closed__2(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default;
v___x_998_ = lean_box(0);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents___redArg(lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_structName_1003_, lean_object* v_parentInfo_1004_){
_start:
{
lean_object* v_toBind_1005_; lean_object* v_getEnv_1006_; lean_object* v_modifyEnv_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
v_toBind_1005_ = lean_ctor_get(v_inst_1000_, 1);
lean_inc(v_toBind_1005_);
v_getEnv_1006_ = lean_ctor_get(v_inst_1001_, 0);
lean_inc(v_getEnv_1006_);
v_modifyEnv_1007_ = lean_ctor_get(v_inst_1001_, 1);
lean_inc(v_modifyEnv_1007_);
lean_dec_ref(v_inst_1001_);
v___x_1008_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1009_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___x_1010_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_setStructureParents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1011_, 0, v___x_1010_);
lean_closure_set(v___f_1011_, 1, v___x_1008_);
lean_closure_set(v___f_1011_, 2, v___x_1009_);
lean_closure_set(v___f_1011_, 3, v_structName_1003_);
lean_closure_set(v___f_1011_, 4, v_parentInfo_1004_);
lean_closure_set(v___f_1011_, 5, v_modifyEnv_1007_);
lean_closure_set(v___f_1011_, 6, v_inst_1000_);
lean_closure_set(v___f_1011_, 7, v_inst_1002_);
v___x_1012_ = lean_apply_4(v_toBind_1005_, lean_box(0), lean_box(0), v_getEnv_1006_, v___f_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_setStructureParents(lean_object* v_m_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_structName_1017_, lean_object* v_parentInfo_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_setStructureParents___redArg(v_inst_1014_, v_inst_1015_, v_inst_1016_, v_structName_1017_, v_parentInfo_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(lean_object* v_as_1020_, lean_object* v_k_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_m_1026_; lean_object* v_a_1027_; uint8_t v___x_1028_; 
v___x_1024_ = lean_nat_add(v_x_1022_, v_x_1023_);
v___x_1025_ = lean_unsigned_to_nat(1u);
v_m_1026_ = lean_nat_shiftr(v___x_1024_, v___x_1025_);
lean_dec(v___x_1024_);
v_a_1027_ = lean_array_fget_borrowed(v_as_1020_, v_m_1026_);
v___x_1028_ = l_Lean_StructureInfo_lt(v_a_1027_, v_k_1021_);
if (v___x_1028_ == 0)
{
uint8_t v___x_1029_; 
lean_dec(v_x_1023_);
v___x_1029_ = l_Lean_StructureInfo_lt(v_k_1021_, v_a_1027_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
lean_dec(v_m_1026_);
lean_dec(v_x_1022_);
lean_inc(v_a_1027_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_a_1027_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_nat_dec_eq(v_m_1026_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = lean_nat_sub(v_m_1026_, v___x_1025_);
lean_dec(v_m_1026_);
v___x_1034_ = lean_nat_dec_lt(v___x_1033_, v_x_1022_);
if (v___x_1034_ == 0)
{
v_x_1023_ = v___x_1033_;
goto _start;
}
else
{
lean_object* v___x_1036_; 
lean_dec(v___x_1033_);
lean_dec(v_x_1022_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
}
else
{
lean_object* v___x_1037_; 
lean_dec(v_m_1026_);
lean_dec(v_x_1022_);
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
}
}
else
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
lean_dec(v_x_1022_);
v___x_1038_ = lean_nat_add(v_m_1026_, v___x_1025_);
lean_dec(v_m_1026_);
v___x_1039_ = lean_nat_dec_le(v___x_1038_, v_x_1023_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v___x_1038_);
lean_dec(v_x_1023_);
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
else
{
v_x_1022_ = v___x_1038_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg___boxed(lean_object* v_as_1042_, lean_object* v_k_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1042_, v_k_1043_, v_x_1044_, v_x_1045_);
lean_dec_ref(v_k_1043_);
lean_dec_ref(v_as_1042_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1047_, lean_object* v_vals_1048_, lean_object* v_i_1049_, lean_object* v_k_1050_){
_start:
{
lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = lean_array_get_size(v_keys_1047_);
v___x_1052_ = lean_nat_dec_lt(v_i_1049_, v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec(v_i_1049_);
v___x_1053_ = lean_box(0);
return v___x_1053_;
}
else
{
lean_object* v_k_x27_1054_; uint8_t v___x_1055_; 
v_k_x27_1054_ = lean_array_fget_borrowed(v_keys_1047_, v_i_1049_);
v___x_1055_ = lean_name_eq(v_k_1050_, v_k_x27_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(1u);
v___x_1057_ = lean_nat_add(v_i_1049_, v___x_1056_);
lean_dec(v_i_1049_);
v_i_1049_ = v___x_1057_;
goto _start;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_array_fget_borrowed(v_vals_1048_, v_i_1049_);
lean_dec(v_i_1049_);
lean_inc(v___x_1059_);
v___x_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1061_, lean_object* v_vals_1062_, lean_object* v_i_1063_, lean_object* v_k_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1061_, v_vals_1062_, v_i_1063_, v_k_1064_);
lean_dec(v_k_1064_);
lean_dec_ref(v_vals_1062_);
lean_dec_ref(v_keys_1061_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(lean_object* v_x_1066_, size_t v_x_1067_, lean_object* v_x_1068_){
_start:
{
if (lean_obj_tag(v_x_1066_) == 0)
{
lean_object* v_es_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1090_; 
v_es_1069_ = lean_ctor_get(v_x_1066_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_x_1066_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1071_ = v_x_1066_;
v_isShared_1072_ = v_isSharedCheck_1090_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_es_1069_);
lean_dec(v_x_1066_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1090_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; size_t v___x_1076_; lean_object* v_j_1077_; lean_object* v___x_1078_; 
v___x_1073_ = lean_box(2);
v___x_1074_ = ((size_t)5ULL);
v___x_1075_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4___redArg___closed__1);
v___x_1076_ = lean_usize_land(v_x_1067_, v___x_1075_);
v_j_1077_ = lean_usize_to_nat(v___x_1076_);
v___x_1078_ = lean_array_get(v___x_1073_, v_es_1069_, v_j_1077_);
lean_dec(v_j_1077_);
lean_dec_ref(v_es_1069_);
switch(lean_obj_tag(v___x_1078_))
{
case 0:
{
lean_object* v_key_1079_; lean_object* v_val_1080_; uint8_t v___x_1081_; 
v_key_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_key_1079_);
v_val_1080_ = lean_ctor_get(v___x_1078_, 1);
lean_inc(v_val_1080_);
lean_dec_ref(v___x_1078_);
v___x_1081_ = lean_name_eq(v_x_1068_, v_key_1079_);
lean_dec(v_key_1079_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec(v_val_1080_);
lean_del_object(v___x_1071_);
v___x_1082_ = lean_box(0);
return v___x_1082_;
}
else
{
lean_object* v___x_1084_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 1);
lean_ctor_set(v___x_1071_, 0, v_val_1080_);
v___x_1084_ = v___x_1071_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_val_1080_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
case 1:
{
lean_object* v_node_1086_; size_t v___x_1087_; 
lean_del_object(v___x_1071_);
v_node_1086_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_node_1086_);
lean_dec_ref(v___x_1078_);
v___x_1087_ = lean_usize_shift_right(v_x_1067_, v___x_1074_);
v_x_1066_ = v_node_1086_;
v_x_1067_ = v___x_1087_;
goto _start;
}
default: 
{
lean_object* v___x_1089_; 
lean_del_object(v___x_1071_);
v___x_1089_ = lean_box(0);
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_ks_1091_; lean_object* v_vs_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_ks_1091_ = lean_ctor_get(v_x_1066_, 0);
lean_inc_ref(v_ks_1091_);
v_vs_1092_ = lean_ctor_get(v_x_1066_, 1);
lean_inc_ref(v_vs_1092_);
lean_dec_ref(v_x_1066_);
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1091_, v_vs_1092_, v___x_1093_, v_x_1068_);
lean_dec_ref(v_vs_1092_);
lean_dec_ref(v_ks_1091_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
size_t v_x_395__boxed_1098_; lean_object* v_res_1099_; 
v_x_395__boxed_1098_ = lean_unbox_usize(v_x_1096_);
lean_dec(v_x_1096_);
v_res_1099_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1095_, v_x_395__boxed_1098_, v_x_1097_);
lean_dec(v_x_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
uint64_t v___y_1103_; 
if (lean_obj_tag(v_x_1101_) == 0)
{
uint64_t v___x_1106_; 
v___x_1106_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2__spec__3_spec__4_spec__7___redArg___closed__0);
v___y_1103_ = v___x_1106_;
goto v___jp_1102_;
}
else
{
uint64_t v_hash_1107_; 
v_hash_1107_ = lean_ctor_get_uint64(v_x_1101_, sizeof(void*)*2);
v___y_1103_ = v_hash_1107_;
goto v___jp_1102_;
}
v___jp_1102_:
{
size_t v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_uint64_to_usize(v___y_1103_);
v___x_1105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1100_, v___x_1104_, v_x_1101_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg___boxed(lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1108_, v_x_1109_);
lean_dec(v_x_1109_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo_x3f(lean_object* v_env_1113_, lean_object* v_structName_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_obj_once(&l_Lean_setStructureParents___redArg___closed__2, &l_Lean_setStructureParents___redArg___closed__2_once, _init_l_Lean_setStructureParents___redArg___closed__2);
v___x_1116_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1113_, v_structName_1114_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1117_; lean_object* v_toEnvExtension_1118_; lean_object* v_asyncMode_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_snd_1122_; lean_object* v___x_1123_; 
v___x_1117_ = l___private_Lean_Structure_0__Lean_structureExt;
v_toEnvExtension_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc_ref(v_toEnvExtension_1118_);
v_asyncMode_1119_ = lean_ctor_get(v_toEnvExtension_1118_, 2);
lean_inc(v_asyncMode_1119_);
lean_dec_ref(v_toEnvExtension_1118_);
v___x_1120_ = lean_box(0);
v___x_1121_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1115_, v___x_1117_, v_env_1113_, v_asyncMode_1119_, v___x_1120_);
lean_dec(v_asyncMode_1119_);
v_snd_1122_ = lean_ctor_get(v___x_1121_, 1);
lean_inc(v_snd_1122_);
lean_dec(v___x_1121_);
v___x_1123_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_snd_1122_, v_structName_1114_);
lean_dec(v_structName_1114_);
return v___x_1123_;
}
else
{
lean_object* v_val_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_val_1124_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_val_1124_);
lean_dec_ref(v___x_1116_);
v___x_1125_ = l___private_Lean_Structure_0__Lean_structureExt;
v___x_1126_ = 0;
v___x_1127_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1115_, v___x_1125_, v_env_1113_, v_val_1124_, v___x_1126_);
lean_dec(v_val_1124_);
lean_dec_ref(v_env_1113_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_array_get_size(v___x_1127_);
v___x_1130_ = lean_nat_dec_lt(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v___x_1127_);
lean_dec(v_structName_1114_);
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_sub(v___x_1129_, v___x_1132_);
v___x_1134_ = lean_nat_dec_le(v___x_1128_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec(v___x_1133_);
lean_dec_ref(v___x_1127_);
lean_dec(v_structName_1114_);
v___x_1135_ = lean_box(0);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = ((lean_object*)(l_Lean_getStructureInfo_x3f___closed__0));
v___x_1137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1137_, 0, v_structName_1114_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
lean_ctor_set(v___x_1137_, 3, v___x_1136_);
v___x_1138_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v___x_1127_, v___x_1137_, v___x_1128_, v___x_1133_);
lean_dec_ref(v___x_1137_);
lean_dec_ref(v___x_1127_);
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v_x_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___boxed(lean_object* v_00_u03b2_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0(v_00_u03b2_1143_, v_x_1144_, v_x_1145_);
lean_dec(v_x_1145_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(lean_object* v_as_1147_, lean_object* v_k_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___redArg(v_as_1147_, v_k_1148_, v_x_1149_, v_x_1150_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1___boxed(lean_object* v_as_1153_, lean_object* v_k_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Array_binSearchAux___at___00Lean_getStructureInfo_x3f_spec__1(v_as_1153_, v_k_1154_, v_x_1155_, v_x_1156_, v_x_1157_);
lean_dec_ref(v_k_1154_);
lean_dec_ref(v_as_1153_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1159_, lean_object* v_x_1160_, size_t v_x_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___redArg(v_x_1160_, v_x_1161_, v_x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
size_t v_x_545__boxed_1168_; lean_object* v_res_1169_; 
v_x_545__boxed_1168_ = lean_unbox_usize(v_x_1166_);
lean_dec(v_x_1166_);
v_res_1169_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0(v_00_u03b2_1164_, v_x_1165_, v_x_545__boxed_1168_, v_x_1167_);
lean_dec(v_x_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1170_, lean_object* v_keys_1171_, lean_object* v_vals_1172_, lean_object* v_heq_1173_, lean_object* v_i_1174_, lean_object* v_k_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1171_, v_vals_1172_, v_i_1174_, v_k_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1177_, lean_object* v_keys_1178_, lean_object* v_vals_1179_, lean_object* v_heq_1180_, lean_object* v_i_1181_, lean_object* v_k_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1177_, v_keys_1178_, v_vals_1179_, v_heq_1180_, v_i_1181_, v_k_1182_);
lean_dec(v_k_1182_);
lean_dec_ref(v_vals_1179_);
lean_dec_ref(v_keys_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureInfo_spec__0(lean_object* v_msg_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = l_Lean_instInhabitedStructureInfo_default;
v___x_1186_ = lean_panic_fn_borrowed(v___x_1185_, v_msg_1184_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_getStructureInfo___closed__3(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1190_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1191_ = lean_unsigned_to_nat(4u);
v___x_1192_ = lean_unsigned_to_nat(139u);
v___x_1193_ = ((lean_object*)(l_Lean_getStructureInfo___closed__1));
v___x_1194_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1195_ = l_mkPanicMessageWithDecl(v___x_1194_, v___x_1193_, v___x_1192_, v___x_1191_, v___x_1190_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureInfo(lean_object* v_env_1196_, lean_object* v_structName_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_getStructureInfo_x3f(v_env_1196_, v_structName_1197_);
if (lean_obj_tag(v___x_1198_) == 1)
{
lean_object* v_val_1199_; 
v_val_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_val_1199_);
lean_dec_ref(v___x_1198_);
return v_val_1199_;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec(v___x_1198_);
v___x_1200_ = lean_obj_once(&l_Lean_getStructureInfo___closed__3, &l_Lean_getStructureInfo___closed__3_once, _init_l_Lean_getStructureInfo___closed__3);
v___x_1201_ = l_panic___at___00Lean_getStructureInfo_spec__0(v___x_1200_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getStructureCtor_spec__0(lean_object* v_msg_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = l_Lean_instInhabitedConstructorVal_default;
v___x_1204_ = lean_panic_fn_borrowed(v___x_1203_, v_msg_1202_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__1(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = ((lean_object*)(l_Lean_getStructureInfo___closed__2));
v___x_1207_ = lean_unsigned_to_nat(9u);
v___x_1208_ = lean_unsigned_to_nat(154u);
v___x_1209_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1210_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1211_ = l_mkPanicMessageWithDecl(v___x_1210_, v___x_1209_, v___x_1208_, v___x_1207_, v___x_1206_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_getStructureCtor___closed__3(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1213_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1214_ = lean_unsigned_to_nat(11u);
v___x_1215_ = lean_unsigned_to_nat(153u);
v___x_1216_ = ((lean_object*)(l_Lean_getStructureCtor___closed__0));
v___x_1217_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1218_ = l_mkPanicMessageWithDecl(v___x_1217_, v___x_1216_, v___x_1215_, v___x_1214_, v___x_1213_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureCtor(lean_object* v_env_1219_, lean_object* v_constName_1220_){
_start:
{
uint8_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = 0;
lean_inc_ref(v_env_1219_);
v___x_1228_ = l_Lean_Environment_find_x3f(v_env_1219_, v_constName_1220_, v___x_1227_);
if (lean_obj_tag(v___x_1228_) == 1)
{
lean_object* v_val_1229_; 
v_val_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1229_);
lean_dec_ref(v___x_1228_);
if (lean_obj_tag(v_val_1229_) == 5)
{
lean_object* v_val_1230_; lean_object* v_ctors_1231_; 
v_val_1230_ = lean_ctor_get(v_val_1229_, 0);
lean_inc_ref(v_val_1230_);
lean_dec_ref(v_val_1229_);
v_ctors_1231_ = lean_ctor_get(v_val_1230_, 4);
lean_inc(v_ctors_1231_);
lean_dec_ref(v_val_1230_);
if (lean_obj_tag(v_ctors_1231_) == 1)
{
lean_object* v_tail_1232_; 
v_tail_1232_ = lean_ctor_get(v_ctors_1231_, 1);
if (lean_obj_tag(v_tail_1232_) == 0)
{
lean_object* v_head_1233_; lean_object* v___x_1234_; 
v_head_1233_ = lean_ctor_get(v_ctors_1231_, 0);
lean_inc(v_head_1233_);
lean_dec_ref(v_ctors_1231_);
v___x_1234_ = l_Lean_Environment_find_x3f(v_env_1219_, v_head_1233_, v___x_1227_);
if (lean_obj_tag(v___x_1234_) == 1)
{
lean_object* v_val_1235_; 
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref(v___x_1234_);
if (lean_obj_tag(v_val_1235_) == 6)
{
lean_object* v_val_1236_; 
v_val_1236_ = lean_ctor_get(v_val_1235_, 0);
lean_inc_ref(v_val_1236_);
lean_dec_ref(v_val_1235_);
return v_val_1236_;
}
else
{
lean_dec(v_val_1235_);
goto v___jp_1224_;
}
}
else
{
lean_dec(v___x_1234_);
goto v___jp_1224_;
}
}
else
{
lean_dec_ref(v_ctors_1231_);
lean_dec_ref(v_env_1219_);
goto v___jp_1221_;
}
}
else
{
lean_dec(v_ctors_1231_);
lean_dec_ref(v_env_1219_);
goto v___jp_1221_;
}
}
else
{
lean_dec(v_val_1229_);
lean_dec_ref(v_env_1219_);
goto v___jp_1221_;
}
}
else
{
lean_dec(v___x_1228_);
lean_dec_ref(v_env_1219_);
goto v___jp_1221_;
}
v___jp_1221_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = lean_obj_once(&l_Lean_getStructureCtor___closed__1, &l_Lean_getStructureCtor___closed__1_once, _init_l_Lean_getStructureCtor___closed__1);
v___x_1223_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1222_);
return v___x_1223_;
}
v___jp_1224_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_obj_once(&l_Lean_getStructureCtor___closed__3, &l_Lean_getStructureCtor___closed__3_once, _init_l_Lean_getStructureCtor___closed__3);
v___x_1226_ = l_panic___at___00Lean_getStructureCtor_spec__0(v___x_1225_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFields(lean_object* v_env_1237_, lean_object* v_structName_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v_fieldNames_1240_; 
v___x_1239_ = l_Lean_getStructureInfo(v_env_1237_, v_structName_1238_);
v_fieldNames_1240_ = lean_ctor_get(v___x_1239_, 1);
lean_inc_ref(v_fieldNames_1240_);
lean_dec_ref(v___x_1239_);
return v_fieldNames_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_getFieldInfo_x3f(lean_object* v_env_1241_, lean_object* v_structName_1242_, lean_object* v_fieldName_1243_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_getStructureInfo_x3f(v_env_1241_, v_structName_1242_);
if (lean_obj_tag(v___x_1244_) == 1)
{
lean_object* v_val_1245_; lean_object* v_fieldInfo_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_val_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_val_1245_);
lean_dec_ref(v___x_1244_);
v_fieldInfo_1246_ = lean_ctor_get(v_val_1245_, 2);
lean_inc_ref(v_fieldInfo_1246_);
lean_dec(v_val_1245_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_array_get_size(v_fieldInfo_1246_);
v___x_1249_ = lean_nat_dec_lt(v___x_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; 
lean_dec_ref(v_fieldInfo_1246_);
lean_dec(v_fieldName_1243_);
v___x_1250_ = lean_box(0);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1251_ = lean_unsigned_to_nat(1u);
v___x_1252_ = lean_nat_sub(v___x_1248_, v___x_1251_);
v___x_1253_ = lean_nat_dec_le(v___x_1247_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
lean_dec(v___x_1252_);
lean_dec_ref(v_fieldInfo_1246_);
lean_dec(v_fieldName_1243_);
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_box(0);
v___x_1257_ = 0;
v___x_1258_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1258_, 0, v_fieldName_1243_);
lean_ctor_set(v___x_1258_, 1, v___x_1255_);
lean_ctor_set(v___x_1258_, 2, v___x_1256_);
lean_ctor_set(v___x_1258_, 3, v___x_1256_);
lean_ctor_set_uint8(v___x_1258_, sizeof(void*)*4, v___x_1257_);
v___x_1259_ = l_Array_binSearchAux___at___00Lean_StructureInfo_getProjFn_x3f_spec__0___redArg(v_fieldInfo_1246_, v___x_1258_, v___x_1247_, v___x_1252_);
lean_dec_ref(v___x_1258_);
lean_dec_ref(v_fieldInfo_1246_);
return v___x_1259_;
}
}
}
else
{
lean_object* v___x_1260_; 
lean_dec(v___x_1244_);
lean_dec(v_fieldName_1243_);
v___x_1260_ = lean_box(0);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubobjectField_x3f(lean_object* v_env_1261_, lean_object* v_structName_1262_, lean_object* v_fieldName_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_getFieldInfo_x3f(v_env_1261_, v_structName_1262_, v_fieldName_1263_);
if (lean_obj_tag(v___x_1264_) == 1)
{
lean_object* v_val_1265_; lean_object* v_subobject_x3f_1266_; 
v_val_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1265_);
lean_dec_ref(v___x_1264_);
v_subobject_x3f_1266_ = lean_ctor_get(v_val_1265_, 2);
lean_inc(v_subobject_x3f_1266_);
lean_dec(v_val_1265_);
return v_subobject_x3f_1266_;
}
else
{
lean_object* v___x_1267_; 
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureParentInfo(lean_object* v_env_1268_, lean_object* v_structName_1269_){
_start:
{
lean_object* v___x_1270_; lean_object* v_parentInfo_1271_; 
v___x_1270_ = l_Lean_getStructureInfo(v_env_1268_, v_structName_1269_);
v_parentInfo_1271_ = lean_ctor_get(v___x_1270_, 3);
lean_inc_ref(v_parentInfo_1271_);
lean_dec_ref(v___x_1270_);
return v_parentInfo_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(lean_object* v_env_1272_, lean_object* v_structName_1273_, lean_object* v_as_1274_, size_t v_i_1275_, size_t v_stop_1276_, lean_object* v_b_1277_){
_start:
{
lean_object* v___y_1279_; uint8_t v___x_1283_; 
v___x_1283_ = lean_usize_dec_eq(v_i_1275_, v_stop_1276_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_array_uget_borrowed(v_as_1274_, v_i_1275_);
lean_inc(v___x_1284_);
lean_inc(v_structName_1273_);
lean_inc_ref(v_env_1272_);
v___x_1285_ = l_Lean_isSubobjectField_x3f(v_env_1272_, v_structName_1273_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
v___y_1279_ = v_b_1277_;
goto v___jp_1278_;
}
else
{
lean_object* v_val_1286_; lean_object* v___x_1287_; 
v_val_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_val_1286_);
lean_dec_ref(v___x_1285_);
v___x_1287_ = lean_array_push(v_b_1277_, v_val_1286_);
v___y_1279_ = v___x_1287_;
goto v___jp_1278_;
}
}
else
{
lean_dec(v_structName_1273_);
lean_dec_ref(v_env_1272_);
return v_b_1277_;
}
v___jp_1278_:
{
size_t v___x_1280_; size_t v___x_1281_; 
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1275_, v___x_1280_);
v_i_1275_ = v___x_1281_;
v_b_1277_ = v___y_1279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0___boxed(lean_object* v_env_1288_, lean_object* v_structName_1289_, lean_object* v_as_1290_, lean_object* v_i_1291_, lean_object* v_stop_1292_, lean_object* v_b_1293_){
_start:
{
size_t v_i_boxed_1294_; size_t v_stop_boxed_1295_; lean_object* v_res_1296_; 
v_i_boxed_1294_ = lean_unbox_usize(v_i_1291_);
lean_dec(v_i_1291_);
v_stop_boxed_1295_ = lean_unbox_usize(v_stop_1292_);
lean_dec(v_stop_1292_);
v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1288_, v_structName_1289_, v_as_1290_, v_i_boxed_1294_, v_stop_boxed_1295_, v_b_1293_);
lean_dec_ref(v_as_1290_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(lean_object* v_env_1297_, lean_object* v_structName_1298_, lean_object* v_as_1299_, lean_object* v_start_1300_, lean_object* v_stop_1301_){
_start:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_getStructureInfo_x3f___closed__0));
v___x_1303_ = lean_nat_dec_lt(v_start_1300_, v_stop_1301_);
if (v___x_1303_ == 0)
{
lean_dec(v_structName_1298_);
lean_dec_ref(v_env_1297_);
return v___x_1302_;
}
else
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_array_get_size(v_as_1299_);
v___x_1305_ = lean_nat_dec_le(v_stop_1301_, v___x_1304_);
if (v___x_1305_ == 0)
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_nat_dec_lt(v_start_1300_, v___x_1304_);
if (v___x_1306_ == 0)
{
lean_dec(v_structName_1298_);
lean_dec_ref(v_env_1297_);
return v___x_1302_;
}
else
{
size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_usize_of_nat(v_start_1300_);
v___x_1308_ = lean_usize_of_nat(v___x_1304_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1297_, v_structName_1298_, v_as_1299_, v___x_1307_, v___x_1308_, v___x_1302_);
return v___x_1309_;
}
}
else
{
size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_usize_of_nat(v_start_1300_);
v___x_1311_ = lean_usize_of_nat(v_stop_1301_);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0_spec__0(v_env_1297_, v_structName_1298_, v_as_1299_, v___x_1310_, v___x_1311_, v___x_1302_);
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0___boxed(lean_object* v_env_1313_, lean_object* v_structName_1314_, lean_object* v_as_1315_, lean_object* v_start_1316_, lean_object* v_stop_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1313_, v_structName_1314_, v_as_1315_, v_start_1316_, v_stop_1317_);
lean_dec(v_stop_1317_);
lean_dec(v_start_1316_);
lean_dec_ref(v_as_1315_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureSubobjects(lean_object* v_env_1319_, lean_object* v_structName_1320_){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_inc(v_structName_1320_);
lean_inc_ref(v_env_1319_);
v___x_1321_ = l_Lean_getStructureFields(v_env_1319_, v_structName_1320_);
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_array_get_size(v___x_1321_);
v___x_1324_ = l_Array_filterMapM___at___00Lean_getStructureSubobjects_spec__0(v_env_1319_, v_structName_1320_, v___x_1321_, v___x_1322_, v___x_1323_);
lean_dec_ref(v___x_1321_);
return v___x_1324_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(lean_object* v_a_1325_, lean_object* v_as_1326_, size_t v_i_1327_, size_t v_stop_1328_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_usize_dec_eq(v_i_1327_, v_stop_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_array_uget_borrowed(v_as_1326_, v_i_1327_);
v___x_1331_ = lean_name_eq(v_a_1325_, v___x_1330_);
if (v___x_1331_ == 0)
{
size_t v___x_1332_; size_t v___x_1333_; 
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_add(v_i_1327_, v___x_1332_);
v_i_1327_ = v___x_1333_;
goto _start;
}
else
{
return v___x_1331_;
}
}
else
{
uint8_t v___x_1335_; 
v___x_1335_ = 0;
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0___boxed(lean_object* v_a_1336_, lean_object* v_as_1337_, lean_object* v_i_1338_, lean_object* v_stop_1339_){
_start:
{
size_t v_i_boxed_1340_; size_t v_stop_boxed_1341_; uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_i_boxed_1340_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_stop_boxed_1341_ = lean_unbox_usize(v_stop_1339_);
lean_dec(v_stop_1339_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1336_, v_as_1337_, v_i_boxed_1340_, v_stop_boxed_1341_);
lean_dec_ref(v_as_1337_);
lean_dec(v_a_1336_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_findField_x3f_spec__0(lean_object* v_as_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_array_get_size(v_as_1344_);
v___x_1348_ = lean_nat_dec_lt(v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
return v___x_1348_;
}
else
{
if (v___x_1348_ == 0)
{
return v___x_1348_;
}
else
{
size_t v___x_1349_; size_t v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1347_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_findField_x3f_spec__0_spec__0(v_a_1345_, v_as_1344_, v___x_1349_, v___x_1350_);
return v___x_1351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_findField_x3f_spec__0___boxed(lean_object* v_as_1352_, lean_object* v_a_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v_as_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_as_1352_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f(lean_object* v_env_1359_, lean_object* v_structName_1360_, lean_object* v_fieldName_1361_){
_start:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
lean_inc(v_structName_1360_);
lean_inc_ref(v_env_1359_);
v___x_1362_ = l_Lean_getStructureFields(v_env_1359_, v_structName_1360_);
v___x_1363_ = l_Array_contains___at___00Lean_findField_x3f_spec__0(v___x_1362_, v_fieldName_1361_);
lean_dec_ref(v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; size_t v_sz_1367_; size_t v___x_1368_; lean_object* v___x_1369_; lean_object* v_fst_1370_; 
lean_inc_ref(v_env_1359_);
v___x_1364_ = l_Lean_getStructureSubobjects(v_env_1359_, v_structName_1360_);
v___x_1365_ = lean_box(0);
v___x_1366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1367_ = lean_array_size(v___x_1364_);
v___x_1368_ = ((size_t)0ULL);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1359_, v_fieldName_1361_, v___x_1364_, v_sz_1367_, v___x_1368_, v___x_1366_);
lean_dec_ref(v___x_1364_);
v_fst_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_fst_1370_);
lean_dec_ref(v___x_1369_);
if (lean_obj_tag(v_fst_1370_) == 0)
{
return v___x_1365_;
}
else
{
lean_object* v_val_1371_; 
v_val_1371_ = lean_ctor_get(v_fst_1370_, 0);
lean_inc(v_val_1371_);
lean_dec_ref(v_fst_1370_);
return v_val_1371_;
}
}
else
{
lean_object* v___x_1372_; 
lean_dec_ref(v_env_1359_);
v___x_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_structName_1360_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(lean_object* v_env_1373_, lean_object* v_fieldName_1374_, lean_object* v_as_1375_, size_t v_sz_1376_, size_t v_i_1377_, lean_object* v_b_1378_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_usize_dec_lt(v_i_1377_, v_sz_1376_);
if (v___x_1379_ == 0)
{
lean_dec_ref(v_env_1373_);
lean_inc_ref(v_b_1378_);
return v_b_1378_;
}
else
{
lean_object* v___x_1380_; lean_object* v_a_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_box(0);
v_a_1381_ = lean_array_uget_borrowed(v_as_1375_, v_i_1377_);
lean_inc(v_a_1381_);
lean_inc_ref(v_env_1373_);
v___x_1382_ = l_Lean_findField_x3f(v_env_1373_, v_a_1381_, v_fieldName_1374_);
if (lean_obj_tag(v___x_1382_) == 1)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec_ref(v_env_1373_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___x_1380_);
return v___x_1384_;
}
else
{
lean_object* v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v___x_1382_);
v___x_1385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_add(v_i_1377_, v___x_1386_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1373_, v_fieldName_1374_, v_as_1375_, v_sz_1376_, v___x_1387_, v___x_1385_);
return v___x_1388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___boxed(lean_object* v_env_1389_, lean_object* v_fieldName_1390_, lean_object* v_as_1391_, lean_object* v_sz_1392_, lean_object* v_i_1393_, lean_object* v_b_1394_){
_start:
{
size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1392_);
lean_dec(v_sz_1392_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1393_);
lean_dec(v_i_1393_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1(v_env_1389_, v_fieldName_1390_, v_as_1391_, v_sz_boxed_1395_, v_i_boxed_1396_, v_b_1394_);
lean_dec_ref(v_b_1394_);
lean_dec_ref(v_as_1391_);
lean_dec(v_fieldName_1390_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_findField_x3f___boxed(lean_object* v_env_1398_, lean_object* v_structName_1399_, lean_object* v_fieldName_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_findField_x3f(v_env_1398_, v_structName_1399_, v_fieldName_1400_);
lean_dec(v_fieldName_1400_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(lean_object* v_projName_1405_, lean_object* v_as_1406_, size_t v_sz_1407_, size_t v_i_1408_, lean_object* v_b_1409_){
_start:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_usize_dec_lt(v_i_1408_, v_sz_1407_);
if (v___x_1410_ == 0)
{
lean_inc_ref(v_b_1409_);
return v_b_1409_;
}
else
{
lean_object* v_a_1411_; lean_object* v_projFn_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_a_1411_ = lean_array_uget_borrowed(v_as_1406_, v_i_1408_);
v_projFn_1412_ = lean_ctor_get(v_a_1411_, 1);
v___x_1413_ = lean_box(0);
v___x_1414_ = l_Lean_Name_isSuffixOf(v_projName_1405_, v_projFn_1412_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1415_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_add(v_i_1408_, v___x_1416_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1405_, v_as_1406_, v_sz_1407_, v___x_1417_, v___x_1415_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_inc(v_a_1411_);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_a_1411_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
lean_ctor_set(v___x_1421_, 1, v___x_1413_);
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___boxed(lean_object* v_projName_1422_, lean_object* v_as_1423_, lean_object* v_sz_1424_, lean_object* v_i_1425_, lean_object* v_b_1426_){
_start:
{
size_t v_sz_boxed_1427_; size_t v_i_boxed_1428_; lean_object* v_res_1429_; 
v_sz_boxed_1427_ = lean_unbox_usize(v_sz_1424_);
lean_dec(v_sz_1424_);
v_i_boxed_1428_ = lean_unbox_usize(v_i_1425_);
lean_dec(v_i_1425_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1422_, v_as_1423_, v_sz_boxed_1427_, v_i_boxed_1428_, v_b_1426_);
lean_dec_ref(v_b_1426_);
lean_dec_ref(v_as_1423_);
lean_dec(v_projName_1422_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(lean_object* v_env_1430_, lean_object* v_projName_1431_, lean_object* v_structName_1432_, lean_object* v_a_1433_){
_start:
{
uint8_t v___x_1434_; 
v___x_1434_ = l_Lean_NameSet_contains(v_a_1433_, v_structName_1432_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1459_; size_t v_sz_1460_; size_t v___x_1461_; lean_object* v___x_1462_; lean_object* v_fst_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1480_; 
lean_inc(v_structName_1432_);
lean_inc_ref(v_env_1430_);
v___x_1435_ = l_Lean_getStructureParentInfo(v_env_1430_, v_structName_1432_);
v___x_1459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1___closed__0));
v_sz_1460_ = lean_array_size(v___x_1435_);
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__1(v_projName_1431_, v___x_1435_, v_sz_1460_, v___x_1461_, v___x_1459_);
v_fst_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v___x_1462_, 1);
lean_dec(v_unused_1481_);
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1480_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_fst_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1480_;
goto v_resetjp_1464_;
}
v___jp_1436_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; size_t v_sz_1440_; size_t v___x_1441_; lean_object* v___x_1442_; lean_object* v_fst_1443_; lean_object* v_fst_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1457_; 
v___x_1437_ = l_Lean_NameSet_insert(v_a_1433_, v_structName_1432_);
v___x_1438_ = lean_box(0);
v___x_1439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v_sz_1440_ = lean_array_size(v___x_1435_);
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1430_, v_projName_1431_, v___x_1435_, v_sz_1440_, v___x_1441_, v___x_1439_, v___x_1437_);
lean_dec_ref(v___x_1435_);
v_fst_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_fst_1443_);
v_fst_1444_ = lean_ctor_get(v_fst_1443_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_fst_1443_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_fst_1443_, 1);
lean_dec(v_unused_1458_);
v___x_1446_ = v_fst_1443_;
v_isShared_1447_ = v_isSharedCheck_1457_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_fst_1444_);
lean_dec(v_fst_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1457_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
if (lean_obj_tag(v_fst_1444_) == 0)
{
lean_object* v_snd_1448_; lean_object* v___x_1450_; 
v_snd_1448_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_snd_1448_);
lean_dec_ref(v___x_1442_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v_snd_1448_);
lean_ctor_set(v___x_1446_, 0, v___x_1438_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_snd_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
else
{
lean_object* v_snd_1452_; lean_object* v_val_1453_; lean_object* v___x_1455_; 
v_snd_1452_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_snd_1452_);
lean_dec_ref(v___x_1442_);
v_val_1453_ = lean_ctor_get(v_fst_1444_, 0);
lean_inc(v_val_1453_);
lean_dec_ref(v_fst_1444_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v_snd_1452_);
lean_ctor_set(v___x_1446_, 0, v_val_1453_);
v___x_1455_ = v___x_1446_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_val_1453_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_snd_1452_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
v_resetjp_1464_:
{
if (lean_obj_tag(v_fst_1463_) == 0)
{
lean_del_object(v___x_1465_);
goto v___jp_1436_;
}
else
{
lean_object* v_val_1467_; 
v_val_1467_ = lean_ctor_get(v_fst_1463_, 0);
lean_inc(v_val_1467_);
lean_dec_ref(v_fst_1463_);
if (lean_obj_tag(v_val_1467_) == 1)
{
lean_object* v_val_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v___x_1435_);
lean_dec(v_structName_1432_);
lean_dec_ref(v_env_1430_);
v_val_1468_ = lean_ctor_get(v_val_1467_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_val_1467_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1470_ = v_val_1467_;
v_isShared_1471_ = v_isSharedCheck_1479_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_val_1468_);
lean_dec(v_val_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1479_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v_structName_1472_; lean_object* v___x_1474_; 
v_structName_1472_ = lean_ctor_get(v_val_1468_, 0);
lean_inc(v_structName_1472_);
lean_dec(v_val_1468_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_structName_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_structName_1472_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v_a_1433_);
lean_ctor_set(v___x_1465_, 0, v___x_1474_);
v___x_1476_ = v___x_1465_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_a_1433_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_dec(v_val_1467_);
lean_del_object(v___x_1465_);
goto v___jp_1436_;
}
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v_structName_1432_);
lean_dec_ref(v_env_1430_);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v_a_1433_);
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(lean_object* v_env_1484_, lean_object* v_projName_1485_, lean_object* v_as_1486_, size_t v_sz_1487_, size_t v_i_1488_, lean_object* v_b_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_usize_dec_lt(v_i_1488_, v_sz_1487_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
lean_dec_ref(v_env_1484_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_b_1489_);
lean_ctor_set(v___x_1492_, 1, v___y_1490_);
return v___x_1492_;
}
else
{
lean_object* v_a_1493_; lean_object* v_structName_1494_; lean_object* v___x_1495_; lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref(v_b_1489_);
v_a_1493_ = lean_array_uget_borrowed(v_as_1486_, v_i_1488_);
v_structName_1494_ = lean_ctor_get(v_a_1493_, 0);
lean_inc(v_structName_1494_);
lean_inc_ref(v_env_1484_);
v___x_1495_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1484_, v_projName_1485_, v_structName_1494_, v___y_1490_);
v_fst_1496_ = lean_ctor_get(v___x_1495_, 0);
v_snd_1497_ = lean_ctor_get(v___x_1495_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1499_ = v___x_1495_;
v_isShared_1500_ = v_isSharedCheck_1511_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snd_1497_);
lean_inc(v_fst_1496_);
lean_dec(v___x_1495_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1511_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_box(0);
if (lean_obj_tag(v_fst_1496_) == 1)
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
lean_dec_ref(v_env_1484_);
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_fst_1496_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v___x_1501_);
lean_ctor_set(v___x_1499_, 0, v___x_1502_);
v___x_1504_ = v___x_1499_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1501_);
v___x_1504_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v_snd_1497_);
return v___x_1505_;
}
}
else
{
lean_object* v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; 
lean_del_object(v___x_1499_);
lean_dec(v_fst_1496_);
v___x_1507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_findField_x3f_spec__1___closed__0));
v___x_1508_ = ((size_t)1ULL);
v___x_1509_ = lean_usize_add(v_i_1488_, v___x_1508_);
v_i_1488_ = v___x_1509_;
v_b_1489_ = v___x_1507_;
v___y_1490_ = v_snd_1497_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0___boxed(lean_object* v_env_1512_, lean_object* v_projName_1513_, lean_object* v_as_1514_, lean_object* v_sz_1515_, lean_object* v_i_1516_, lean_object* v_b_1517_, lean_object* v___y_1518_){
_start:
{
size_t v_sz_boxed_1519_; size_t v_i_boxed_1520_; lean_object* v_res_1521_; 
v_sz_boxed_1519_ = lean_unbox_usize(v_sz_1515_);
lean_dec(v_sz_1515_);
v_i_boxed_1520_ = lean_unbox_usize(v_i_1516_);
lean_dec(v_i_1516_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go_spec__0(v_env_1512_, v_projName_1513_, v_as_1514_, v_sz_boxed_1519_, v_i_boxed_1520_, v_b_1517_, v___y_1518_);
lean_dec_ref(v_as_1514_);
lean_dec(v_projName_1513_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go___boxed(lean_object* v_env_1522_, lean_object* v_projName_1523_, lean_object* v_structName_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1522_, v_projName_1523_, v_structName_1524_, v_a_1525_);
lean_dec(v_projName_1523_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f(lean_object* v_env_1527_, lean_object* v_structName_1528_, lean_object* v_projName_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_fst_1532_; 
v___x_1530_ = l_Lean_NameSet_empty;
v___x_1531_ = l___private_Lean_Structure_0__Lean_findParentProjStruct_x3f_go(v_env_1527_, v_projName_1529_, v_structName_1528_, v___x_1530_);
v_fst_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_fst_1532_);
lean_dec_ref(v___x_1531_);
return v_fst_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_findParentProjStruct_x3f___boxed(lean_object* v_env_1533_, lean_object* v_structName_1534_, lean_object* v_projName_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_findParentProjStruct_x3f(v_env_1533_, v_structName_1534_, v_projName_1535_);
lean_dec(v_projName_1535_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFlatCtorOfStructCtorName(lean_object* v_structCtorName_1540_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_mkFlatCtorOfStructCtorName___closed__1));
v___x_1542_ = l_Lean_Name_append(v_structCtorName_1540_, v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(lean_object* v_env_1543_, lean_object* v_structName_1544_, uint8_t v_includeSubobjectFields_1545_, lean_object* v_as_1546_, size_t v_i_1547_, size_t v_stop_1548_, lean_object* v_b_1549_){
_start:
{
lean_object* v___y_1551_; uint8_t v___x_1555_; 
v___x_1555_ = lean_usize_dec_eq(v_i_1547_, v_stop_1548_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_array_uget_borrowed(v_as_1546_, v_i_1547_);
lean_inc(v___x_1556_);
lean_inc(v_structName_1544_);
lean_inc_ref(v_env_1543_);
v___x_1557_ = l_Lean_isSubobjectField_x3f(v_env_1543_, v_structName_1544_, v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; 
lean_inc(v___x_1556_);
v___x_1558_ = lean_array_push(v_b_1549_, v___x_1556_);
v___y_1551_ = v___x_1558_;
goto v___jp_1550_;
}
else
{
if (v_includeSubobjectFields_1545_ == 0)
{
lean_object* v_val_1559_; lean_object* v___x_1560_; 
v_val_1559_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1559_);
lean_dec_ref(v___x_1557_);
lean_inc_ref(v_env_1543_);
v___x_1560_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1543_, v_val_1559_, v_b_1549_, v_includeSubobjectFields_1545_);
v___y_1551_ = v___x_1560_;
goto v___jp_1550_;
}
else
{
lean_object* v_val_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_val_1561_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1561_);
lean_dec_ref(v___x_1557_);
lean_inc(v___x_1556_);
v___x_1562_ = lean_array_push(v_b_1549_, v___x_1556_);
lean_inc_ref(v_env_1543_);
v___x_1563_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1543_, v_val_1561_, v___x_1562_, v_includeSubobjectFields_1545_);
v___y_1551_ = v___x_1563_;
goto v___jp_1550_;
}
}
}
else
{
lean_dec(v_structName_1544_);
lean_dec_ref(v_env_1543_);
return v_b_1549_;
}
v___jp_1550_:
{
size_t v___x_1552_; size_t v___x_1553_; 
v___x_1552_ = ((size_t)1ULL);
v___x_1553_ = lean_usize_add(v_i_1547_, v___x_1552_);
v_i_1547_ = v___x_1553_;
v_b_1549_ = v___y_1551_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(lean_object* v_env_1564_, lean_object* v_structName_1565_, lean_object* v_fullNames_1566_, uint8_t v_includeSubobjectFields_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
lean_inc(v_structName_1565_);
lean_inc_ref(v_env_1564_);
v___x_1568_ = l_Lean_getStructureFields(v_env_1564_, v_structName_1565_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_array_get_size(v___x_1568_);
v___x_1571_ = lean_nat_dec_lt(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_dec_ref(v___x_1568_);
lean_dec(v_structName_1565_);
lean_dec_ref(v_env_1564_);
return v_fullNames_1566_;
}
else
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_le(v___x_1570_, v___x_1570_);
if (v___x_1572_ == 0)
{
if (v___x_1571_ == 0)
{
lean_dec_ref(v___x_1568_);
lean_dec(v_structName_1565_);
lean_dec_ref(v_env_1564_);
return v_fullNames_1566_;
}
else
{
size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = lean_usize_of_nat(v___x_1570_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1564_, v_structName_1565_, v_includeSubobjectFields_1567_, v___x_1568_, v___x_1573_, v___x_1574_, v_fullNames_1566_);
lean_dec_ref(v___x_1568_);
return v___x_1575_;
}
}
else
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = lean_usize_of_nat(v___x_1570_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1564_, v_structName_1565_, v_includeSubobjectFields_1567_, v___x_1568_, v___x_1576_, v___x_1577_, v_fullNames_1566_);
lean_dec_ref(v___x_1568_);
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux___boxed(lean_object* v_env_1579_, lean_object* v_structName_1580_, lean_object* v_fullNames_1581_, lean_object* v_includeSubobjectFields_1582_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1583_; lean_object* v_res_1584_; 
v_includeSubobjectFields_boxed_1583_ = lean_unbox(v_includeSubobjectFields_1582_);
v_res_1584_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1579_, v_structName_1580_, v_fullNames_1581_, v_includeSubobjectFields_boxed_1583_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0___boxed(lean_object* v_env_1585_, lean_object* v_structName_1586_, lean_object* v_includeSubobjectFields_1587_, lean_object* v_as_1588_, lean_object* v_i_1589_, lean_object* v_stop_1590_, lean_object* v_b_1591_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1592_; size_t v_i_boxed_1593_; size_t v_stop_boxed_1594_; lean_object* v_res_1595_; 
v_includeSubobjectFields_boxed_1592_ = lean_unbox(v_includeSubobjectFields_1587_);
v_i_boxed_1593_ = lean_unbox_usize(v_i_1589_);
lean_dec(v_i_1589_);
v_stop_boxed_1594_ = lean_unbox_usize(v_stop_1590_);
lean_dec(v_stop_1590_);
v_res_1595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux_spec__0(v_env_1585_, v_structName_1586_, v_includeSubobjectFields_boxed_1592_, v_as_1588_, v_i_boxed_1593_, v_stop_boxed_1594_, v_b_1591_);
lean_dec_ref(v_as_1588_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened(lean_object* v_env_1596_, lean_object* v_structName_1597_, uint8_t v_includeSubobjectFields_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = ((lean_object*)(l_Lean_getStructureInfo_x3f___closed__0));
v___x_1600_ = l___private_Lean_Structure_0__Lean_getStructureFieldsFlattenedAux(v_env_1596_, v_structName_1597_, v___x_1599_, v_includeSubobjectFields_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureFieldsFlattened___boxed(lean_object* v_env_1601_, lean_object* v_structName_1602_, lean_object* v_includeSubobjectFields_1603_){
_start:
{
uint8_t v_includeSubobjectFields_boxed_1604_; lean_object* v_res_1605_; 
v_includeSubobjectFields_boxed_1604_ = lean_unbox(v_includeSubobjectFields_1603_);
v_res_1605_ = l_Lean_getStructureFieldsFlattened(v_env_1601_, v_structName_1602_, v_includeSubobjectFields_boxed_1604_);
return v_res_1605_;
}
}
LEAN_EXPORT uint8_t l_Lean_isStructure(lean_object* v_env_1606_, lean_object* v_constName_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_getStructureInfo_x3f(v_env_1606_, v_constName_1607_);
if (lean_obj_tag(v___x_1608_) == 0)
{
uint8_t v___x_1609_; 
v___x_1609_ = 0;
return v___x_1609_;
}
else
{
uint8_t v___x_1610_; 
lean_dec_ref(v___x_1608_);
v___x_1610_ = 1;
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isStructure___boxed(lean_object* v_env_1611_, lean_object* v_constName_1612_){
_start:
{
uint8_t v_res_1613_; lean_object* v_r_1614_; 
v_res_1613_ = l_Lean_isStructure(v_env_1611_, v_constName_1612_);
v_r_1614_ = lean_box(v_res_1613_);
return v_r_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnForField_x3f(lean_object* v_env_1615_, lean_object* v_structName_1616_, lean_object* v_fieldName_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_getFieldInfo_x3f(v_env_1615_, v_structName_1616_, v_fieldName_1617_);
if (lean_obj_tag(v___x_1618_) == 1)
{
lean_object* v_val_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
v_val_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_val_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_projFn_1623_; lean_object* v___x_1625_; 
v_projFn_1623_ = lean_ctor_get(v_val_1619_, 1);
lean_inc(v_projFn_1623_);
lean_dec(v_val_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_projFn_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_projFn_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
lean_object* v___x_1628_; 
lean_dec(v___x_1618_);
v___x_1628_ = lean_box(0);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjFnInfoForField_x3f(lean_object* v_env_1629_, lean_object* v_structName_1630_, lean_object* v_fieldName_1631_){
_start:
{
lean_object* v___x_1632_; 
lean_inc_ref(v_env_1629_);
v___x_1632_ = l_Lean_getProjFnForField_x3f(v_env_1629_, v_structName_1630_, v_fieldName_1631_);
if (lean_obj_tag(v___x_1632_) == 1)
{
lean_object* v_val_1633_; lean_object* v___x_1634_; 
v_val_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1633_);
lean_dec_ref(v___x_1632_);
lean_inc(v_val_1633_);
v___x_1634_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_1629_, v_val_1633_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v___x_1635_; 
lean_dec(v_val_1633_);
v___x_1635_ = lean_box(0);
return v___x_1635_;
}
else
{
lean_object* v_val_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1644_; 
v_val_1636_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1638_ = v___x_1634_;
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_val_1636_);
lean_dec(v___x_1634_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_val_1633_);
lean_ctor_set(v___x_1640_, 1, v_val_1636_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1640_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v___x_1645_; 
lean_dec(v___x_1632_);
lean_dec_ref(v_env_1629_);
v___x_1645_ = lean_box(0);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefaultFnOfProjFn(lean_object* v_projFn_1649_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l_Lean_mkDefaultFnOfProjFn___closed__1));
v___x_1651_ = l_Lean_Name_append(v_projFn_1649_, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInheritedDefaultFnOfProjFn(lean_object* v_projFn_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_Lean_mkInheritedDefaultFnOfProjFn___closed__1));
v___x_1657_ = l_Lean_Name_append(v_projFn_1655_, v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(lean_object* v_mkName_1658_, lean_object* v_env_1659_, lean_object* v_structName_1660_, lean_object* v_fieldName_1661_){
_start:
{
lean_object* v___x_1662_; 
lean_inc(v_fieldName_1661_);
lean_inc(v_structName_1660_);
lean_inc_ref(v_env_1659_);
v___x_1662_ = l_Lean_getProjFnForField_x3f(v_env_1659_, v_structName_1660_, v_fieldName_1661_);
if (lean_obj_tag(v___x_1662_) == 1)
{
lean_object* v_val_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_fieldName_1661_);
lean_dec(v_structName_1660_);
v_val_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1674_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_val_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1674_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_defFn_1667_; uint8_t v___x_1668_; uint8_t v___x_1669_; 
v_defFn_1667_ = lean_apply_1(v_mkName_1658_, v_val_1663_);
v___x_1668_ = 1;
lean_inc(v_defFn_1667_);
v___x_1669_ = l_Lean_Environment_contains(v_env_1659_, v_defFn_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_dec(v_defFn_1667_);
lean_del_object(v___x_1665_);
v___x_1670_ = lean_box(0);
return v___x_1670_;
}
else
{
lean_object* v___x_1672_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v_defFn_1667_);
v___x_1672_ = v___x_1665_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_defFn_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v_defFn_1676_; uint8_t v___x_1677_; uint8_t v___x_1678_; 
lean_dec(v___x_1662_);
v___x_1675_ = l_Lean_Name_append(v_structName_1660_, v_fieldName_1661_);
v_defFn_1676_ = lean_apply_1(v_mkName_1658_, v___x_1675_);
v___x_1677_ = 1;
lean_inc(v_defFn_1676_);
v___x_1678_ = l_Lean_Environment_contains(v_env_1659_, v_defFn_1676_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_dec(v_defFn_1676_);
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_defFn_1676_);
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDefaultFnForField_x3f(lean_object* v_env_1682_, lean_object* v_structName_1683_, lean_object* v_fieldName_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_getDefaultFnForField_x3f___closed__0));
v___x_1686_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1685_, v_env_1682_, v_structName_1683_, v_fieldName_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_getEffectiveDefaultFnForField_x3f(lean_object* v_env_1688_, lean_object* v_structName_1689_, lean_object* v_fieldName_1690_){
_start:
{
lean_object* v___x_1691_; 
lean_inc(v_fieldName_1690_);
lean_inc(v_structName_1689_);
lean_inc_ref(v_env_1688_);
v___x_1691_ = l_Lean_getDefaultFnForField_x3f(v_env_1688_, v_structName_1689_, v_fieldName_1690_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_Lean_getEffectiveDefaultFnForField_x3f___closed__0));
v___x_1693_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1692_, v_env_1688_, v_structName_1689_, v_fieldName_1690_);
return v___x_1693_;
}
else
{
lean_dec(v_fieldName_1690_);
lean_dec(v_structName_1689_);
lean_dec_ref(v_env_1688_);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAutoParamFnOfProjFn(lean_object* v_projFn_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_mkAutoParamFnOfProjFn___closed__1));
v___x_1699_ = l_Lean_Name_append(v_projFn_1697_, v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAutoParamFnForField_x3f(lean_object* v_env_1701_, lean_object* v_structName_1702_, lean_object* v_fieldName_1703_){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_getAutoParamFnForField_x3f___closed__0));
v___x_1705_ = l___private_Lean_Structure_0__Lean_getFnForFieldUsing_x3f(v___x_1704_, v_env_1701_, v_structName_1702_, v_fieldName_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(lean_object* v_f_1706_, lean_object* v_as_1707_, lean_object* v_i_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = lean_array_get_size(v_as_1707_);
v___x_1711_ = lean_nat_dec_lt(v_i_1708_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v_i_1708_);
lean_dec_ref(v_f_1706_);
v___x_1712_ = lean_box(0);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v___y_1709_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v_fst_1716_; 
v___x_1714_ = lean_array_fget_borrowed(v_as_1707_, v_i_1708_);
lean_inc_ref(v_f_1706_);
lean_inc(v___x_1714_);
v___x_1715_ = lean_apply_2(v_f_1706_, v___x_1714_, v___y_1709_);
v_fst_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_fst_1716_);
if (lean_obj_tag(v_fst_1716_) == 0)
{
lean_object* v_snd_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_snd_1717_ = lean_ctor_get(v___x_1715_, 1);
lean_inc(v_snd_1717_);
lean_dec_ref(v___x_1715_);
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = lean_nat_add(v_i_1708_, v___x_1718_);
lean_dec(v_i_1708_);
v_i_1708_ = v___x_1719_;
v___y_1709_ = v_snd_1717_;
goto _start;
}
else
{
lean_dec_ref(v_fst_1716_);
lean_dec(v_i_1708_);
lean_dec_ref(v_f_1706_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg___boxed(lean_object* v_f_1721_, lean_object* v_as_1722_, lean_object* v_i_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v_f_1721_, v_as_1722_, v_i_1723_, v___y_1724_);
lean_dec_ref(v_as_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__1(lean_object* v_path_1726_, lean_object* v_env_1727_, lean_object* v_baseStructName_1728_, lean_object* v_field_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_subobject_x3f_1731_; 
v_subobject_x3f_1731_ = lean_ctor_get(v_field_1729_, 2);
lean_inc(v_subobject_x3f_1731_);
if (lean_obj_tag(v_subobject_x3f_1731_) == 1)
{
lean_object* v_projFn_1732_; lean_object* v_val_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_projFn_1732_ = lean_ctor_get(v_field_1729_, 1);
lean_inc(v_projFn_1732_);
lean_dec_ref(v_field_1729_);
v_val_1733_ = lean_ctor_get(v_subobject_x3f_1731_, 0);
lean_inc(v_val_1733_);
lean_dec_ref(v_subobject_x3f_1731_);
v___x_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1734_, 0, v_projFn_1732_);
lean_ctor_set(v___x_1734_, 1, v_path_1726_);
v___x_1735_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1727_, v_baseStructName_1728_, v_val_1733_, v___x_1734_, v___y_1730_);
return v___x_1735_;
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_dec(v_subobject_x3f_1731_);
lean_dec_ref(v_field_1729_);
lean_dec(v_baseStructName_1728_);
lean_dec_ref(v_env_1727_);
lean_dec(v_path_1726_);
v___x_1736_ = lean_box(0);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v___y_1730_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(lean_object* v_env_1738_, lean_object* v_baseStructName_1739_, lean_object* v_structName_1740_, lean_object* v_path_1741_, lean_object* v_a_1742_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_name_eq(v_baseStructName_1739_, v_structName_1740_);
if (v___x_1743_ == 0)
{
lean_object* v___f_1744_; lean_object* v___f_1745_; uint8_t v___x_1759_; 
lean_inc(v_baseStructName_1739_);
lean_inc_ref(v_env_1738_);
lean_inc(v_path_1741_);
v___f_1744_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__0), 5, 3);
lean_closure_set(v___f_1744_, 0, v_path_1741_);
lean_closure_set(v___f_1744_, 1, v_env_1738_);
lean_closure_set(v___f_1744_, 2, v_baseStructName_1739_);
lean_inc_ref(v_env_1738_);
v___f_1745_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__1), 5, 3);
lean_closure_set(v___f_1745_, 0, v_path_1741_);
lean_closure_set(v___f_1745_, 1, v_env_1738_);
lean_closure_set(v___f_1745_, 2, v_baseStructName_1739_);
v___x_1759_ = l_Lean_NameSet_contains(v_a_1742_, v_structName_1740_);
if (v___x_1759_ == 0)
{
goto v___jp_1746_;
}
else
{
if (v___x_1743_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec_ref(v___f_1745_);
lean_dec_ref(v___f_1744_);
lean_dec(v_structName_1740_);
lean_dec_ref(v_env_1738_);
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v_a_1742_);
return v___x_1761_;
}
else
{
goto v___jp_1746_;
}
}
v___jp_1746_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_inc(v_structName_1740_);
v___x_1747_ = l_Lean_NameSet_insert(v_a_1742_, v_structName_1740_);
v___x_1748_ = l_Lean_getStructureInfo_x3f(v_env_1738_, v_structName_1740_);
if (lean_obj_tag(v___x_1748_) == 1)
{
lean_object* v_val_1749_; lean_object* v_fieldInfo_1750_; lean_object* v_parentInfo_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v_fst_1754_; 
v_val_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_val_1749_);
lean_dec_ref(v___x_1748_);
v_fieldInfo_1750_ = lean_ctor_get(v_val_1749_, 2);
lean_inc_ref(v_fieldInfo_1750_);
v_parentInfo_1751_ = lean_ctor_get(v_val_1749_, 3);
lean_inc_ref(v_parentInfo_1751_);
lean_dec(v_val_1749_);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v___f_1745_, v_fieldInfo_1750_, v___x_1752_, v___x_1747_);
lean_dec_ref(v_fieldInfo_1750_);
v_fst_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_fst_1754_);
if (lean_obj_tag(v_fst_1754_) == 0)
{
lean_object* v_snd_1755_; lean_object* v___x_1756_; 
v_snd_1755_ = lean_ctor_get(v___x_1753_, 1);
lean_inc(v_snd_1755_);
lean_dec_ref(v___x_1753_);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v___f_1744_, v_parentInfo_1751_, v___x_1752_, v_snd_1755_);
lean_dec_ref(v_parentInfo_1751_);
return v___x_1756_;
}
else
{
lean_dec_ref(v_fst_1754_);
lean_dec_ref(v_parentInfo_1751_);
lean_dec_ref(v___f_1744_);
return v___x_1753_;
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v___x_1748_);
lean_dec_ref(v___f_1745_);
lean_dec_ref(v___f_1744_);
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1747_);
return v___x_1758_;
}
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec(v_structName_1740_);
lean_dec(v_baseStructName_1739_);
lean_dec_ref(v_env_1738_);
v___x_1762_ = l_List_reverse___redArg(v_path_1741_);
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v_a_1742_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go___lam__0(lean_object* v_path_1765_, lean_object* v_env_1766_, lean_object* v_baseStructName_1767_, lean_object* v_parent_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_structName_1770_; lean_object* v_projFn_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v_structName_1770_ = lean_ctor_get(v_parent_1768_, 0);
lean_inc(v_structName_1770_);
v_projFn_1771_ = lean_ctor_get(v_parent_1768_, 1);
lean_inc(v_projFn_1771_);
lean_dec_ref(v_parent_1768_);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_projFn_1771_);
lean_ctor_set(v___x_1772_, 1, v_path_1765_);
v___x_1773_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1766_, v_baseStructName_1767_, v_structName_1770_, v___x_1772_, v___y_1769_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(lean_object* v_00_u03b2_1774_, lean_object* v_00_u03b1_1775_, lean_object* v_f_1776_, lean_object* v_as_1777_, lean_object* v_i_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___redArg(v_f_1776_, v_as_1777_, v_i_1778_, v___y_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0___boxed(lean_object* v_00_u03b2_1781_, lean_object* v_00_u03b1_1782_, lean_object* v_f_1783_, lean_object* v_as_1784_, lean_object* v_i_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go___at___00__private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go_spec__0(v_00_u03b2_1781_, v_00_u03b1_1782_, v_f_1783_, v_as_1784_, v_i_1785_, v___y_1786_);
lean_dec_ref(v_as_1784_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object* v_env_1788_, lean_object* v_baseStructName_1789_, lean_object* v_structName_1790_){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_fst_1794_; 
v___x_1791_ = lean_box(0);
v___x_1792_ = l_Lean_NameSet_empty;
v___x_1793_ = l___private_Lean_Structure_0__Lean_getPathToBaseStructure_x3f_go(v_env_1788_, v_baseStructName_1789_, v_structName_1790_, v___x_1791_, v___x_1792_);
v_fst_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_fst_1794_);
lean_dec_ref(v___x_1793_);
return v_fst_1794_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNonRecStructure(lean_object* v_env_1795_, lean_object* v_constName_1796_){
_start:
{
uint8_t v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = 0;
v___x_1798_ = l_Lean_Environment_find_x3f(v_env_1795_, v_constName_1796_, v___x_1797_);
if (lean_obj_tag(v___x_1798_) == 1)
{
lean_object* v_val_1799_; 
v_val_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_val_1799_);
lean_dec_ref(v___x_1798_);
if (lean_obj_tag(v_val_1799_) == 5)
{
lean_object* v_val_1800_; lean_object* v_numIndices_1801_; lean_object* v_ctors_1802_; uint8_t v_isRec_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_val_1800_ = lean_ctor_get(v_val_1799_, 0);
lean_inc_ref(v_val_1800_);
lean_dec_ref(v_val_1799_);
v_numIndices_1801_ = lean_ctor_get(v_val_1800_, 2);
lean_inc(v_numIndices_1801_);
v_ctors_1802_ = lean_ctor_get(v_val_1800_, 4);
lean_inc(v_ctors_1802_);
v_isRec_1803_ = lean_ctor_get_uint8(v_val_1800_, sizeof(void*)*6);
lean_dec_ref(v_val_1800_);
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = lean_nat_dec_eq(v_numIndices_1801_, v___x_1804_);
lean_dec(v_numIndices_1801_);
if (v___x_1805_ == 0)
{
lean_dec(v_ctors_1802_);
return v___x_1797_;
}
else
{
if (lean_obj_tag(v_ctors_1802_) == 1)
{
lean_object* v_tail_1806_; 
v_tail_1806_ = lean_ctor_get(v_ctors_1802_, 1);
lean_inc(v_tail_1806_);
lean_dec_ref(v_ctors_1802_);
if (lean_obj_tag(v_tail_1806_) == 0)
{
if (v_isRec_1803_ == 0)
{
return v___x_1805_;
}
else
{
return v___x_1797_;
}
}
else
{
lean_dec(v_tail_1806_);
return v___x_1797_;
}
}
else
{
lean_dec(v_ctors_1802_);
return v___x_1797_;
}
}
}
else
{
lean_dec(v_val_1799_);
return v___x_1797_;
}
}
else
{
lean_dec(v___x_1798_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNonRecStructure___boxed(lean_object* v_env_1807_, lean_object* v_constName_1808_){
_start:
{
uint8_t v_res_1809_; lean_object* v_r_1810_; 
v_res_1809_ = l_Lean_isNonRecStructure(v_env_1807_, v_constName_1808_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(lean_object* v_msg_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_panic_fn_borrowed(v___x_1812_, v_msg_1811_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_getNonRecStructureCtor_x3f___closed__1(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1815_ = ((lean_object*)(l_Lean_getStructureCtor___closed__2));
v___x_1816_ = lean_unsigned_to_nat(11u);
v___x_1817_ = lean_unsigned_to_nat(374u);
v___x_1818_ = ((lean_object*)(l_Lean_getNonRecStructureCtor_x3f___closed__0));
v___x_1819_ = ((lean_object*)(l_Lean_getStructureInfo___closed__0));
v___x_1820_ = l_mkPanicMessageWithDecl(v___x_1819_, v___x_1818_, v___x_1817_, v___x_1816_, v___x_1815_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureCtor_x3f(lean_object* v_env_1821_, lean_object* v_constName_1822_){
_start:
{
uint8_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = 0;
lean_inc_ref(v_env_1821_);
v___x_1827_ = l_Lean_Environment_find_x3f(v_env_1821_, v_constName_1822_, v___x_1826_);
if (lean_obj_tag(v___x_1827_) == 1)
{
lean_object* v_val_1828_; 
v_val_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_val_1828_);
lean_dec_ref(v___x_1827_);
if (lean_obj_tag(v_val_1828_) == 5)
{
lean_object* v_val_1829_; lean_object* v_numIndices_1830_; lean_object* v_ctors_1831_; uint8_t v_isRec_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_val_1829_ = lean_ctor_get(v_val_1828_, 0);
lean_inc_ref(v_val_1829_);
lean_dec_ref(v_val_1828_);
v_numIndices_1830_ = lean_ctor_get(v_val_1829_, 2);
lean_inc(v_numIndices_1830_);
v_ctors_1831_ = lean_ctor_get(v_val_1829_, 4);
lean_inc(v_ctors_1831_);
v_isRec_1832_ = lean_ctor_get_uint8(v_val_1829_, sizeof(void*)*6);
lean_dec_ref(v_val_1829_);
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1834_ = lean_nat_dec_eq(v_numIndices_1830_, v___x_1833_);
lean_dec(v_numIndices_1830_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec(v_ctors_1831_);
lean_dec_ref(v_env_1821_);
v___x_1835_ = lean_box(0);
return v___x_1835_;
}
else
{
if (lean_obj_tag(v_ctors_1831_) == 1)
{
lean_object* v_tail_1836_; 
v_tail_1836_ = lean_ctor_get(v_ctors_1831_, 1);
if (lean_obj_tag(v_tail_1836_) == 0)
{
if (v_isRec_1832_ == 0)
{
lean_object* v_head_1837_; lean_object* v___x_1838_; 
v_head_1837_ = lean_ctor_get(v_ctors_1831_, 0);
lean_inc(v_head_1837_);
lean_dec_ref(v_ctors_1831_);
v___x_1838_ = l_Lean_Environment_find_x3f(v_env_1821_, v_head_1837_, v_isRec_1832_);
if (lean_obj_tag(v___x_1838_) == 1)
{
lean_object* v_val_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1847_; 
v_val_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_val_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
if (lean_obj_tag(v_val_1839_) == 6)
{
lean_object* v_val_1843_; lean_object* v___x_1845_; 
v_val_1843_ = lean_ctor_get(v_val_1839_, 0);
lean_inc_ref(v_val_1843_);
lean_dec_ref(v_val_1839_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v_val_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_val_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
else
{
lean_del_object(v___x_1841_);
lean_dec(v_val_1839_);
goto v___jp_1823_;
}
}
}
else
{
lean_dec(v___x_1838_);
goto v___jp_1823_;
}
}
else
{
lean_object* v___x_1848_; 
lean_dec_ref(v_ctors_1831_);
lean_dec_ref(v_env_1821_);
v___x_1848_ = lean_box(0);
return v___x_1848_;
}
}
else
{
lean_object* v___x_1849_; 
lean_dec_ref(v_ctors_1831_);
lean_dec_ref(v_env_1821_);
v___x_1849_ = lean_box(0);
return v___x_1849_;
}
}
else
{
lean_object* v___x_1850_; 
lean_dec(v_ctors_1831_);
lean_dec_ref(v_env_1821_);
v___x_1850_ = lean_box(0);
return v___x_1850_;
}
}
}
else
{
lean_object* v___x_1851_; 
lean_dec(v_val_1828_);
lean_dec_ref(v_env_1821_);
v___x_1851_ = lean_box(0);
return v___x_1851_;
}
}
else
{
lean_object* v___x_1852_; 
lean_dec(v___x_1827_);
lean_dec_ref(v_env_1821_);
v___x_1852_ = lean_box(0);
return v___x_1852_;
}
v___jp_1823_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_obj_once(&l_Lean_getNonRecStructureCtor_x3f___closed__1, &l_Lean_getNonRecStructureCtor_x3f___closed__1_once, _init_l_Lean_getNonRecStructureCtor_x3f___closed__1);
v___x_1825_ = l_panic___at___00Lean_getNonRecStructureCtor_x3f_spec__0(v___x_1824_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getNonRecStructureNumFields(lean_object* v_env_1853_, lean_object* v_constName_1854_){
_start:
{
uint8_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = 0;
lean_inc_ref(v_env_1853_);
v___x_1856_ = l_Lean_Environment_find_x3f(v_env_1853_, v_constName_1854_, v___x_1855_);
if (lean_obj_tag(v___x_1856_) == 1)
{
lean_object* v_val_1857_; 
v_val_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_val_1857_);
lean_dec_ref(v___x_1856_);
if (lean_obj_tag(v_val_1857_) == 5)
{
lean_object* v_val_1858_; lean_object* v_numIndices_1859_; lean_object* v_ctors_1860_; uint8_t v_isRec_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_val_1858_ = lean_ctor_get(v_val_1857_, 0);
lean_inc_ref(v_val_1858_);
lean_dec_ref(v_val_1857_);
v_numIndices_1859_ = lean_ctor_get(v_val_1858_, 2);
lean_inc(v_numIndices_1859_);
v_ctors_1860_ = lean_ctor_get(v_val_1858_, 4);
lean_inc(v_ctors_1860_);
v_isRec_1861_ = lean_ctor_get_uint8(v_val_1858_, sizeof(void*)*6);
lean_dec_ref(v_val_1858_);
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = lean_nat_dec_eq(v_numIndices_1859_, v___x_1862_);
lean_dec(v_numIndices_1859_);
if (v___x_1863_ == 0)
{
lean_dec(v_ctors_1860_);
lean_dec_ref(v_env_1853_);
return v___x_1862_;
}
else
{
if (lean_obj_tag(v_ctors_1860_) == 1)
{
lean_object* v_tail_1864_; 
v_tail_1864_ = lean_ctor_get(v_ctors_1860_, 1);
if (lean_obj_tag(v_tail_1864_) == 0)
{
if (v_isRec_1861_ == 0)
{
lean_object* v_head_1865_; lean_object* v___x_1866_; 
v_head_1865_ = lean_ctor_get(v_ctors_1860_, 0);
lean_inc(v_head_1865_);
lean_dec_ref(v_ctors_1860_);
v___x_1866_ = l_Lean_Environment_find_x3f(v_env_1853_, v_head_1865_, v_isRec_1861_);
if (lean_obj_tag(v___x_1866_) == 1)
{
lean_object* v_val_1867_; 
v_val_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_val_1867_);
lean_dec_ref(v___x_1866_);
if (lean_obj_tag(v_val_1867_) == 6)
{
lean_object* v_val_1868_; lean_object* v_numFields_1869_; 
v_val_1868_ = lean_ctor_get(v_val_1867_, 0);
lean_inc_ref(v_val_1868_);
lean_dec_ref(v_val_1867_);
v_numFields_1869_ = lean_ctor_get(v_val_1868_, 4);
lean_inc(v_numFields_1869_);
lean_dec_ref(v_val_1868_);
return v_numFields_1869_;
}
else
{
lean_dec(v_val_1867_);
return v___x_1862_;
}
}
else
{
lean_dec(v___x_1866_);
return v___x_1862_;
}
}
else
{
lean_dec_ref(v_ctors_1860_);
lean_dec_ref(v_env_1853_);
return v___x_1862_;
}
}
else
{
lean_dec_ref(v_ctors_1860_);
lean_dec_ref(v_env_1853_);
return v___x_1862_;
}
}
else
{
lean_dec(v_ctors_1860_);
lean_dec_ref(v_env_1853_);
return v___x_1862_;
}
}
}
else
{
lean_object* v___x_1870_; 
lean_dec(v_val_1857_);
lean_dec_ref(v_env_1853_);
v___x_1870_ = lean_unsigned_to_nat(0u);
return v___x_1870_;
}
}
else
{
lean_object* v___x_1871_; 
lean_dec(v___x_1856_);
lean_dec_ref(v_env_1853_);
v___x_1871_ = lean_unsigned_to_nat(0u);
return v___x_1871_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0(void){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__0, &l_Lean_instInhabitedStructureResolutionState_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__0);
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState_default(void){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionState(void){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_instInhabitedStructureResolutionState_default;
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(lean_object* v___x_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v___x_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(v___x_1880_);
return v_res_1882_;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___f_1884_; 
v___x_1883_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionState_default___closed__1, &l_Lean_instInhabitedStructureResolutionState_default___closed__1_once, _init_l_Lean_instInhabitedStructureResolutionState_default___closed__1);
v___f_1884_ = lean_alloc_closure((void*)(l_Lean_initFn___lam__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1884_, 0, v___x_1883_);
return v___f_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___f_1886_ = lean_obj_once(&l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_, &l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__0_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_);
v___x_1887_ = lean_box(0);
v___x_1888_ = lean_box(1);
v___x_1889_ = l_Lean_registerEnvExtension___redArg(v___f_1886_, v___x_1887_, v___x_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2____boxed(lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object* v_env_1892_, lean_object* v_structName_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v_asyncMode_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1894_ = l_Lean_structureResolutionExt;
v_asyncMode_1895_ = lean_ctor_get(v___x_1894_, 2);
lean_inc(v_asyncMode_1895_);
v___x_1896_ = l_Lean_instInhabitedStructureResolutionState_default;
v___x_1897_ = lean_box(0);
v___x_1898_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1896_, v___x_1894_, v_env_1892_, v_asyncMode_1895_, v___x_1897_);
lean_dec(v_asyncMode_1895_);
v___x_1899_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_getStructureInfo_x3f_spec__0___redArg(v___x_1898_, v_structName_1893_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f___boxed(lean_object* v_env_1900_, lean_object* v_structName_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_1900_, v_structName_1901_);
lean_dec(v_structName_1901_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0(lean_object* v___x_1903_, lean_object* v___x_1904_, lean_object* v_structName_1905_, lean_object* v_resolutionOrder_1906_, lean_object* v_s_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_PersistentHashMap_insert___redArg(v___x_1903_, v___x_1904_, v_s_1907_, v_structName_1905_, v_resolutionOrder_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1(lean_object* v___f_1909_, lean_object* v_env_1910_){
_start:
{
lean_object* v___x_1911_; lean_object* v_asyncMode_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1911_ = l_Lean_structureResolutionExt;
v_asyncMode_1912_ = lean_ctor_get(v___x_1911_, 2);
lean_inc(v_asyncMode_1912_);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1911_, v_env_1910_, v___f_1909_, v_asyncMode_1912_, v___x_1913_);
lean_dec(v_asyncMode_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(lean_object* v_inst_1915_, lean_object* v_structName_1916_, lean_object* v_resolutionOrder_1917_){
_start:
{
lean_object* v_modifyEnv_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___f_1921_; lean_object* v___f_1922_; lean_object* v___x_1923_; 
v_modifyEnv_1918_ = lean_ctor_get(v_inst_1915_, 1);
lean_inc(v_modifyEnv_1918_);
lean_dec_ref(v_inst_1915_);
v___x_1919_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
v___x_1920_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__1));
v___f_1921_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1921_, 0, v___x_1919_);
lean_closure_set(v___f_1921_, 1, v___x_1920_);
lean_closure_set(v___f_1921_, 2, v_structName_1916_);
lean_closure_set(v___f_1921_, 3, v_resolutionOrder_1917_);
v___f_1922_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1922_, 0, v___f_1921_);
v___x_1923_ = lean_apply_1(v_modifyEnv_1918_, v___f_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder(lean_object* v_m_1924_, lean_object* v_inst_1925_, lean_object* v_structName_1926_, lean_object* v_resolutionOrder_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_1925_, v_structName_1926_, v_resolutionOrder_1927_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_Lean_instInhabitedStructureInfo_default___closed__0));
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
return v___x_1938_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionOrderResult_default(void){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_obj_once(&l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0, &l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0_once, _init_l_Lean_instInhabitedStructureResolutionOrderResult_default___closed__0);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_instInhabitedStructureResolutionOrderResult(void){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_instInhabitedStructureResolutionOrderResult_default;
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(lean_object* v___x_1941_, lean_object* v_resOrders_1942_, lean_object* v___x_1943_, lean_object* v_toPure_1944_, lean_object* v_____s_1945_){
_start:
{
lean_object* v_fst_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1961_; 
v_fst_1946_ = lean_ctor_get(v_____s_1945_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_____s_1945_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v_____s_1945_, 1);
lean_dec(v_unused_1962_);
v___x_1948_ = v_____s_1945_;
v_isShared_1949_ = v_isSharedCheck_1961_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_fst_1946_);
lean_dec(v_____s_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1961_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
if (lean_obj_tag(v_fst_1946_) == 0)
{
uint8_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1950_ = 0;
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = lean_array_get_borrowed(v___x_1941_, v_resOrders_1942_, v___x_1951_);
v___x_1953_ = lean_array_get_borrowed(v___x_1943_, v___x_1952_, v___x_1951_);
v___x_1954_ = lean_box(v___x_1950_);
lean_inc(v___x_1953_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___x_1953_);
lean_ctor_set(v___x_1948_, 0, v___x_1954_);
v___x_1956_ = v___x_1948_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1953_);
v___x_1956_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_apply_2(v_toPure_1944_, lean_box(0), v___x_1956_);
return v___x_1957_;
}
}
else
{
lean_object* v_val_1959_; lean_object* v___x_1960_; 
lean_del_object(v___x_1948_);
v_val_1959_ = lean_ctor_get(v_fst_1946_, 0);
lean_inc(v_val_1959_);
lean_dec_ref(v_fst_1946_);
v___x_1960_ = lean_apply_2(v_toPure_1944_, lean_box(0), v_val_1959_);
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed(lean_object* v___x_1963_, lean_object* v_resOrders_1964_, lean_object* v___x_1965_, lean_object* v_toPure_1966_, lean_object* v_____s_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0(v___x_1963_, v_resOrders_1964_, v___x_1965_, v_toPure_1966_, v_____s_1967_);
lean_dec(v___x_1965_);
lean_dec_ref(v_resOrders_1964_);
lean_dec_ref(v___x_1963_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1(lean_object* v_toPure_1969_, lean_object* v_____do__lift_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_apply_2(v_toPure_1969_, lean_box(0), v_____do__lift_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3(lean_object* v___x_1972_, lean_object* v_toPure_1973_, lean_object* v___x_1974_, lean_object* v_____s_1975_){
_start:
{
lean_object* v_fst_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1994_; 
v_fst_1976_ = lean_ctor_get(v_____s_1975_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_____s_1975_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v_____s_1975_, 1);
lean_dec(v_unused_1995_);
v___x_1978_ = v_____s_1975_;
v_isShared_1979_ = v_isSharedCheck_1994_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_fst_1976_);
lean_dec(v_____s_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1994_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
if (lean_obj_tag(v_fst_1976_) == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_del_object(v___x_1978_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1972_);
v___x_1981_ = lean_apply_2(v_toPure_1973_, lean_box(0), v___x_1980_);
return v___x_1981_;
}
else
{
lean_object* v___x_1983_; 
lean_dec_ref(v___x_1972_);
lean_inc_ref(v_fst_1976_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v___x_1974_);
v___x_1983_ = v___x_1978_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_fst_1976_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1974_);
v___x_1983_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1991_; 
v_isSharedCheck_1991_ = !lean_is_exclusive(v_fst_1976_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v_fst_1976_, 0);
lean_dec(v_unused_1992_);
v___x_1985_ = v_fst_1976_;
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
else
{
lean_dec(v_fst_1976_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1991_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set_tag(v___x_1985_, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1983_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_apply_2(v_toPure_1973_, lean_box(0), v___x_1988_);
return v___x_1989_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(lean_object* v_toPure_1996_, lean_object* v_next_1997_, lean_object* v_G_1998_, lean_object* v_____do__lift_1999_){
_start:
{
if (lean_obj_tag(v_____do__lift_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; 
lean_dec(v_G_1998_);
v_a_2000_ = lean_ctor_get(v_____do__lift_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v_____do__lift_1999_);
v___x_2001_ = lean_apply_2(v_toPure_1996_, lean_box(0), v_a_2000_);
return v___x_2001_;
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec(v_toPure_1996_);
v_a_2002_ = lean_ctor_get(v_____do__lift_1999_, 0);
lean_inc(v_a_2002_);
lean_dec_ref(v_____do__lift_1999_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_add(v_next_1997_, v___x_2003_);
v___x_2005_ = lean_apply_4(v_G_1998_, v___x_2004_, v_a_2002_, lean_box(0), lean_box(0));
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed(lean_object* v_toPure_2006_, lean_object* v_next_2007_, lean_object* v_G_2008_, lean_object* v_____do__lift_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2(v_toPure_2006_, v_next_2007_, v_G_2008_, v_____do__lift_2009_);
lean_dec(v_next_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(lean_object* v___x_2011_, lean_object* v_v_2012_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_name_eq(v_v_2012_, v___x_2011_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed(lean_object* v___x_2014_, lean_object* v_v_2015_){
_start:
{
uint8_t v_res_2016_; lean_object* v_r_2017_; 
v_res_2016_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5(v___x_2014_, v_v_2015_);
lean_dec(v_v_2015_);
lean_dec(v___x_2014_);
v_r_2017_ = lean_box(v_res_2016_);
return v_r_2017_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(uint8_t v___x_2037_, lean_object* v___f_2038_, lean_object* v_resOrder_2039_){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v_array_2044_; lean_object* v_start_2045_; lean_object* v_stop_2046_; uint8_t v___x_2047_; lean_object* v___y_2049_; 
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_array_get_size(v_resOrder_2039_);
v___x_2042_ = l_Array_toSubarray___redArg(v_resOrder_2039_, v___x_2040_, v___x_2041_);
v___x_2043_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2044_ = lean_ctor_get(v___x_2042_, 0);
lean_inc_ref(v_array_2044_);
v_start_2045_ = lean_ctor_get(v___x_2042_, 1);
lean_inc(v_start_2045_);
v_stop_2046_ = lean_ctor_get(v___x_2042_, 2);
lean_inc(v_stop_2046_);
lean_dec_ref(v___x_2042_);
v___x_2047_ = lean_nat_dec_lt(v_start_2045_, v_stop_2046_);
if (v___x_2047_ == 0)
{
lean_dec(v_stop_2046_);
lean_dec(v_start_2045_);
lean_dec_ref(v_array_2044_);
lean_dec_ref(v___f_2038_);
return v___x_2037_;
}
else
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = lean_array_get_size(v_array_2044_);
v___x_2057_ = lean_nat_dec_le(v_stop_2046_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_dec(v_stop_2046_);
v___y_2049_ = v___x_2056_;
goto v___jp_2048_;
}
else
{
v___y_2049_ = v_stop_2046_;
goto v___jp_2048_;
}
}
v___jp_2048_:
{
uint8_t v___x_2050_; 
v___x_2050_ = lean_nat_dec_lt(v_start_2045_, v___y_2049_);
if (v___x_2050_ == 0)
{
lean_dec(v___y_2049_);
lean_dec(v_start_2045_);
lean_dec_ref(v_array_2044_);
lean_dec_ref(v___f_2038_);
return v___x_2047_;
}
else
{
size_t v___x_2051_; size_t v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2051_ = lean_usize_of_nat(v_start_2045_);
lean_dec(v_start_2045_);
v___x_2052_ = lean_usize_of_nat(v___y_2049_);
lean_dec(v___y_2049_);
v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2043_, v___f_2038_, v_array_2044_, v___x_2051_, v___x_2052_);
v___x_2054_ = lean_unbox(v___x_2053_);
lean_dec(v___x_2053_);
if (v___x_2054_ == 0)
{
return v___x_2050_;
}
else
{
uint8_t v___x_2055_; 
v___x_2055_ = 0;
return v___x_2055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed(lean_object* v___x_2058_, lean_object* v___f_2059_, lean_object* v_resOrder_2060_){
_start:
{
uint8_t v___x_1715__boxed_2061_; uint8_t v_res_2062_; lean_object* v_r_2063_; 
v___x_1715__boxed_2061_ = lean_unbox(v___x_2058_);
v_res_2062_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4(v___x_1715__boxed_2061_, v___f_2059_, v_resOrder_2060_);
v_r_2063_ = lean_box(v_res_2062_);
return v_r_2063_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(lean_object* v___f_2064_, uint8_t v___y_2065_, lean_object* v_v_2066_){
_start:
{
lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = lean_apply_1(v___f_2064_, v_v_2066_);
v___x_2068_ = lean_unbox(v___x_2067_);
if (v___x_2068_ == 0)
{
return v___y_2065_;
}
else
{
uint8_t v___x_2069_; 
v___x_2069_ = 0;
return v___x_2069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed(lean_object* v___f_2070_, lean_object* v___y_2071_, lean_object* v_v_2072_){
_start:
{
uint8_t v___y_1771__boxed_2073_; uint8_t v_res_2074_; lean_object* v_r_2075_; 
v___y_1771__boxed_2073_ = lean_unbox(v___y_2071_);
v_res_2074_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6(v___f_2070_, v___y_1771__boxed_2073_, v_v_2072_);
v_r_2075_ = lean_box(v_res_2074_);
return v_r_2075_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(lean_object* v___f_2076_, uint8_t v___x_2077_, lean_object* v_v_2078_){
_start:
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = lean_apply_1(v___f_2076_, v_v_2078_);
v___x_2080_ = lean_unbox(v___x_2079_);
if (v___x_2080_ == 0)
{
return v___x_2077_;
}
else
{
uint8_t v___x_2081_; 
v___x_2081_ = 0;
return v___x_2081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed(lean_object* v___f_2082_, lean_object* v___x_2083_, lean_object* v_v_2084_){
_start:
{
uint8_t v___x_1783__boxed_2085_; uint8_t v_res_2086_; lean_object* v_r_2087_; 
v___x_1783__boxed_2085_ = lean_unbox(v___x_2083_);
v_res_2086_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7(v___f_2082_, v___x_1783__boxed_2085_, v_v_2084_);
v_r_2087_ = lean_box(v_res_2086_);
return v_r_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(lean_object* v___x_2088_, lean_object* v_toPure_2089_, lean_object* v___x_2090_, lean_object* v_resOrders_2091_, lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v_toBind_2094_, lean_object* v___f_2095_, lean_object* v___x_2096_, lean_object* v_next_2097_, lean_object* v___x_2098_, lean_object* v_next_2099_, lean_object* v_acc_2100_, lean_object* v_h_2101_, lean_object* v_G_2102_){
_start:
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_nat_dec_lt(v_next_2099_, v___x_2088_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
lean_dec(v_G_2102_);
lean_dec(v_next_2099_);
lean_dec_ref(v___x_2096_);
lean_dec(v___f_2095_);
lean_dec(v_toBind_2094_);
lean_dec(v___x_2093_);
lean_dec_ref(v_resOrders_2091_);
lean_dec(v___x_2088_);
v___x_2104_ = lean_apply_2(v_toPure_2089_, lean_box(0), v_acc_2100_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v_array_2109_; lean_object* v_start_2110_; lean_object* v_stop_2111_; lean_object* v___f_2112_; lean_object* v___y_2114_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___f_2139_; lean_object* v___x_2140_; lean_object* v___f_2141_; uint8_t v___y_2143_; uint8_t v___x_2155_; 
lean_dec_ref(v_acc_2100_);
v___x_2105_ = lean_array_get_borrowed(v___x_2090_, v_resOrders_2091_, v_next_2099_);
v___x_2106_ = lean_array_get(v___x_2092_, v___x_2105_, v___x_2093_);
lean_inc(v_next_2099_);
lean_inc(v___x_2093_);
lean_inc_ref(v_resOrders_2091_);
v___x_2107_ = l_Array_toSubarray___redArg(v_resOrders_2091_, v___x_2093_, v_next_2099_);
v___x_2108_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2109_ = lean_ctor_get(v___x_2107_, 0);
lean_inc_ref(v_array_2109_);
v_start_2110_ = lean_ctor_get(v___x_2107_, 1);
lean_inc(v_start_2110_);
v_stop_2111_ = lean_ctor_get(v___x_2107_, 2);
lean_inc(v_stop_2111_);
lean_dec_ref(v___x_2107_);
lean_inc(v_next_2099_);
lean_inc(v_toPure_2089_);
v___f_2112_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2112_, 0, v_toPure_2089_);
lean_closure_set(v___f_2112_, 1, v_next_2099_);
lean_closure_set(v___f_2112_, 2, v_G_2102_);
lean_inc(v___x_2106_);
v___f_2139_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2139_, 0, v___x_2106_);
v___x_2140_ = lean_box(v___x_2103_);
v___f_2141_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___boxed), 3, 2);
lean_closure_set(v___f_2141_, 0, v___x_2140_);
lean_closure_set(v___f_2141_, 1, v___f_2139_);
v___x_2155_ = lean_nat_dec_lt(v_start_2110_, v_stop_2111_);
if (v___x_2155_ == 0)
{
lean_dec(v_stop_2111_);
lean_dec(v_start_2110_);
lean_dec_ref(v_array_2109_);
v___y_2143_ = v___x_2103_;
goto v___jp_2142_;
}
else
{
lean_object* v___x_2156_; lean_object* v___f_2157_; lean_object* v___y_2159_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2156_ = lean_box(v___x_2103_);
lean_inc_ref(v___f_2141_);
v___f_2157_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2157_, 0, v___f_2141_);
lean_closure_set(v___f_2157_, 1, v___x_2156_);
v___x_2165_ = lean_array_get_size(v_array_2109_);
v___x_2166_ = lean_nat_dec_le(v_stop_2111_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_dec(v_stop_2111_);
v___y_2159_ = v___x_2165_;
goto v___jp_2158_;
}
else
{
v___y_2159_ = v_stop_2111_;
goto v___jp_2158_;
}
v___jp_2158_:
{
uint8_t v___x_2160_; 
v___x_2160_ = lean_nat_dec_lt(v_start_2110_, v___y_2159_);
if (v___x_2160_ == 0)
{
lean_dec(v___y_2159_);
lean_dec_ref(v___f_2157_);
lean_dec(v_start_2110_);
lean_dec_ref(v_array_2109_);
v___y_2143_ = v___x_2155_;
goto v___jp_2142_;
}
else
{
size_t v___x_2161_; size_t v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2161_ = lean_usize_of_nat(v_start_2110_);
lean_dec(v_start_2110_);
v___x_2162_ = lean_usize_of_nat(v___y_2159_);
lean_dec(v___y_2159_);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2108_, v___f_2157_, v_array_2109_, v___x_2161_, v___x_2162_);
v___x_2164_ = lean_unbox(v___x_2163_);
lean_dec(v___x_2163_);
if (v___x_2164_ == 0)
{
v___y_2143_ = v___x_2160_;
goto v___jp_2142_;
}
else
{
lean_dec_ref(v___f_2141_);
lean_dec(v___x_2106_);
lean_dec(v_next_2099_);
lean_dec(v___x_2093_);
lean_dec_ref(v_resOrders_2091_);
lean_dec(v___x_2088_);
goto v___jp_2117_;
}
}
}
}
v___jp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_inc(v_toBind_2094_);
v___x_2115_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___y_2114_, v___f_2095_);
v___x_2116_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___x_2115_, v___f_2112_);
return v___x_2116_;
}
v___jp_2117_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2096_);
v___x_2119_ = lean_apply_2(v_toPure_2089_, lean_box(0), v___x_2118_);
v___y_2114_ = v___x_2119_;
goto v___jp_2113_;
}
v___jp_2120_:
{
uint8_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2121_ = lean_nat_dec_eq(v_next_2097_, v___x_2093_);
lean_dec(v___x_2093_);
v___x_2122_ = lean_box(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2106_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2098_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
v___x_2127_ = lean_apply_2(v_toPure_2089_, lean_box(0), v___x_2126_);
v___y_2114_ = v___x_2127_;
goto v___jp_2113_;
}
v___jp_2128_:
{
uint8_t v___x_2134_; 
v___x_2134_ = lean_nat_dec_lt(v___y_2130_, v___y_2133_);
if (v___x_2134_ == 0)
{
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v___x_2096_);
goto v___jp_2120_;
}
else
{
size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2135_ = lean_usize_of_nat(v___y_2130_);
lean_dec(v___y_2130_);
v___x_2136_ = lean_usize_of_nat(v___y_2133_);
lean_dec(v___y_2133_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___y_2129_, v___y_2131_, v___y_2132_, v___x_2135_, v___x_2136_);
v___x_2138_ = lean_unbox(v___x_2137_);
lean_dec(v___x_2137_);
if (v___x_2138_ == 0)
{
lean_dec_ref(v___x_2096_);
goto v___jp_2120_;
}
else
{
lean_dec(v___x_2106_);
lean_dec(v___x_2093_);
goto v___jp_2117_;
}
}
}
v___jp_2142_:
{
if (v___y_2143_ == 0)
{
lean_dec_ref(v___f_2141_);
lean_dec(v___x_2106_);
lean_dec(v_next_2099_);
lean_dec(v___x_2093_);
lean_dec_ref(v_resOrders_2091_);
lean_dec(v___x_2088_);
goto v___jp_2117_;
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_array_2147_; lean_object* v_start_2148_; lean_object* v_stop_2149_; uint8_t v___x_2150_; 
v___x_2144_ = lean_unsigned_to_nat(1u);
v___x_2145_ = lean_nat_add(v_next_2099_, v___x_2144_);
lean_dec(v_next_2099_);
v___x_2146_ = l_Array_toSubarray___redArg(v_resOrders_2091_, v___x_2145_, v___x_2088_);
v_array_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc_ref(v_array_2147_);
v_start_2148_ = lean_ctor_get(v___x_2146_, 1);
lean_inc(v_start_2148_);
v_stop_2149_ = lean_ctor_get(v___x_2146_, 2);
lean_inc(v_stop_2149_);
lean_dec_ref(v___x_2146_);
v___x_2150_ = lean_nat_dec_lt(v_start_2148_, v_stop_2149_);
if (v___x_2150_ == 0)
{
lean_dec(v_stop_2149_);
lean_dec(v_start_2148_);
lean_dec_ref(v_array_2147_);
lean_dec_ref(v___f_2141_);
lean_dec_ref(v___x_2096_);
goto v___jp_2120_;
}
else
{
lean_object* v___x_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2151_ = lean_box(v___y_2143_);
v___f_2152_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__6___boxed), 3, 2);
lean_closure_set(v___f_2152_, 0, v___f_2141_);
lean_closure_set(v___f_2152_, 1, v___x_2151_);
v___x_2153_ = lean_array_get_size(v_array_2147_);
v___x_2154_ = lean_nat_dec_le(v_stop_2149_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_dec(v_stop_2149_);
v___y_2129_ = v___x_2108_;
v___y_2130_ = v_start_2148_;
v___y_2131_ = v___f_2152_;
v___y_2132_ = v_array_2147_;
v___y_2133_ = v___x_2153_;
goto v___jp_2128_;
}
else
{
v___y_2129_ = v___x_2108_;
v___y_2130_ = v_start_2148_;
v___y_2131_ = v___f_2152_;
v___y_2132_ = v_array_2147_;
v___y_2133_ = v_stop_2149_;
goto v___jp_2128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed(lean_object* v___x_2167_, lean_object* v_toPure_2168_, lean_object* v___x_2169_, lean_object* v_resOrders_2170_, lean_object* v___x_2171_, lean_object* v___x_2172_, lean_object* v_toBind_2173_, lean_object* v___f_2174_, lean_object* v___x_2175_, lean_object* v_next_2176_, lean_object* v___x_2177_, lean_object* v_next_2178_, lean_object* v_acc_2179_, lean_object* v_h_2180_, lean_object* v_G_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8(v___x_2167_, v_toPure_2168_, v___x_2169_, v_resOrders_2170_, v___x_2171_, v___x_2172_, v_toBind_2173_, v___f_2174_, v___x_2175_, v_next_2176_, v___x_2177_, v_next_2178_, v_acc_2179_, v_h_2180_, v_G_2181_);
lean_dec(v_next_2176_);
lean_dec(v___x_2171_);
lean_dec_ref(v___x_2169_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(lean_object* v___x_2183_, lean_object* v_toPure_2184_, lean_object* v___x_2185_, lean_object* v_resOrders_2186_, lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v_toBind_2189_, lean_object* v___f_2190_, lean_object* v___x_2191_, lean_object* v___x_2192_, lean_object* v___f_2193_, lean_object* v___f_2194_, lean_object* v_next_2195_, lean_object* v_acc_2196_, lean_object* v_h_2197_, lean_object* v_G_2198_){
_start:
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_nat_dec_lt(v_next_2195_, v___x_2183_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; 
lean_dec(v_G_2198_);
lean_dec(v_next_2195_);
lean_dec(v___f_2194_);
lean_dec(v___f_2193_);
lean_dec_ref(v___x_2191_);
lean_dec(v___f_2190_);
lean_dec(v_toBind_2189_);
lean_dec(v___x_2188_);
lean_dec(v___x_2187_);
lean_dec_ref(v_resOrders_2186_);
lean_dec_ref(v___x_2185_);
v___x_2200_ = lean_apply_2(v_toPure_2184_, lean_box(0), v_acc_2196_);
return v___x_2200_;
}
else
{
lean_object* v___f_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec_ref(v_acc_2196_);
lean_inc(v_next_2195_);
lean_inc(v_toPure_2184_);
v___f_2201_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2201_, 0, v_toPure_2184_);
lean_closure_set(v___f_2201_, 1, v_next_2195_);
lean_closure_set(v___f_2201_, 2, v_G_2198_);
v___x_2202_ = lean_nat_sub(v___x_2183_, v_next_2195_);
lean_inc_ref(v___x_2191_);
lean_inc(v_toBind_2189_);
lean_inc(v___x_2188_);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__8___boxed), 15, 11);
lean_closure_set(v___f_2203_, 0, v___x_2202_);
lean_closure_set(v___f_2203_, 1, v_toPure_2184_);
lean_closure_set(v___f_2203_, 2, v___x_2185_);
lean_closure_set(v___f_2203_, 3, v_resOrders_2186_);
lean_closure_set(v___f_2203_, 4, v___x_2187_);
lean_closure_set(v___f_2203_, 5, v___x_2188_);
lean_closure_set(v___f_2203_, 6, v_toBind_2189_);
lean_closure_set(v___f_2203_, 7, v___f_2190_);
lean_closure_set(v___f_2203_, 8, v___x_2191_);
lean_closure_set(v___f_2203_, 9, v_next_2195_);
lean_closure_set(v___f_2203_, 10, v___x_2192_);
v___x_2204_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2203_, v___x_2188_, v___x_2191_, lean_box(0));
lean_inc(v_toBind_2189_);
v___x_2205_ = lean_apply_4(v_toBind_2189_, lean_box(0), lean_box(0), v___x_2204_, v___f_2193_);
lean_inc(v_toBind_2189_);
v___x_2206_ = lean_apply_4(v_toBind_2189_, lean_box(0), lean_box(0), v___x_2205_, v___f_2194_);
v___x_2207_ = lean_apply_4(v_toBind_2189_, lean_box(0), lean_box(0), v___x_2206_, v___f_2201_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed(lean_object* v___x_2208_, lean_object* v_toPure_2209_, lean_object* v___x_2210_, lean_object* v_resOrders_2211_, lean_object* v___x_2212_, lean_object* v___x_2213_, lean_object* v_toBind_2214_, lean_object* v___f_2215_, lean_object* v___x_2216_, lean_object* v___x_2217_, lean_object* v___f_2218_, lean_object* v___f_2219_, lean_object* v_next_2220_, lean_object* v_acc_2221_, lean_object* v_h_2222_, lean_object* v_G_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9(v___x_2208_, v_toPure_2209_, v___x_2210_, v_resOrders_2211_, v___x_2212_, v___x_2213_, v_toBind_2214_, v___f_2215_, v___x_2216_, v___x_2217_, v___f_2218_, v___f_2219_, v_next_2220_, v_acc_2221_, v_h_2222_, v_G_2223_);
lean_dec(v___x_2208_);
return v_res_2224_;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0(void){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Array_instInhabited(lean_box(0));
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(lean_object* v_inst_2229_, lean_object* v_resOrders_2230_){
_start:
{
lean_object* v_toApplicative_2231_; lean_object* v_toBind_2232_; lean_object* v_toPure_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___f_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___f_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_toApplicative_2231_ = lean_ctor_get(v_inst_2229_, 0);
lean_inc_ref(v_toApplicative_2231_);
v_toBind_2232_ = lean_ctor_get(v_inst_2229_, 1);
lean_inc(v_toBind_2232_);
lean_dec_ref(v_inst_2229_);
v_toPure_2233_ = lean_ctor_get(v_toApplicative_2231_, 1);
lean_inc(v_toPure_2233_);
lean_dec_ref(v_toApplicative_2231_);
v___x_2234_ = lean_box(0);
v___x_2235_ = lean_obj_once(&l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0, &l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0_once, _init_l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__0);
v___x_2236_ = lean_array_get_size(v_resOrders_2230_);
lean_inc(v_toPure_2233_);
lean_inc_ref(v_resOrders_2230_);
v___f_2237_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2237_, 0, v___x_2235_);
lean_closure_set(v___f_2237_, 1, v_resOrders_2230_);
lean_closure_set(v___f_2237_, 2, v___x_2234_);
lean_closure_set(v___f_2237_, 3, v_toPure_2233_);
lean_inc(v_toPure_2233_);
v___f_2238_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2238_, 0, v_toPure_2233_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = lean_box(0);
v___x_2241_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___closed__1));
lean_inc(v_toPure_2233_);
v___f_2242_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__3), 4, 3);
lean_closure_set(v___f_2242_, 0, v___x_2241_);
lean_closure_set(v___f_2242_, 1, v_toPure_2233_);
lean_closure_set(v___f_2242_, 2, v___x_2240_);
lean_inc_ref(v___f_2238_);
lean_inc(v_toBind_2232_);
v___f_2243_ = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__9___boxed), 16, 12);
lean_closure_set(v___f_2243_, 0, v___x_2236_);
lean_closure_set(v___f_2243_, 1, v_toPure_2233_);
lean_closure_set(v___f_2243_, 2, v___x_2235_);
lean_closure_set(v___f_2243_, 3, v_resOrders_2230_);
lean_closure_set(v___f_2243_, 4, v___x_2234_);
lean_closure_set(v___f_2243_, 5, v___x_2239_);
lean_closure_set(v___f_2243_, 6, v_toBind_2232_);
lean_closure_set(v___f_2243_, 7, v___f_2238_);
lean_closure_set(v___f_2243_, 8, v___x_2241_);
lean_closure_set(v___f_2243_, 9, v___x_2240_);
lean_closure_set(v___f_2243_, 10, v___f_2242_);
lean_closure_set(v___f_2243_, 11, v___f_2238_);
v___x_2244_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2243_, v___x_2239_, v___x_2241_, lean_box(0));
v___x_2245_ = lean_apply_4(v_toBind_2232_, lean_box(0), lean_box(0), v___x_2244_, v___f_2237_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent(lean_object* v_m_2246_, lean_object* v_inst_2247_, lean_object* v_resOrders_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2247_, v_resOrders_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2250_){
_start:
{
lean_object* v_structName_2251_; 
v_structName_2251_ = lean_ctor_get(v_x_2250_, 0);
lean_inc(v_structName_2251_);
return v_structName_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_computeStructureResolutionOrder___redArg___lam__0(v_x_2252_);
lean_dec_ref(v_x_2252_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__1(lean_object* v_toPure_2254_, lean_object* v_result_2255_, lean_object* v_____r_2256_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_apply_2(v_toPure_2254_, lean_box(0), v_result_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__2(lean_object* v_toPure_2258_, lean_object* v_inst_2259_, lean_object* v_structName_2260_, lean_object* v_toBind_2261_, lean_object* v_result_2262_){
_start:
{
lean_object* v_resolutionOrder_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_resolutionOrder_2263_ = lean_ctor_get(v_result_2262_, 0);
lean_inc_ref(v_resolutionOrder_2263_);
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2264_, 0, v_toPure_2258_);
lean_closure_set(v___f_2264_, 1, v_result_2262_);
v___x_2265_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___redArg(v_inst_2259_, v_structName_2260_, v_resolutionOrder_2263_);
v___x_2266_ = lean_apply_4(v_toBind_2261_, lean_box(0), lean_box(0), v___x_2265_, v___f_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5(lean_object* v___x_2267_, lean_object* v_x_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_array_get_borrowed(v___x_2269_, v_x_2268_, v___x_2267_);
lean_inc(v___x_2270_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__5___boxed(lean_object* v___x_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__5(v___x_2271_, v_x_2272_);
lean_dec_ref(v_x_2272_);
lean_dec(v___x_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6(lean_object* v_snd_2274_, lean_object* v_x1_2275_, lean_object* v_x2_2276_){
_start:
{
uint8_t v___x_2277_; 
v___x_2277_ = lean_name_eq(v_x2_2276_, v_snd_2274_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_array_push(v_x1_2275_, v_x2_2276_);
return v___x_2278_;
}
else
{
lean_dec(v_x2_2276_);
return v_x1_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed(lean_object* v_snd_2279_, lean_object* v_x1_2280_, lean_object* v_x2_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__6(v_snd_2279_, v_x1_2280_, v_x2_2281_);
lean_dec(v_snd_2279_);
return v_res_2282_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__9(lean_object* v_snd_2283_, lean_object* v_x_2284_){
_start:
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_name_eq(v_x_2284_, v_snd_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed(lean_object* v_snd_2286_, lean_object* v_x_2287_){
_start:
{
uint8_t v_res_2288_; lean_object* v_r_2289_; 
v_res_2288_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__9(v_snd_2286_, v_x_2287_);
lean_dec(v_x_2287_);
lean_dec(v_snd_2286_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__8(lean_object* v___x_2290_, lean_object* v_parentNames_2291_, lean_object* v_x_2292_){
_start:
{
uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_inc(v_x_2292_);
v___x_2293_ = l_Array_contains___redArg(v___x_2290_, v_parentNames_2291_, v_x_2292_);
v___x_2294_ = lean_box(v___x_2293_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v_x_2292_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7(lean_object* v___x_2296_, lean_object* v___f_2297_, lean_object* v_x_2298_){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2299_ = lean_array_get_size(v_x_2298_);
v___x_2300_ = lean_mk_empty_array_with_capacity(v___x_2296_);
v___x_2301_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2302_ = lean_nat_dec_lt(v___x_2296_, v___x_2299_);
if (v___x_2302_ == 0)
{
lean_dec_ref(v_x_2298_);
lean_dec_ref(v___f_2297_);
return v___x_2300_;
}
else
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_nat_dec_le(v___x_2299_, v___x_2299_);
if (v___x_2303_ == 0)
{
if (v___x_2302_ == 0)
{
lean_dec_ref(v_x_2298_);
lean_dec_ref(v___f_2297_);
return v___x_2300_;
}
else
{
size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = ((size_t)0ULL);
v___x_2305_ = lean_usize_of_nat(v___x_2299_);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2301_, v___f_2297_, v_x_2298_, v___x_2304_, v___x_2305_, v___x_2300_);
return v___x_2306_;
}
}
else
{
size_t v___x_2307_; size_t v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = ((size_t)0ULL);
v___x_2308_ = lean_usize_of_nat(v___x_2299_);
v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2301_, v___f_2297_, v_x_2298_, v___x_2307_, v___x_2308_, v___x_2300_);
return v___x_2309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed(lean_object* v___x_2310_, lean_object* v___f_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__7(v___x_2310_, v___f_2311_, v_x_2312_);
lean_dec(v___x_2310_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__10(lean_object* v___f_2314_, lean_object* v_x1_2315_, lean_object* v_x2_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_array_2321_; lean_object* v_start_2322_; lean_object* v_stop_2323_; lean_object* v___y_2325_; uint8_t v___x_2332_; 
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_array_get_size(v_x2_2316_);
lean_inc_ref(v_x2_2316_);
v___x_2319_ = l_Array_toSubarray___redArg(v_x2_2316_, v___x_2317_, v___x_2318_);
v___x_2320_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_array_2321_ = lean_ctor_get(v___x_2319_, 0);
lean_inc_ref(v_array_2321_);
v_start_2322_ = lean_ctor_get(v___x_2319_, 1);
lean_inc(v_start_2322_);
v_stop_2323_ = lean_ctor_get(v___x_2319_, 2);
lean_inc(v_stop_2323_);
lean_dec_ref(v___x_2319_);
v___x_2332_ = lean_nat_dec_lt(v_start_2322_, v_stop_2323_);
if (v___x_2332_ == 0)
{
lean_dec(v_stop_2323_);
lean_dec(v_start_2322_);
lean_dec_ref(v_array_2321_);
lean_dec_ref(v_x2_2316_);
lean_dec_ref(v___f_2314_);
return v_x1_2315_;
}
else
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = lean_array_get_size(v_array_2321_);
v___x_2334_ = lean_nat_dec_le(v_stop_2323_, v___x_2333_);
if (v___x_2334_ == 0)
{
lean_dec(v_stop_2323_);
v___y_2325_ = v___x_2333_;
goto v___jp_2324_;
}
else
{
v___y_2325_ = v_stop_2323_;
goto v___jp_2324_;
}
}
v___jp_2324_:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_nat_dec_lt(v_start_2322_, v___y_2325_);
if (v___x_2326_ == 0)
{
lean_dec(v___y_2325_);
lean_dec(v_start_2322_);
lean_dec_ref(v_array_2321_);
lean_dec_ref(v_x2_2316_);
lean_dec_ref(v___f_2314_);
return v_x1_2315_;
}
else
{
size_t v___x_2327_; size_t v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2327_ = lean_usize_of_nat(v_start_2322_);
lean_dec(v_start_2322_);
v___x_2328_ = lean_usize_of_nat(v___y_2325_);
lean_dec(v___y_2325_);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2320_, v___f_2314_, v_array_2321_, v___x_2327_, v___x_2328_);
v___x_2330_ = lean_unbox(v___x_2329_);
lean_dec(v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec_ref(v_x2_2316_);
return v_x1_2315_;
}
else
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_array_push(v_x1_2315_, v_x2_2316_);
return v___x_2331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11(lean_object* v_toPure_2336_, lean_object* v___x_2337_, lean_object* v_fst_2338_, lean_object* v_fst_2339_, lean_object* v___f_2340_, uint8_t v_relaxed_2341_, lean_object* v_parentNames_2342_, lean_object* v_snd_2343_, lean_object* v___f_2344_, lean_object* v_____x_2345_){
_start:
{
lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v_fst_2354_; lean_object* v_snd_2355_; lean_object* v___f_2356_; lean_object* v___f_2357_; lean_object* v_defects_2359_; uint8_t v___x_2373_; 
v_fst_2354_ = lean_ctor_get(v_____x_2345_, 0);
lean_inc(v_fst_2354_);
v_snd_2355_ = lean_ctor_get(v_____x_2345_, 1);
lean_inc(v_snd_2355_);
lean_dec_ref(v_____x_2345_);
lean_inc(v_snd_2355_);
v___f_2356_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_2356_, 0, v_snd_2355_);
lean_inc(v___x_2337_);
v___f_2357_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_2357_, 0, v___x_2337_);
lean_closure_set(v___f_2357_, 1, v___f_2356_);
v___x_2373_ = lean_unbox(v_fst_2354_);
lean_dec(v_fst_2354_);
if (v___x_2373_ == 0)
{
if (v_relaxed_2341_ == 0)
{
lean_object* v___x_2374_; lean_object* v___f_2375_; lean_object* v___y_2377_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2401_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2374_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc_ref(v_parentNames_2342_);
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__8), 3, 2);
lean_closure_set(v___f_2375_, 0, v___x_2374_);
lean_closure_set(v___f_2375_, 1, v_parentNames_2342_);
v___x_2412_ = lean_array_get_size(v_fst_2339_);
v___x_2413_ = lean_mk_empty_array_with_capacity(v___x_2337_);
v___x_2414_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2415_ = lean_nat_dec_lt(v___x_2337_, v___x_2412_);
if (v___x_2415_ == 0)
{
v___y_2401_ = v___x_2413_;
goto v___jp_2400_;
}
else
{
lean_object* v___f_2416_; lean_object* v___f_2417_; uint8_t v___x_2418_; 
lean_inc(v_snd_2355_);
v___f_2416_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__9___boxed), 2, 1);
lean_closure_set(v___f_2416_, 0, v_snd_2355_);
v___f_2417_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__10), 3, 1);
lean_closure_set(v___f_2417_, 0, v___f_2416_);
v___x_2418_ = lean_nat_dec_le(v___x_2412_, v___x_2412_);
if (v___x_2418_ == 0)
{
if (v___x_2415_ == 0)
{
lean_dec_ref(v___f_2417_);
v___y_2401_ = v___x_2413_;
goto v___jp_2400_;
}
else
{
size_t v___x_2419_; size_t v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = lean_usize_of_nat(v___x_2412_);
lean_inc(v_fst_2339_);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2414_, v___f_2417_, v_fst_2339_, v___x_2419_, v___x_2420_, v___x_2413_);
v___y_2401_ = v___x_2421_;
goto v___jp_2400_;
}
}
else
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = lean_usize_of_nat(v___x_2412_);
lean_inc(v_fst_2339_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2414_, v___f_2417_, v_fst_2339_, v___x_2422_, v___x_2423_, v___x_2413_);
v___y_2401_ = v___x_2424_;
goto v___jp_2400_;
}
}
v___jp_2376_:
{
lean_object* v_conflicts_2378_; uint8_t v___x_2379_; lean_object* v___x_2380_; size_t v_sz_2381_; size_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_defects_2385_; 
v_conflicts_2378_ = l_Array_eraseReps___redArg(v___x_2374_, v___y_2377_);
lean_inc(v_snd_2355_);
v___x_2379_ = l_Array_contains___redArg(v___x_2374_, v_parentNames_2342_, v_snd_2355_);
v___x_2380_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2381_ = lean_array_size(v_conflicts_2378_);
v___x_2382_ = ((size_t)0ULL);
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2380_, v___f_2375_, v_sz_2381_, v___x_2382_, v_conflicts_2378_);
lean_inc(v_snd_2355_);
v___x_2384_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2384_, 0, v_snd_2355_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*2, v___x_2379_);
v_defects_2385_ = lean_array_push(v_snd_2343_, v___x_2384_);
v_defects_2359_ = v_defects_2385_;
goto v___jp_2358_;
}
v___jp_2386_:
{
lean_object* v___x_2392_; 
lean_inc_ref(v___y_2389_);
v___x_2392_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___y_2389_, v___y_2390_, v___y_2388_, v___y_2387_, v___y_2391_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_2391_);
lean_dec(v___y_2390_);
v___y_2377_ = v___x_2392_;
goto v___jp_2376_;
}
v___jp_2393_:
{
uint8_t v___x_2399_; 
v___x_2399_ = lean_nat_dec_le(v___y_2398_, v___y_2394_);
if (v___x_2399_ == 0)
{
lean_dec(v___y_2394_);
lean_inc(v___y_2398_);
v___y_2387_ = v___y_2398_;
v___y_2388_ = v___y_2395_;
v___y_2389_ = v___y_2396_;
v___y_2390_ = v___y_2397_;
v___y_2391_ = v___y_2398_;
goto v___jp_2386_;
}
else
{
v___y_2387_ = v___y_2398_;
v___y_2388_ = v___y_2395_;
v___y_2389_ = v___y_2396_;
v___y_2390_ = v___y_2397_;
v___y_2391_ = v___y_2394_;
goto v___jp_2386_;
}
}
v___jp_2400_:
{
lean_object* v___x_2402_; size_t v_sz_2403_; size_t v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2402_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2403_ = lean_array_size(v___y_2401_);
v___x_2404_ = ((size_t)0ULL);
v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2402_, v___f_2344_, v_sz_2403_, v___x_2404_, v___y_2401_);
v___x_2406_ = lean_array_get_size(v___x_2405_);
v___x_2407_ = lean_nat_dec_eq(v___x_2406_, v___x_2337_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2408_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___closed__0));
v___x_2409_ = lean_unsigned_to_nat(1u);
v___x_2410_ = lean_nat_sub(v___x_2406_, v___x_2409_);
v___x_2411_ = lean_nat_dec_le(v___x_2337_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_inc(v___x_2410_);
v___y_2394_ = v___x_2410_;
v___y_2395_ = v___x_2405_;
v___y_2396_ = v___x_2408_;
v___y_2397_ = v___x_2406_;
v___y_2398_ = v___x_2410_;
goto v___jp_2393_;
}
else
{
lean_inc(v___x_2337_);
v___y_2394_ = v___x_2410_;
v___y_2395_ = v___x_2405_;
v___y_2396_ = v___x_2408_;
v___y_2397_ = v___x_2406_;
v___y_2398_ = v___x_2337_;
goto v___jp_2393_;
}
}
else
{
v___y_2377_ = v___x_2405_;
goto v___jp_2376_;
}
}
}
else
{
lean_dec_ref(v___f_2344_);
lean_dec_ref(v_parentNames_2342_);
v_defects_2359_ = v_snd_2343_;
goto v___jp_2358_;
}
}
else
{
lean_dec_ref(v___f_2344_);
lean_dec_ref(v_parentNames_2342_);
v_defects_2359_ = v_snd_2343_;
goto v___jp_2358_;
}
v___jp_2346_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___y_2347_);
lean_ctor_set(v___x_2350_, 1, v___y_2348_);
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___y_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
v___x_2353_ = lean_apply_2(v_toPure_2336_, lean_box(0), v___x_2352_);
return v___x_2353_;
}
v___jp_2358_:
{
lean_object* v_resOrder_2360_; lean_object* v___x_2361_; size_t v_sz_2362_; size_t v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v_resOrder_2360_ = lean_array_push(v_fst_2338_, v_snd_2355_);
v___x_2361_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2362_ = lean_array_size(v_fst_2339_);
v___x_2363_ = ((size_t)0ULL);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2361_, v___f_2357_, v_sz_2362_, v___x_2363_, v_fst_2339_);
v___x_2365_ = lean_array_get_size(v___x_2364_);
v___x_2366_ = lean_mk_empty_array_with_capacity(v___x_2337_);
v___x_2367_ = lean_nat_dec_lt(v___x_2337_, v___x_2365_);
lean_dec(v___x_2337_);
if (v___x_2367_ == 0)
{
lean_dec(v___x_2364_);
lean_dec_ref(v___f_2340_);
v___y_2347_ = v_resOrder_2360_;
v___y_2348_ = v_defects_2359_;
v___y_2349_ = v___x_2366_;
goto v___jp_2346_;
}
else
{
uint8_t v___x_2368_; 
v___x_2368_ = lean_nat_dec_le(v___x_2365_, v___x_2365_);
if (v___x_2368_ == 0)
{
if (v___x_2367_ == 0)
{
lean_dec(v___x_2364_);
lean_dec_ref(v___f_2340_);
v___y_2347_ = v_resOrder_2360_;
v___y_2348_ = v_defects_2359_;
v___y_2349_ = v___x_2366_;
goto v___jp_2346_;
}
else
{
size_t v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_usize_of_nat(v___x_2365_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2361_, v___f_2340_, v___x_2364_, v___x_2363_, v___x_2369_, v___x_2366_);
v___y_2347_ = v_resOrder_2360_;
v___y_2348_ = v_defects_2359_;
v___y_2349_ = v___x_2370_;
goto v___jp_2346_;
}
}
else
{
size_t v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_usize_of_nat(v___x_2365_);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2361_, v___f_2340_, v___x_2364_, v___x_2363_, v___x_2371_, v___x_2366_);
v___y_2347_ = v_resOrder_2360_;
v___y_2348_ = v_defects_2359_;
v___y_2349_ = v___x_2372_;
goto v___jp_2346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed(lean_object* v_toPure_2425_, lean_object* v___x_2426_, lean_object* v_fst_2427_, lean_object* v_fst_2428_, lean_object* v___f_2429_, lean_object* v_relaxed_2430_, lean_object* v_parentNames_2431_, lean_object* v_snd_2432_, lean_object* v___f_2433_, lean_object* v_____x_2434_){
_start:
{
uint8_t v_relaxed_boxed_2435_; lean_object* v_res_2436_; 
v_relaxed_boxed_2435_ = lean_unbox(v_relaxed_2430_);
v_res_2436_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__11(v_toPure_2425_, v___x_2426_, v_fst_2427_, v_fst_2428_, v___f_2429_, v_relaxed_boxed_2435_, v_parentNames_2431_, v_snd_2432_, v___f_2433_, v_____x_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12(lean_object* v___x_2437_, lean_object* v_toPure_2438_, lean_object* v___f_2439_, uint8_t v_relaxed_2440_, lean_object* v_parentNames_2441_, lean_object* v___f_2442_, lean_object* v_inst_2443_, lean_object* v_toBind_2444_, lean_object* v_x_2445_, lean_object* v_____s_2446_){
_start:
{
lean_object* v_snd_2447_; lean_object* v_fst_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2472_; 
v_snd_2447_ = lean_ctor_get(v_____s_2446_, 1);
v_fst_2448_ = lean_ctor_get(v_____s_2446_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_____s_2446_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2450_ = v_____s_2446_;
v_isShared_2451_ = v_isSharedCheck_2472_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_snd_2447_);
lean_inc(v_fst_2448_);
lean_dec(v_____s_2446_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2472_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2471_; 
v_fst_2452_ = lean_ctor_get(v_snd_2447_, 0);
v_snd_2453_ = lean_ctor_get(v_snd_2447_, 1);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_snd_2447_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2455_ = v_snd_2447_;
v_isShared_2456_ = v_isSharedCheck_2471_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_snd_2453_);
lean_inc(v_fst_2452_);
lean_dec(v_snd_2447_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2471_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = lean_array_get_size(v_fst_2448_);
v___x_2458_ = lean_nat_dec_eq(v___x_2457_, v___x_2437_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_del_object(v___x_2455_);
lean_del_object(v___x_2450_);
v___x_2459_ = lean_box(v_relaxed_2440_);
lean_inc(v_fst_2448_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__11___boxed), 10, 9);
lean_closure_set(v___f_2460_, 0, v_toPure_2438_);
lean_closure_set(v___f_2460_, 1, v___x_2437_);
lean_closure_set(v___f_2460_, 2, v_fst_2452_);
lean_closure_set(v___f_2460_, 3, v_fst_2448_);
lean_closure_set(v___f_2460_, 4, v___f_2439_);
lean_closure_set(v___f_2460_, 5, v___x_2459_);
lean_closure_set(v___f_2460_, 6, v_parentNames_2441_);
lean_closure_set(v___f_2460_, 7, v_snd_2453_);
lean_closure_set(v___f_2460_, 8, v___f_2442_);
v___x_2461_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg(v_inst_2443_, v_fst_2448_);
v___x_2462_ = lean_apply_4(v_toBind_2444_, lean_box(0), lean_box(0), v___x_2461_, v___f_2460_);
return v___x_2462_;
}
else
{
lean_object* v___x_2464_; 
lean_dec(v_toBind_2444_);
lean_dec_ref(v_inst_2443_);
lean_dec_ref(v___f_2442_);
lean_dec_ref(v_parentNames_2441_);
lean_dec_ref(v___f_2439_);
lean_dec(v___x_2437_);
if (v_isShared_2456_ == 0)
{
v___x_2464_ = v___x_2455_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_fst_2452_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_snd_2453_);
v___x_2464_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2466_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2464_);
v___x_2466_ = v___x_2450_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_fst_2448_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
v___x_2468_ = lean_apply_2(v_toPure_2438_, lean_box(0), v___x_2467_);
return v___x_2468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed(lean_object* v___x_2473_, lean_object* v_toPure_2474_, lean_object* v___f_2475_, lean_object* v_relaxed_2476_, lean_object* v_parentNames_2477_, lean_object* v___f_2478_, lean_object* v_inst_2479_, lean_object* v_toBind_2480_, lean_object* v_x_2481_, lean_object* v_____s_2482_){
_start:
{
uint8_t v_relaxed_boxed_2483_; lean_object* v_res_2484_; 
v_relaxed_boxed_2483_ = lean_unbox(v_relaxed_2476_);
v_res_2484_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__12(v___x_2473_, v_toPure_2474_, v___f_2475_, v_relaxed_boxed_2483_, v_parentNames_2477_, v___f_2478_, v_inst_2479_, v_toBind_2480_, v_x_2481_, v_____s_2482_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13(lean_object* v_toPure_2491_, lean_object* v___f_2492_, uint8_t v_relaxed_2493_, lean_object* v_parentNames_2494_, lean_object* v_inst_2495_, lean_object* v_toBind_2496_, lean_object* v_structName_2497_, lean_object* v___f_2498_, lean_object* v___f_2499_, lean_object* v_parentResOrders_2500_){
_start:
{
lean_object* v___x_2501_; lean_object* v___f_2502_; lean_object* v___x_2503_; lean_object* v___f_2504_; lean_object* v___y_2506_; lean_object* v_j_2515_; lean_object* v_as_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2501_ = lean_unsigned_to_nat(0u);
v___f_2502_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__0));
v___x_2503_ = lean_box(v_relaxed_2493_);
lean_inc(v_toBind_2496_);
lean_inc_ref(v_inst_2495_);
lean_inc_ref(v_parentNames_2494_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__12___boxed), 10, 8);
lean_closure_set(v___f_2504_, 0, v___x_2501_);
lean_closure_set(v___f_2504_, 1, v_toPure_2491_);
lean_closure_set(v___f_2504_, 2, v___f_2492_);
lean_closure_set(v___f_2504_, 3, v___x_2503_);
lean_closure_set(v___f_2504_, 4, v_parentNames_2494_);
lean_closure_set(v___f_2504_, 5, v___f_2502_);
lean_closure_set(v___f_2504_, 6, v_inst_2495_);
lean_closure_set(v___f_2504_, 7, v_toBind_2496_);
v_j_2515_ = lean_array_get_size(v_parentResOrders_2500_);
v_as_2516_ = lean_array_push(v_parentResOrders_2500_, v_parentNames_2494_);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2501_, v_as_2516_, v_j_2515_);
v___x_2518_ = lean_array_get_size(v___x_2517_);
v___x_2519_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__2));
v___x_2520_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v___x_2521_ = lean_nat_dec_lt(v___x_2501_, v___x_2518_);
if (v___x_2521_ == 0)
{
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___f_2499_);
v___y_2506_ = v___x_2519_;
goto v___jp_2505_;
}
else
{
uint8_t v___x_2522_; 
v___x_2522_ = lean_nat_dec_le(v___x_2518_, v___x_2518_);
if (v___x_2522_ == 0)
{
if (v___x_2521_ == 0)
{
lean_dec_ref(v___x_2517_);
lean_dec_ref(v___f_2499_);
v___y_2506_ = v___x_2519_;
goto v___jp_2505_;
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2518_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2520_, v___f_2499_, v___x_2517_, v___x_2523_, v___x_2524_, v___x_2519_);
v___y_2506_ = v___x_2525_;
goto v___jp_2505_;
}
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = lean_usize_of_nat(v___x_2518_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2520_, v___f_2499_, v___x_2517_, v___x_2526_, v___x_2527_, v___x_2519_);
v___y_2506_ = v___x_2528_;
goto v___jp_2505_;
}
}
v___jp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_resOrder_2509_; lean_object* v_defects_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_mk_empty_array_with_capacity(v___x_2507_);
v_resOrder_2509_ = lean_array_push(v___x_2508_, v_structName_2497_);
v_defects_2510_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1));
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_resOrder_2509_);
lean_ctor_set(v___x_2511_, 1, v_defects_2510_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___y_2506_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = l___private_Init_While_0__Lean_Loop_forIn_loop(lean_box(0), lean_box(0), v_inst_2495_, v___f_2504_, v___x_2512_);
v___x_2514_ = lean_apply_4(v_toBind_2496_, lean_box(0), lean_box(0), v___x_2513_, v___f_2498_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed(lean_object* v_toPure_2529_, lean_object* v___f_2530_, lean_object* v_relaxed_2531_, lean_object* v_parentNames_2532_, lean_object* v_inst_2533_, lean_object* v_toBind_2534_, lean_object* v_structName_2535_, lean_object* v___f_2536_, lean_object* v___f_2537_, lean_object* v_parentResOrders_2538_){
_start:
{
uint8_t v_relaxed_boxed_2539_; lean_object* v_res_2540_; 
v_relaxed_boxed_2539_ = lean_unbox(v_relaxed_2531_);
v_res_2540_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__13(v_toPure_2529_, v___f_2530_, v_relaxed_boxed_2539_, v_parentNames_2532_, v_inst_2533_, v_toBind_2534_, v_structName_2535_, v___f_2536_, v___f_2537_, v_parentResOrders_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT uint8_t l_Lean_mergeStructureResolutionOrders___redArg___lam__0(lean_object* v_x_2541_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2542_ = lean_array_get_size(v_x_2541_);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_nat_dec_eq(v___x_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
uint8_t v___x_2545_; 
v___x_2545_ = 1;
return v___x_2545_;
}
else
{
uint8_t v___x_2546_; 
v___x_2546_ = 0;
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__0___boxed(lean_object* v_x_2547_){
_start:
{
uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_res_2548_ = l_Lean_mergeStructureResolutionOrders___redArg___lam__0(v_x_2547_);
lean_dec_ref(v_x_2547_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__1(lean_object* v___f_2550_, lean_object* v_x1_2551_, lean_object* v_x2_2552_){
_start:
{
lean_object* v___x_2553_; uint8_t v___x_2554_; 
lean_inc_ref(v_x2_2552_);
v___x_2553_ = lean_apply_1(v___f_2550_, v_x2_2552_);
v___x_2554_ = lean_unbox(v___x_2553_);
if (v___x_2554_ == 0)
{
lean_dec_ref(v_x2_2552_);
return v_x1_2551_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_array_push(v_x1_2551_, v_x2_2552_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__4(lean_object* v_toPure_2556_, lean_object* v_____s_2557_){
_start:
{
lean_object* v_snd_2558_; lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2568_; 
v_snd_2558_ = lean_ctor_get(v_____s_2557_, 1);
lean_inc(v_snd_2558_);
lean_dec_ref(v_____s_2557_);
v_fst_2559_ = lean_ctor_get(v_snd_2558_, 0);
v_snd_2560_ = lean_ctor_get(v_snd_2558_, 1);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_snd_2558_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2562_ = v_snd_2558_;
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snd_2560_);
lean_inc(v_fst_2559_);
lean_dec(v_snd_2558_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_fst_2559_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_snd_2560_);
v___x_2565_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_apply_2(v_toPure_2556_, lean_box(0), v___x_2565_);
return v___x_2566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__3(lean_object* v_toPure_2569_, lean_object* v_____do__lift_2570_){
_start:
{
lean_object* v_resolutionOrder_2571_; lean_object* v___x_2572_; 
v_resolutionOrder_2571_ = lean_ctor_get(v_____do__lift_2570_, 0);
lean_inc_ref(v_resolutionOrder_2571_);
lean_dec_ref(v_____do__lift_2570_);
v___x_2572_ = lean_apply_2(v_toPure_2569_, lean_box(0), v_resolutionOrder_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg(lean_object* v_inst_2577_, lean_object* v_inst_2578_, lean_object* v_structName_2579_, lean_object* v_parentNames_2580_, uint8_t v_relaxed_2581_){
_start:
{
lean_object* v_toApplicative_2582_; lean_object* v_toBind_2583_; lean_object* v_toPure_2584_; lean_object* v___f_2585_; lean_object* v___f_2586_; lean_object* v___f_2587_; lean_object* v___f_2588_; lean_object* v___x_2589_; lean_object* v___f_2590_; size_t v_sz_2591_; size_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_toApplicative_2582_ = lean_ctor_get(v_inst_2577_, 0);
v_toBind_2583_ = lean_ctor_get(v_inst_2577_, 1);
lean_inc(v_toBind_2583_);
v_toPure_2584_ = lean_ctor_get(v_toApplicative_2582_, 1);
v___f_2585_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___closed__1));
lean_inc(v_toPure_2584_);
v___f_2586_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2586_, 0, v_toPure_2584_);
lean_inc(v_toBind_2583_);
lean_inc_ref(v_inst_2577_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2587_, 0, v_inst_2577_);
lean_closure_set(v___f_2587_, 1, v_inst_2578_);
lean_closure_set(v___f_2587_, 2, v_toBind_2583_);
lean_closure_set(v___f_2587_, 3, v___f_2586_);
lean_inc(v_toPure_2584_);
v___f_2588_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2588_, 0, v_toPure_2584_);
v___x_2589_ = lean_box(v_relaxed_2581_);
lean_inc(v_toBind_2583_);
lean_inc_ref(v_inst_2577_);
lean_inc_ref(v_parentNames_2580_);
lean_inc(v_toPure_2584_);
v___f_2590_ = lean_alloc_closure((void*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___boxed), 10, 9);
lean_closure_set(v___f_2590_, 0, v_toPure_2584_);
lean_closure_set(v___f_2590_, 1, v___f_2585_);
lean_closure_set(v___f_2590_, 2, v___x_2589_);
lean_closure_set(v___f_2590_, 3, v_parentNames_2580_);
lean_closure_set(v___f_2590_, 4, v_inst_2577_);
lean_closure_set(v___f_2590_, 5, v_toBind_2583_);
lean_closure_set(v___f_2590_, 6, v_structName_2579_);
lean_closure_set(v___f_2590_, 7, v___f_2588_);
lean_closure_set(v___f_2590_, 8, v___f_2585_);
v_sz_2591_ = lean_array_size(v_parentNames_2580_);
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2577_, v___f_2587_, v_sz_2591_, v___x_2592_, v_parentNames_2580_);
v___x_2594_ = lean_apply_4(v_toBind_2583_, lean_box(0), lean_box(0), v___x_2593_, v___f_2590_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3(lean_object* v_structName_2595_, lean_object* v_toPure_2596_, lean_object* v___f_2597_, lean_object* v_inst_2598_, lean_object* v_inst_2599_, uint8_t v_relaxed_2600_, lean_object* v_toBind_2601_, lean_object* v___f_2602_, lean_object* v_env_2603_){
_start:
{
lean_object* v___x_2604_; 
lean_inc_ref(v_env_2603_);
v___x_2604_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(v_env_2603_, v_structName_2595_);
if (lean_obj_tag(v___x_2604_) == 1)
{
lean_object* v_val_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec_ref(v_env_2603_);
lean_dec(v___f_2602_);
lean_dec(v_toBind_2601_);
lean_dec_ref(v_inst_2599_);
lean_dec_ref(v_inst_2598_);
lean_dec_ref(v___f_2597_);
lean_dec(v_structName_2595_);
v_val_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_val_2605_);
lean_dec_ref(v___x_2604_);
v___x_2606_ = ((lean_object*)(l_Lean_mergeStructureResolutionOrders___redArg___lam__13___closed__1));
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v_val_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_apply_2(v_toPure_2596_, lean_box(0), v___x_2607_);
return v___x_2608_;
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; size_t v_sz_2611_; size_t v___x_2612_; lean_object* v_parentNames_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec(v___x_2604_);
lean_dec(v_toPure_2596_);
lean_inc(v_structName_2595_);
v___x_2609_ = l_Lean_getStructureParentInfo(v_env_2603_, v_structName_2595_);
v___x_2610_ = ((lean_object*)(l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___redArg___lam__4___closed__9));
v_sz_2611_ = lean_array_size(v___x_2609_);
v___x_2612_ = ((size_t)0ULL);
v_parentNames_2613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2610_, v___f_2597_, v_sz_2611_, v___x_2612_, v___x_2609_);
v___x_2614_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2598_, v_inst_2599_, v_structName_2595_, v_parentNames_2613_, v_relaxed_2600_);
v___x_2615_ = lean_apply_4(v_toBind_2601_, lean_box(0), lean_box(0), v___x_2614_, v___f_2602_);
return v___x_2615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed(lean_object* v_structName_2616_, lean_object* v_toPure_2617_, lean_object* v___f_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_relaxed_2621_, lean_object* v_toBind_2622_, lean_object* v___f_2623_, lean_object* v_env_2624_){
_start:
{
uint8_t v_relaxed_boxed_2625_; lean_object* v_res_2626_; 
v_relaxed_boxed_2625_ = lean_unbox(v_relaxed_2621_);
v_res_2626_ = l_Lean_computeStructureResolutionOrder___redArg___lam__3(v_structName_2616_, v_toPure_2617_, v___f_2618_, v_inst_2619_, v_inst_2620_, v_relaxed_boxed_2625_, v_toBind_2622_, v___f_2623_, v_env_2624_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg(lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_structName_2629_, uint8_t v_relaxed_2630_){
_start:
{
lean_object* v_toApplicative_2631_; lean_object* v_toBind_2632_; lean_object* v_getEnv_2633_; lean_object* v_toPure_2634_; lean_object* v___f_2635_; lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; 
v_toApplicative_2631_ = lean_ctor_get(v_inst_2627_, 0);
v_toBind_2632_ = lean_ctor_get(v_inst_2627_, 1);
lean_inc(v_toBind_2632_);
v_getEnv_2633_ = lean_ctor_get(v_inst_2628_, 0);
lean_inc(v_getEnv_2633_);
v_toPure_2634_ = lean_ctor_get(v_toApplicative_2631_, 1);
lean_inc(v_toPure_2634_);
v___f_2635_ = ((lean_object*)(l_Lean_computeStructureResolutionOrder___redArg___closed__0));
lean_inc(v_toBind_2632_);
lean_inc(v_structName_2629_);
lean_inc_ref(v_inst_2628_);
lean_inc(v_toPure_2634_);
v___f_2636_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2636_, 0, v_toPure_2634_);
lean_closure_set(v___f_2636_, 1, v_inst_2628_);
lean_closure_set(v___f_2636_, 2, v_structName_2629_);
lean_closure_set(v___f_2636_, 3, v_toBind_2632_);
v___x_2637_ = lean_box(v_relaxed_2630_);
lean_inc(v_toBind_2632_);
v___f_2638_ = lean_alloc_closure((void*)(l_Lean_computeStructureResolutionOrder___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2638_, 0, v_structName_2629_);
lean_closure_set(v___f_2638_, 1, v_toPure_2634_);
lean_closure_set(v___f_2638_, 2, v___f_2635_);
lean_closure_set(v___f_2638_, 3, v_inst_2627_);
lean_closure_set(v___f_2638_, 4, v_inst_2628_);
lean_closure_set(v___f_2638_, 5, v___x_2637_);
lean_closure_set(v___f_2638_, 6, v_toBind_2632_);
lean_closure_set(v___f_2638_, 7, v___f_2636_);
v___x_2639_ = lean_apply_4(v_toBind_2632_, lean_box(0), lean_box(0), v_getEnv_2633_, v___f_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___lam__2(lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_toBind_2642_, lean_object* v___f_2643_, lean_object* v_parentName_2644_){
_start:
{
uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2645_ = 1;
v___x_2646_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2640_, v_inst_2641_, v_parentName_2644_, v___x_2645_);
v___x_2647_ = lean_apply_4(v_toBind_2642_, lean_box(0), lean_box(0), v___x_2646_, v___f_2643_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___redArg___boxed(lean_object* v_inst_2648_, lean_object* v_inst_2649_, lean_object* v_structName_2650_, lean_object* v_relaxed_2651_){
_start:
{
uint8_t v_relaxed_boxed_2652_; lean_object* v_res_2653_; 
v_relaxed_boxed_2652_ = lean_unbox(v_relaxed_2651_);
v_res_2653_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2648_, v_inst_2649_, v_structName_2650_, v_relaxed_boxed_2652_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___redArg___boxed(lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_structName_2656_, lean_object* v_parentNames_2657_, lean_object* v_relaxed_2658_){
_start:
{
uint8_t v_relaxed_boxed_2659_; lean_object* v_res_2660_; 
v_relaxed_boxed_2659_ = lean_unbox(v_relaxed_2658_);
v_res_2660_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2654_, v_inst_2655_, v_structName_2656_, v_parentNames_2657_, v_relaxed_boxed_2659_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder(lean_object* v_m_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_structName_2664_, uint8_t v_relaxed_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2662_, v_inst_2663_, v_structName_2664_, v_relaxed_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___boxed(lean_object* v_m_2667_, lean_object* v_inst_2668_, lean_object* v_inst_2669_, lean_object* v_structName_2670_, lean_object* v_relaxed_2671_){
_start:
{
uint8_t v_relaxed_boxed_2672_; lean_object* v_res_2673_; 
v_relaxed_boxed_2672_ = lean_unbox(v_relaxed_2671_);
v_res_2673_ = l_Lean_computeStructureResolutionOrder(v_m_2667_, v_inst_2668_, v_inst_2669_, v_structName_2670_, v_relaxed_boxed_2672_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders(lean_object* v_m_2674_, lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_structName_2677_, lean_object* v_parentNames_2678_, uint8_t v_relaxed_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_mergeStructureResolutionOrders___redArg(v_inst_2675_, v_inst_2676_, v_structName_2677_, v_parentNames_2678_, v_relaxed_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_mergeStructureResolutionOrders___boxed(lean_object* v_m_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_structName_2684_, lean_object* v_parentNames_2685_, lean_object* v_relaxed_2686_){
_start:
{
uint8_t v_relaxed_boxed_2687_; lean_object* v_res_2688_; 
v_relaxed_boxed_2687_ = lean_unbox(v_relaxed_2686_);
v_res_2688_ = l_Lean_mergeStructureResolutionOrders(v_m_2681_, v_inst_2682_, v_inst_2683_, v_structName_2684_, v_parentNames_2685_, v_relaxed_boxed_2687_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0(lean_object* v_x_2689_){
_start:
{
lean_object* v_resolutionOrder_2690_; 
v_resolutionOrder_2690_ = lean_ctor_get(v_x_2689_, 0);
lean_inc_ref(v_resolutionOrder_2690_);
return v_resolutionOrder_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg___lam__0___boxed(lean_object* v_x_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_getStructureResolutionOrder___redArg___lam__0(v_x_2691_);
lean_dec_ref(v_x_2691_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___redArg(lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_structName_2696_){
_start:
{
lean_object* v_toApplicative_2697_; lean_object* v_toFunctor_2698_; lean_object* v_map_2699_; lean_object* v___f_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_toApplicative_2697_ = lean_ctor_get(v_inst_2694_, 0);
v_toFunctor_2698_ = lean_ctor_get(v_toApplicative_2697_, 0);
v_map_2699_ = lean_ctor_get(v_toFunctor_2698_, 0);
lean_inc(v_map_2699_);
v___f_2700_ = ((lean_object*)(l_Lean_getStructureResolutionOrder___redArg___closed__0));
v___x_2701_ = 1;
v___x_2702_ = l_Lean_computeStructureResolutionOrder___redArg(v_inst_2694_, v_inst_2695_, v_structName_2696_, v___x_2701_);
v___x_2703_ = lean_apply_4(v_map_2699_, lean_box(0), lean_box(0), v___f_2700_, v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder(lean_object* v_m_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_structName_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2705_, v_inst_2706_, v_structName_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg___lam__0(lean_object* v___x_2709_, lean_object* v_structName_2710_, lean_object* v_x_2711_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Array_erase___redArg(v___x_2709_, v_x_2711_, v_structName_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___redArg(lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_structName_2715_){
_start:
{
lean_object* v_toApplicative_2716_; lean_object* v_toFunctor_2717_; lean_object* v_map_2718_; lean_object* v___x_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v_toApplicative_2716_ = lean_ctor_get(v_inst_2713_, 0);
v_toFunctor_2717_ = lean_ctor_get(v_toApplicative_2716_, 0);
v_map_2718_ = lean_ctor_get(v_toFunctor_2717_, 0);
lean_inc(v_map_2718_);
v___x_2719_ = ((lean_object*)(l_Lean_setStructureParents___redArg___closed__0));
lean_inc(v_structName_2715_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_getAllParentStructures___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2720_, 0, v___x_2719_);
lean_closure_set(v___f_2720_, 1, v_structName_2715_);
v___x_2721_ = l_Lean_getStructureResolutionOrder___redArg(v_inst_2713_, v_inst_2714_, v_structName_2715_);
v___x_2722_ = lean_apply_4(v_map_2718_, lean_box(0), lean_box(0), v___f_2720_, v___x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures(lean_object* v_m_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_structName_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_getAllParentStructures___redArg(v_inst_2724_, v_inst_2725_, v_structName_2726_);
return v___x_2727_;
}
}
lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Structure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedStructureInfo_default = _init_l_Lean_instInhabitedStructureInfo_default();
lean_mark_persistent(l_Lean_instInhabitedStructureInfo_default);
l_Lean_instInhabitedStructureInfo = _init_l_Lean_instInhabitedStructureInfo();
lean_mark_persistent(l_Lean_instInhabitedStructureInfo);
l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default = _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_instInhabitedStructureState_default);
l___private_Lean_Structure_0__Lean_instInhabitedStructureState = _init_l___private_Lean_Structure_0__Lean_instInhabitedStructureState();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_instInhabitedStructureState);
res = l___private_Lean_Structure_0__Lean_initFn_00___x40_Lean_Structure_2533181092____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Structure_0__Lean_structureExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Structure_0__Lean_structureExt);
lean_dec_ref(res);
l_Lean_instInhabitedStructureResolutionState_default = _init_l_Lean_instInhabitedStructureResolutionState_default();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionState_default);
l_Lean_instInhabitedStructureResolutionState = _init_l_Lean_instInhabitedStructureResolutionState();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionState);
res = l_Lean_initFn_00___x40_Lean_Structure_3808158513____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_structureResolutionExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_structureResolutionExt);
lean_dec_ref(res);
l_Lean_instInhabitedStructureResolutionOrderResult_default = _init_l_Lean_instInhabitedStructureResolutionOrderResult_default();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionOrderResult_default);
l_Lean_instInhabitedStructureResolutionOrderResult = _init_l_Lean_instInhabitedStructureResolutionOrderResult();
lean_mark_persistent(l_Lean_instInhabitedStructureResolutionOrderResult);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Structure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ProjFns(uint8_t builtin);
lean_object* initialize_Lean_Exception(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Structure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Structure(builtin);
}
#ifdef __cplusplus
}
#endif
